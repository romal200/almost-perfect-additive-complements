#!/usr/bin/env python3
"""Strict end-to-end verification and all-owned axiom audit for the Lean 4 formalization.

Performs four independent checks against the pinned toolchain in `lean/lean-toolchain`
and manifest in `lean/lake-manifest.json`:
  1. Source hygiene check across all project `.lean` files (rejects `sorry`, `admit`,
     custom `axiom` declarations, `implemented_by`, `unsafe`, and linter/warning overrides).
  2. Fresh per-module compilation in topological import order with
     `lake env lean -j1 -DwarningAsError=true` into a clean project `.olean` build tree.
  3. All-owned declaration transitive axiom audit (`Lean.collectAxioms`) covering every
     public and private declaration across all project modules, asserting zero project
     axioms, transitive axioms strictly in `{propext, Classical.choice, Quot.sound}`,
     and presence of all required endpoint theorems.
  4. Independent stock kernel replay of all freshly compiled project `.olean` modules
     using the pinned `leanchecker` executable.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ALLOWED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
VALID_KINDS = {
    "axiom",
    "definition",
    "theorem",
    "opaque",
    "quotient",
    "constructor",
    "recursor",
    "inductive",
}
MARKER = "ALL-OWNED-JSON "
MODULE_RE = re.compile(r"[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*")
PROJECT_ROOT = "AlmostPerfect"

REQUIRED_ENDPOINTS = (
    "AlmostPerfect.main_classification",
    "AlmostPerfect.conjecture_1_3",
    "AlmostPerfect.no_repeated_sums_below_eight_fifths",
    "AlmostPerfect.gabardo_lai_single_step",
    "AlmostPerfect.weak_limit_unique",
    "AlmostPerfect.exists_levelApprox",
    "AlmostPerfect.forward_doubling_step",
    "AlmostPerfect.polynomial_iteration_rigidity",
    "AlmostPerfect.zhang_gap_lemma",
    "AlmostPerfect.modularLift_limsup_eq_three_halves",
    "AlmostPerfect.modularLift_repCount_le_one",
    "AlmostPerfect.almostPerfect_limsup_le_two",
    "AlmostPerfect.truncPoly_exact_identity",
    "AlmostPerfect.exists_repCount_eq_one_eventually",
)

FORBIDDEN_CODE_PATTERNS = (
    (re.compile(r"\bsorry\b"), "sorry"),
    (re.compile(r"\badmit\b"), "admit"),
    (re.compile(r"(?m)^\s*(?:private\s+|protected\s+)?axiom\b"), "custom axiom declaration"),
    (re.compile(r"@\[[^\]]*\bimplemented_by\b"), "implemented_by attribute"),
    (re.compile(r"(?m)^\s*(?:private\s+|protected\s+)?unsafe\b"), "unsafe declaration"),
    (re.compile(r"\bwarningAsError\s+false\b"), "warningAsError override"),
    (re.compile(r"\blinter\.[A-Za-z0-9_.]+\s+false\b"), "linter suppression"),
)


def strip_lean_comments_and_strings(text: str) -> str:
    """Replace Lean comments (`-- ...`, `/- ... -/`) and string literals with spaces."""
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while depth and i < n:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    if text[i] == "\n":
                        out.append("\n")
                    i += 1
            if depth:
                raise ValueError("Unterminated block comment in Lean source")
            out.append(" ")
        elif text[i] == '"':
            i += 1
            out.append(" ")
            while i < n:
                if text[i] == "\\" and i + 1 < n:
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    if text[i] == "\n":
                        out.append("\n")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def header_tokens(text: str):
    """Lazily yield non-comment header tokens."""
    i = 0
    n = len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = n if end < 0 else end
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while depth and i < n:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("Unterminated block comment in Lean header")
        else:
            start = i
            while i < n and not text[i].isspace() and not text.startswith(("--", "/-"), i):
                i += 1
            yield text[start:i]


def imports_of(source: Path) -> list[str]:
    tokens = iter(header_tokens(source.read_text(encoding="utf-8")))
    token = next(tokens, None)
    if token == "module":
        token = next(tokens, None)
    if token == "prelude":
        token = next(tokens, None)
    imports: list[str] = []
    while token is not None:
        if token == "public":
            token = next(tokens, None)
        if token == "meta":
            token = next(tokens, None)
        if token != "import":
            break
        mod = next(tokens, None)
        if mod == "all":
            mod = next(tokens, None)
        if mod is None or not MODULE_RE.fullmatch(mod):
            raise ValueError(f"Unsupported import in {source}: {mod}")
        imports.append(mod)
        token = next(tokens, None)
    return imports


def is_project_module(module: str) -> bool:
    return module == PROJECT_ROOT or module.startswith(PROJECT_ROOT + ".")


def discover_project_modules(lean_dir: Path) -> list[str]:
    """Discover all `.lean` files under `AlmostPerfect` and return topological compile order."""
    disk_modules: set[str] = set()
    root_file = lean_dir / f"{PROJECT_ROOT}.lean"
    if not root_file.is_file():
        raise RuntimeError(f"Missing umbrella module: {root_file}")
    disk_modules.add(PROJECT_ROOT)
    for path in sorted((lean_dir / PROJECT_ROOT).rglob("*.lean")):
        rel = path.relative_to(lean_dir).with_suffix("")
        disk_modules.add(".".join(rel.parts))

    order: list[str] = []
    seen: set[str] = set()
    visiting: set[str] = set()

    def visit(mod: str) -> None:
        if mod in seen:
            return
        if mod in visiting:
            raise RuntimeError(f"Import cycle involving {mod}")
        visiting.add(mod)
        src = lean_dir / (mod.replace(".", "/") + ".lean")
        if not src.is_file():
            raise RuntimeError(f"Missing imported project module source: {src}")
        for dep in imports_of(src):
            if is_project_module(dep):
                visit(dep)
        visiting.remove(mod)
        seen.add(mod)
        order.append(mod)

    visit(PROJECT_ROOT)
    if seen != disk_modules:
        unreached = sorted(disk_modules - seen)
        raise RuntimeError(f"Project modules not imported by {PROJECT_ROOT}.lean: {unreached}")
    return order


def check_source_hygiene(lean_dir: Path, modules: list[str]) -> None:
    print(f"[1/4] Checking source hygiene across {len(modules)} Lean modules...", flush=True)
    for mod in modules:
        src = lean_dir / (mod.replace(".", "/") + ".lean")
        cleaned = strip_lean_comments_and_strings(src.read_text(encoding="utf-8"))
        for pattern, label in FORBIDDEN_CODE_PATTERNS:
            match = pattern.search(cleaned)
            if match is not None:
                line_no = cleaned[: match.start()].count("\n") + 1
                raise RuntimeError(f"Forbidden {label} in {src.relative_to(lean_dir)}:{line_no}")
    print(f"      PASS: zero sorry/admit/custom axiom/unsafe/linter-suppression tokens.", flush=True)


def run_cmd(cmd: list[str], cwd: Path, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if result.returncode != 0:
        print(f"FAILED command: {' '.join(cmd)}", flush=True)
        print(result.stdout, flush=True)
        raise SystemExit(result.returncode)
    return result


def compile_strict_modules(lean_dir: Path, modules: list[str], env: dict[str, str]) -> None:
    print(
        f"[2/4] Compiling all {len(modules)} modules freshly with `lake env lean -j1 -DwarningAsError=true`...",
        flush=True,
    )
    build_lib = lean_dir / ".lake" / "build" / "lib" / "lean"
    # Clean any pre-existing project .olean artifacts to guarantee a clean fresh build
    for stale in (build_lib / f"{PROJECT_ROOT}.olean", build_lib / f"{PROJECT_ROOT}.olean.server", build_lib / f"{PROJECT_ROOT}.olean.private"):
        if stale.exists():
            stale.unlink()
    proj_dir = build_lib / PROJECT_ROOT
    if proj_dir.exists():
        shutil.rmtree(proj_dir)

    for idx, mod in enumerate(modules, 1):
        rel_src = mod.replace(".", "/") + ".lean"
        out_olean = build_lib / (mod.replace(".", "/") + ".olean")
        out_olean.parent.mkdir(parents=True, exist_ok=True)
        res = run_cmd(
            ["lake", "env", "lean", "-j1", "-DwarningAsError=true", "-o", str(out_olean), rel_src],
            cwd=lean_dir,
            env=env,
        )
        if res.stdout.strip():
            print(res.stdout.strip(), flush=True)
        print(f"      [{idx:2d}/{len(modules)}] PASS {mod}", flush=True)
    print(f"      PASS: all {len(modules)} modules compiled with 0 errors and 0 warnings.", flush=True)


def generate_audit_lean(modules: list[str], required: tuple[str, ...]) -> str:
    imports = "\n".join(f"import {mod}" for mod in sorted(modules))
    expected_mods = ", ".join(json.dumps(mod) for mod in sorted(modules))
    req_names = ", ".join("`" + name for name in required)
    allowed_names = ", ".join("`" + name for name in ALLOWED_AXIOMS)
    return f"""{imports}
import Lean.Util.CollectAxioms
import Lean.PrivateName
import Lean.Elab.Command
import Lean.Data.Json

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let expectedModules : Array String := #[{expected_mods}]
  let required : Array Name := #[{req_names}]
  let allowed : Array Name := #[{allowed_names}]
  let env ← getEnv
  if env.header.isModule then
    throwError "All-owned audit must use legacy private-import mode"
  unless env.header.modules.size == env.header.moduleData.size do
    throwError "Imported module/data inventory size mismatch"
  let mut rawNames : NameSet := {{}}
  let mut seenModules : Array String := #[]
  for h : idx in [0:env.header.modules.size] do
    let mod := env.header.modules[idx]
    let moduleName := mod.module.toString
    let isProject := moduleName == "{PROJECT_ROOT}" || moduleName.startsWith "{PROJECT_ROOT}."
    unless !isProject || expectedModules.contains moduleName do
      throwError "Unregistered project module in audit: {{moduleName}}"
    if expectedModules.contains moduleName then
      unless mod.hasData && mod.importAll do
        throwError "Project module lacks complete private data: {{moduleName}}"
      let data := env.header.moduleData[idx]!
      unless data.constNames == data.constants.map (·.name) do
        throwError "Serialized declaration names differ from their constants: {{moduleName}}"
      seenModules := seenModules.push moduleName
      let mut privateCount := 0
      for name in data.constNames do
        unless (env.find? name).isSome do
          throwError "Serialized project declaration is invisible: {{moduleName}}: {{name}}"
        rawNames := rawNames.insert name
        if (privateToUserName? name).isSome then
          privateCount := privateCount + 1
      let record := Json.mkObj [
        ("tag", toJson "module"),
        ("module", toJson moduleName),
        ("import_all", toJson mod.importAll),
        ("has_data", toJson mod.hasData),
        ("names", toJson (data.constNames.map (·.toString))),
        ("private_count", toJson privateCount)
      ]
      logInfo m!"{MARKER}{{record.compress}}"
  unless seenModules.size == expectedModules.size &&
      expectedModules.all seenModules.contains do
    throwError "Incomplete exact project module inventory"
  let mut audited : NameSet := {{}}
  let mut declarations := 0
  let mut theorems := 0
  let mut privateDeclarations := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name |>.bind (env.header.modules[·]?) with
      | some mod => mod.module.toString
      | none => ""
    let byModule := expectedModules.contains owner
    let bySerialized := rawNames.contains name
    if byModule || bySerialized then
      declarations := declarations + 1
      audited := audited.insert name
      let kind := match info with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quotient"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .inductInfo _ => "inductive"
      if info.isTheorem then
        theorems := theorems + 1
      let privateName := privateToUserName? name
      if privateName.isSome then
        privateDeclarations := privateDeclarations + 1
      if let .axiomInfo _ := info then
        unless allowed.contains name do
          throwError "Unapproved project axiom {{name}}"
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unapproved axiom {{axiomName}} in {{name}}"
      let record := Json.mkObj [
        ("tag", toJson "declaration"),
        ("name", toJson name.toString),
        ("owner", toJson owner),
        ("kind", toJson kind),
        ("private_user_name", toJson (privateName.map (·.toString))),
        ("by_module", toJson byModule),
        ("by_serialized", toJson bySerialized),
        ("axioms", toJson (axioms.map (·.toString)))
      ]
      logInfo m!"{MARKER}{{record.compress}}"
  for name in rawNames.toArray do
    unless audited.contains name do
      throwError "Serialized project declaration escaped the audit: {{name}}"
  for name in required do
    let _ ← getConstInfo name
    unless audited.contains name do
      throwError "Required declaration is outside audited ownership: {{name}}"
    let record := Json.mkObj [("tag", toJson "required"), ("name", toJson name.toString)]
    logInfo m!"{MARKER}{{record.compress}}"
  let record := Json.mkObj [
    ("tag", toJson "passed"),
    ("modules", toJson seenModules.size),
    ("declarations", toJson declarations),
    ("theorems", toJson theorems),
    ("private_declarations", toJson privateDeclarations),
    ("raw_declarations", toJson rawNames.toArray.size),
    ("required", toJson required.size),
    ("allowed_axioms", toJson (allowed.map (·.toString)))
  ]
  logInfo m!"{MARKER}{{record.compress}}"
"""


def run_all_owned_audit(lean_dir: Path, modules: list[str], env: dict[str, str]) -> dict:
    print(f"[3/4] Running all-owned declaration & transitive axiom audit...", flush=True)
    audit_src = generate_audit_lean(modules, REQUIRED_ENDPOINTS)
    with tempfile.TemporaryDirectory(prefix="ap-audit-") as tmp:
        audit_path = Path(tmp) / "AllOwnedAudit.lean"
        audit_path.write_text(audit_src, encoding="utf-8")
        res = run_cmd(
            ["lake", "env", "lean", "-j1", "-DwarningAsError=true", str(audit_path)],
            cwd=lean_dir,
            env=env,
        )

    records = []
    for line in res.stdout.splitlines():
        if MARKER in line:
            records.append(json.loads(line.split(MARKER, 1)[1]))

    tagged: dict[str, list[dict]] = {t: [] for t in ("module", "declaration", "required", "passed")}
    for rec in records:
        tag = rec.get("tag")
        if tag not in tagged:
            raise RuntimeError(f"Unexpected audit record tag: {tag}")
        tagged[tag].append(rec)

    if len(tagged["passed"]) != 1:
        raise RuntimeError(f"Expected exactly 1 passed summary record, got {len(tagged['passed'])}")
    summary = tagged["passed"][0]

    mod_map = {row["module"]: row for row in tagged["module"]}
    if len(mod_map) != len(tagged["module"]) or set(mod_map) != set(modules):
        raise RuntimeError("Imported project module set mismatch in audit")

    raw_names: set[str] = set()
    for name, row in mod_map.items():
        if not row["import_all"] or not row["has_data"] or len(row["names"]) != len(set(row["names"])):
            raise RuntimeError(f"Incomplete private raw-module data for {name}")
        raw_names.update(row["names"])

    decl_map = {row["name"]: row for row in tagged["declaration"]}
    if len(decl_map) != len(tagged["declaration"]) or not raw_names <= set(decl_map):
        raise RuntimeError("Repeated or omitted serialized declaration in audit")

    used_axioms: set[str] = set()
    allowed_set = set(ALLOWED_AXIOMS)
    for name, row in decl_map.items():
        if row["kind"] not in VALID_KINDS:
            raise RuntimeError(f"Unexpected declaration kind {row['kind']} for {name}")
        if row["kind"] == "axiom" and name not in allowed_set:
            raise RuntimeError(f"Unapproved direct project axiom: {name}")
        decl_axioms = set(row["axioms"])
        if not decl_axioms <= allowed_set:
            raise RuntimeError(f"Unapproved transitive axioms {decl_axioms - allowed_set} in {name}")
        used_axioms.update(decl_axioms)

    private_decls = {n for n, r in decl_map.items() if r["private_user_name"] is not None}
    for mod_name, row in mod_map.items():
        if row["private_count"] != sum(d in private_decls for d in row["names"]):
            raise RuntimeError(f"Private declaration count mismatch for {mod_name}")

    req_seen = [row["name"] for row in tagged["required"]]
    if len(req_seen) != len(set(req_seen)) or set(req_seen) != set(REQUIRED_ENDPOINTS):
        raise RuntimeError("Required endpoint theorem inventory mismatch")

    kinds = Counter(row["kind"] for row in decl_map.values())
    expected_summary = {
        "tag": "passed",
        "modules": len(mod_map),
        "declarations": len(decl_map),
        "theorems": kinds["theorem"],
        "private_declarations": len(private_decls),
        "raw_declarations": len(raw_names),
        "required": len(req_seen),
        "allowed_axioms": list(ALLOWED_AXIOMS),
    }
    if summary != expected_summary:
        raise RuntimeError(f"Audit summary mismatch: got {summary}, expected {expected_summary}")

    endpoint_axioms = {ep: sorted(decl_map[ep]["axioms"]) for ep in REQUIRED_ENDPOINTS}
    print(
        f"      PASS: {len(mod_map)} modules, {len(decl_map)} owned declarations "
        f"({kinds['theorem']} theorems, {len(private_decls)} private), "
        f"{len(req_seen)}/{len(REQUIRED_ENDPOINTS)} required endpoints verified.",
        flush=True,
    )
    print(f"      Axioms used across entire project: {sorted(used_axioms)}", flush=True)
    return {
        "summary": summary,
        "kind_counts": dict(kinds),
        "used_axioms": sorted(used_axioms),
        "endpoint_axioms": endpoint_axioms,
        "module_declaration_counts": {m: len(mod_map[m]["names"]) for m in sorted(mod_map)},
    }


def run_kernel_replay(lean_dir: Path, modules: list[str], env: dict[str, str]) -> None:
    print(f"[4/4] Replaying all {len(modules)} compiled modules via pinned `leanchecker`...", flush=True)
    res = run_cmd(
        ["lake", "env", "leanchecker", "-v", PROJECT_ROOT],
        cwd=lean_dir,
        env=env,
    )
    lines = [ln for ln in res.stdout.splitlines() if ln.strip()]
    print(f"      PASS: `leanchecker -v {PROJECT_ROOT}` exited 0 ({len(lines)} output lines).", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--skip-compile",
        action="store_true",
        help="Skip fresh per-module compilation (only use if `.olean` files were just built).",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help="Optional path to write a JSON verification summary.",
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent
    lean_dir = repo_root / "lean"
    toolchain = (lean_dir / "lean-toolchain").read_text(encoding="utf-8").strip()
    modules = discover_project_modules(lean_dir)

    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    elan_bin = Path.home() / ".elan" / "bin"
    if elan_bin.is_dir():
        env["PATH"] = str(elan_bin) + os.pathsep + env.get("PATH", "")

    print(f"Verifying Lean formalization (toolchain: {toolchain}, modules: {len(modules)})", flush=True)
    check_source_hygiene(lean_dir, modules)
    if not args.skip_compile:
        compile_strict_modules(lean_dir, modules, env)
    else:
        print("[2/4] Skipping fresh compilation (--skip-compile).", flush=True)
    audit_report = run_all_owned_audit(lean_dir, modules, env)
    run_kernel_replay(lean_dir, modules, env)

    if args.json_out is not None:
        report = {
            "toolchain": toolchain,
            "modules_compile_order": modules,
            **audit_report,
            "kernel_replay": "PASS",
        }
        args.json_out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print("ALL CHECKS PASSED: zero sorry, zero custom axioms, 0 warnings, kernel replay verified.", flush=True)


if __name__ == "__main__":
    main()
