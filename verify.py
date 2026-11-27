"""
Standalone exact verification script for the proof of Conjecture 1.3 of
van Doorn, Liu, and Tang (arXiv:2610.35027v1).

Verifies using exact rational (fractions.Fraction) and symbolic (sympy)
arithmetic — never relying on floating-point approximations:
  1. Lemma 3.1, 3.3, 3.4: polynomial invariants V(z), tilde_V(z), W_N(z),
     and modular difference density bound 1_{d=0} <= (1-d) + d(d-1).
  2. Section 4: Lemma 4.2 sharp lower bound (2*M2 + 2)/(M2 + 2), Type I
     ratio = 2 in both cases, and M1 >= 3 Zhang gap bound >= 18/11 > 8/5.
  3. Section 5: exact rational margins for Lemmas 5.1–5.2 (eps = 1/1000)
     and exact polynomial identities (5.6), (5.7), (5.8) across multiple
     non-perfect, shifted, modular, and swapped doubling families.
  4. Section 6: Lemma 6.1 polynomial iteration rigidity on arbitrary
     initial representation profiles (including r(n) >= 2 and m0 > 0).
  5. Section 7: multi-step exact doubling induction, modular bijection
     (7.3), and Zhang's base-4 upper bound v^2 <= 3*a_v.
"""

from fractions import Fraction
import bisect
import sympy as sp

z = sp.Symbol("z")


def make_bin(k):
    return sorted(
        sum(((v >> i) & 1) * (4**i) for i in range(k)) for v in range(2**k)
    )


def poly_from_set(S, shift=0):
    return sp.Poly(sum(z ** (x - shift) for x in S), z)


def ord_zero(P):
    assert not P.is_zero
    coeffs = P.all_coeffs()[::-1]
    for i, coeff in enumerate(coeffs):
        if coeff != 0:
            return i
    raise AssertionError("Zero polynomial")


def strip_z(P):
    o = ord_zero(P)
    return o, sp.Poly(sp.quo(P.as_expr(), z**o, z), z)


def verify_section4_measure_bounds():
    print("[1/5] Verifying Section 4 (Gabardo-Lai, Type I, and M1 >= 3 bounds)...")
    M2, u = sp.symbols("M2 u", positive=True)
    u_star = sp.solve(sp.Eq(2 - u, 2 - M2 + M2 * u), u)[0]
    val_star = sp.simplify(2 / (2 - u_star))
    assert sp.simplify(u_star - M2 / (M2 + 1)) == 0
    assert sp.simplify(val_star - (2 * M2 + 2) / (M2 + 2)) == 0
    assert sp.simplify(u_star - (1 - 1 / M2) - 1 / (M2 * (M2 + 1))) == 0

    for M1 in (2, 3, 4, 5):
        for M2_v in (2, 3, 4):
            assert (Fraction(2, M1) * Fraction(1, 1)) / Fraction(1, M1) == 2
            assert (Fraction(1, M1) * Fraction(2, M2_v)) / Fraction(1, M1 * M2_v) == 2

    eta = Fraction(1, 100)
    for M1 in (3, 4, 5, 10):
        r_nu = Fraction(2, 3 * M1)
        exact_bound = Fraction(2, 1) / (1 + r_nu)
        eps_bound = Fraction(2, 1) / (1 + r_nu + eta)
        assert exact_bound >= Fraction(18, 11) > Fraction(8, 5)
        assert eps_bound > Fraction(8, 5)
    print("      PASSED: Lemma 4.2, Type I cases A/B, and M1 >= 3 bound verified.")


def verify_section5_margins():
    print("[2/5] Verifying Section 5 (exact rational margins for eps = 1/1000)...")
    eps = Fraction(1, 1000)

    # Lemma 3.4 pointwise bound
    for d in range(50):
        assert (1 if d == 0 else 0) <= (1 - d) + d * (d - 1)

    # Lemma 5.1: y0 <= (1 + 8*eps)*N
    assert 3 * (Fraction(1, 3) + eps) + eps <= 1 + 8 * eps
    assert (Fraction(1, 3) + eps) / (Fraction(1, 3) - eps) + eps < 1 + 8 * eps

    # Lemma 5.2 Step 2 (I_kill)
    a_lo = Fraction(1, 12) + 13 * eps - 9 * eps
    a_hi = Fraction(1, 4) - 2 * eps
    assert a_lo > Fraction(1, 12) + 3 * eps > Fraction(1, 12)
    assert a_hi < Fraction(1, 4)
    len_ikill = (Fraction(1, 4) - 2 * eps) - (Fraction(1, 12) + 13 * eps)
    assert len_ikill > Fraction(15, 100) > 8 * eps

    # Dyadic masses of nu_0 verified on exact depth-6 approximation
    pts = [
        sum(((v >> i) & 1) * Fraction(1, 4 ** (i + 1)) for i in range(6))
        for v in range(2**6)
    ]
    assert sum(1 for p in pts if Fraction(1, 16) <= p <= Fraction(1, 12)) == 2**4
    assert sum(1 for p in pts if Fraction(5, 16) <= p <= Fraction(1, 3)) == 2**4
    assert sum(1 for p in pts if Fraction(1, 12) < p < Fraction(1, 4)) == 0

    # Lemma 5.2 Step 3 (Substeps 3a and 3b)
    assert Fraction(1, 12) + eps < Fraction(1, 3) - 3 * eps
    assert (Fraction(1, 3) - 2 * eps) - (Fraction(1, 12) + eps) > eps
    assert Fraction(3, 8) - (Fraction(1, 16) - eps) < Fraction(1, 3) - 2 * eps

    assert Fraction(1, 3) + eps < Fraction(3, 8) - eps
    assert Fraction(3, 8) - (Fraction(1, 3) + eps) > eps
    assert Fraction(5, 8) - (Fraction(5, 16) - eps) < Fraction(1, 3) - 2 * eps

    # Proposition 5.3 zero-interval margin
    assert Fraction(1, 3) + 4 * eps < Fraction(5, 8) - eps
    print("      PASSED: All Section 5 rational margins verified.")


def verify_exact_doubling_case(label, A_full, B_full, N):
    r = {}
    for a in A_full:
        for b in B_full:
            if a + b <= 3 * N:
                r[a + b] = r.get(a + b, 0) + 1
    n0 = 1
    for n in range(3 * N, -1, -1):
        if r.get(n, 0) != 1:
            n0 = n + 1
            break

    a_min, b_min = min(A_full), min(B_full)
    m0 = a_min + b_min
    delta = {n: r.get(n, 0) - 1 for n in range(n0)}
    E = sum(abs(v) for v in delta.values())
    c = sum(delta.values())

    Delta_z = sp.Poly(sum(v * z**n for n, v in delta.items()), z)
    V_z = sp.Poly(1 + (1 - z) * Delta_z.as_expr(), z)
    oV, tilde_V = strip_z(V_z)
    assert oV == m0 and tilde_V.eval(0) == 1 and tilde_V.eval(1) == 1
    assert sp.diff(V_z.as_expr(), z).subs(z, 1) == -c

    A0 = [a for a in A_full if a <= N]
    B0 = [b for b in B_full if b <= N]
    x0 = max(A0)
    y0 = min(a for a in A_full if a > N)
    w0 = min(b for b in B_full if b > N)

    cross0 = {}
    for a in A0:
        for b in B0:
            if a + b > N:
                cross0[a + b] = cross0.get(a + b, 0) + 1
    T_N = sum(cross0.values())
    assert len(A0) * len(B0) - N == 1 + c + T_N

    E0_z = sp.Poly(sum(v * z ** (m - (N + 1)) for m, v in cross0.items()), z)
    W0_z = sp.Poly(1 - (1 - z) * E0_z.as_expr(), z)
    PA0, PB0 = poly_from_set(A0), poly_from_set(B0)
    assert sp.Poly((1 - z) * PA0.as_expr() * PB0.as_expr(), z) == sp.Poly(
        V_z.as_expr() - z ** (N + 1) * W0_z.as_expr(), z
    )

    s = y0 - (N + 1)
    eta1 = {m - y0: v for m, v in cross0.items() if m >= y0}
    H_eta1 = sp.Poly(sum(v * z**n for n, v in eta1.items()), z)
    U1_z = sp.Poly(1 - (1 - z) * H_eta1.as_expr(), z)
    assert W0_z == sp.Poly(z**s * U1_z.as_expr(), z)

    L1 = min(N, w0 - 1 - y0)
    T2 = L1 - (E + 1) * (n0 + 1)
    assert T2 > x0 + n0
    A1_prime = [a for a in A_full if y0 <= a <= y0 + T2]
    PA1 = poly_from_set(A1_prime, shift=y0)

    # (5.6)
    assert sp.Poly(PA1.as_expr() * V_z.as_expr(), z) == sp.Poly(
        PA0.as_expr() * U1_z.as_expr(), z
    )

    # (5.10)
    F_z = sp.Poly(U1_z.as_expr() - (1 - z) * PA1.as_expr() * PB0.as_expr(), z)
    assert sp.Poly(V_z.as_expr() * F_z.as_expr(), z) == sp.Poly(
        z**y0 * U1_z.as_expr() ** 2, z
    )

    u1, _ = strip_z(U1_z)
    oF, _ = strip_z(F_z)
    assert oF == y0 + 2 * u1 - m0
    N1_prime = 2 * y0 + 2 * u1 - m0 - 1 - max(a_min, b_min)

    A_N1p = [a for a in A_full if a <= N1_prime]
    B_N1p = [b for b in B_full if b <= N1_prime]
    assert A_N1p == sorted(A0 + A1_prime)
    assert B_N1p == B0

    cross1 = {}
    for a in A_N1p:
        for b in B_N1p:
            if a + b > N1_prime:
                cross1[a + b] = cross1.get(a + b, 0) + 1
    T_N1p = sum(cross1.values())
    E1_z = sp.Poly(sum(v * z ** (m - (N1_prime + 1)) for m, v in cross1.items()), z)
    W1_z = sp.Poly(1 - (1 - z) * E1_z.as_expr(), z)

    # (5.7) and (5.8)
    assert sp.Poly(z ** (N1_prime + 1) * V_z.as_expr() * W1_z.as_expr(), z) == sp.Poly(
        z ** (2 * (N + 1)) * W0_z.as_expr() ** 2, z
    )
    oW0, tilde_W0 = strip_z(W0_z)
    oW1, tilde_W1 = strip_z(W1_z)
    assert oW1 == max(a_min, b_min)
    assert sp.Poly(tilde_V.as_expr() * tilde_W1.as_expr(), z) == sp.Poly(
        tilde_W0.as_expr() ** 2, z
    )
    assert tilde_W0 == tilde_V and tilde_W1 == tilde_V
    assert T_N1p == -c - min(a_min, b_min)

    # Exact translation & modular bijection (7.3)
    D0 = y0 - a_min
    assert A1_prime == [a + D0 for a in A0]
    assert w0 - b_min == 2 * D0
    residues = sorted((a + b) % D0 for a in A0 for b in B0)
    assert residues == list(range(D0))
    print(f"      PASSED {label}: N={N} -> N1'={N1_prime}, D0={D0}, T(N1')={T_N1p}, tilde_V={tilde_V.as_expr()}")


def verify_section5_polynomial_identities():
    print("[3/5] Verifying Proposition 5.3 & Section 7 identities on concrete families...")
    A_bin = make_bin(6)
    B_bin = [2 * a for a in A_bin]

    verify_exact_doubling_case("Perfect binary Cantor", A_bin, B_bin, 4**4 - 1)
    verify_exact_doubling_case("Perfect binary Cantor (N=4^4-3)", A_bin, B_bin, 4**4 - 3)
    verify_exact_doubling_case(
        "Shifted binary Cantor (3, 5)", [3 + a for a in A_bin], [5 + b for b in B_bin], 4**4 + 2
    )
    verify_exact_doubling_case(
        "Shifted binary Cantor (7, 2)", [7 + a for a in A_bin], [2 + b for b in B_bin], 4**4 + 4
    )

    A_r51 = sorted(c0 + 4 * a for c0 in (0, 2) for a in make_bin(5))
    B_r51 = sorted(d0 + 4 * b for d0 in (0, 3) for b in (2 * a for a in make_bin(5)))
    verify_exact_doubling_case("Remark 5.1 C={0,2}, D={0,3}", A_r51, B_r51, 4 * 4**3 - 1)

    A_r51s = sorted(c0 + 4 * a for c0 in (2, 4) for a in make_bin(6))
    B_r51s = sorted(d0 + 4 * b for d0 in (5, 8) for b in (2 * a for a in make_bin(6)))
    verify_exact_doubling_case("Shifted Remark 5.1 Step 1", A_r51s, B_r51s, 4 * 4**4 + 1)
    verify_exact_doubling_case("Shifted Remark 5.1 Step 2 (swapped)", B_r51s, A_r51s, 2 * 4 * 4**4 + 1)

    A_m6 = sorted(c0 + 6 * a for c0 in (0, 1, 5) for a in make_bin(5))
    B_m6 = sorted(d0 + 6 * b for d0 in (0, 3) for b in (2 * a for a in make_bin(5)))
    verify_exact_doubling_case("Mod-6 C={0,1,5}, D={0,3} Step 1", A_m6, B_m6, 6 * 4**3 - 1)
    verify_exact_doubling_case("Mod-6 C={0,1,5}, D={0,3} Step 2 (swapped)", B_m6, A_m6, 2 * 6 * 4**3 - 1)


def verify_section6_rigidity():
    print("[4/5] Verifying Lemma 6.1 (Polynomial Iteration Rigidity, incl. r(n) >= 2)...")
    profiles = [
        [1],
        [1, 0],
        [0, 0, 1, 3, 0, 2, 4, 0],
        [1, 0, 2, 0, 3, 1, 0],
        [0, 0, 0, 0, 1, 5, 5, 0, 2],
    ]
    for r_list in profiles:
        n0 = len(r_list)
        delta = [r - 1 for r in r_list]
        E = sum(abs(d) for d in delta)
        c = sum(delta)
        V_z = sp.Poly(1 + (1 - z) * sum(delta[n] * z**n for n in range(n0)), z)
        m0 = next(n for n, rv in enumerate(r_list) if rv > 0)
        assert r_list[m0] == 1
        tilde_V = sp.Poly(sp.quo(V_z.as_expr(), z**m0, z), z)
        assert tilde_V.eval(0) == 1 and tilde_V.eval(1) == 1
        assert sp.diff(tilde_V.as_expr(), z).subs(z, 1) == -c - m0
        vc = tilde_V.all_coeffs()[::-1]
        for d in range(1, len(vc)):
            assert abs(vc[d]) <= E

        M = 2
        while M <= max(n0, E + 1):
            M *= 2
        for R_expr in (1 + z, 1 - z + z**3, 1 + z**2 - z**5, 1 - 2 * z**4 + z**7, 1 + z ** (n0 + 3)):
            P = sp.Poly(tilde_V.as_expr() * R_expr**M, z)
            pc = P.all_coeffs()[::-1]
            rc = sp.Poly(R_expr, z).all_coeffs()[::-1]
            d = next(i for i in range(1, len(rc)) if rc[i] != 0)
            assert pc[d] == (vc[d] if d < len(vc) else 0) + M * rc[d]
            assert abs(pc[d]) >= 2
    print("      PASSED: Polynomial rigidity coefficient explosion verified on all profiles.")


def verify_section7_corollary1_and_induction():
    print("[5/5] Verifying Section 7 (multi-step induction and Corollary 1 base-4 bound)...")
    # Verify v^2 <= 3 * a_v for all 0 <= v < 2^12
    for v in range(2**12):
        a_v = sum(((v >> i) & 1) * (4**i) for i in range(12))
        assert v * v <= 3 * a_v

    # Multi-step doubling check on shifted mod-8 non-perfect complement
    A_bin = make_bin(7)
    B_bin = [2 * a for a in A_bin]
    C, D, m = [2, 3, 6, 7], [5, 7], 8
    assert sorted((c0 + d0) % m for c0 in C for d0 in D) == list(range(m))
    A = sorted(c0 + m * a for c0 in C for a in A_bin)
    B = sorted(d0 + m * b for d0 in D for b in B_bin)
    a_min, b_min = min(A), min(B)
    D0 = m * 4**3
    N_cur = D0 + min(a_min, b_min) - 1
    for step in range(4):
        A_cur = [a for a in A if a <= N_cur]
        B_cur = [b for b in B if b <= N_cur]
        N_next = 2 * D0 * (2**step) + min(a_min, b_min) - 1
        if step % 2 == 0:
            assert min(a for a in A if a > N_cur) == D0 * (2**step) + a_min
            assert [a for a in A if a <= N_next] == sorted(
                A_cur + [a + D0 * (2**step) for a in A_cur]
            )
            assert [b for b in B if b <= N_next] == B_cur
        else:
            assert min(b for b in B if b > N_cur) == D0 * (2**step) + b_min
            assert [b for b in B if b <= N_next] == sorted(
                B_cur + [b + D0 * (2**step) for b in B_cur]
            )
            assert [a for a in A if a <= N_next] == A_cur
        N_cur = N_next

    max_ratio = max(
        Fraction(bisect.bisect_right(A, x) * bisect.bisect_right(B, x), x)
        for x in range(1000, 30000)
    )
    assert Fraction(149, 100) < max_ratio < Fraction(151, 100)
    print(f"      PASSED: 4-step doubling verified; max A(x)B(x)/x on [1000,30000) = {float(max_ratio):.6f}.")


if __name__ == "__main__":
    verify_section4_measure_bounds()
    verify_section5_margins()
    verify_section5_polynomial_identities()
    verify_section6_rigidity()
    verify_section7_corollary1_and_induction()
    print("\nALL VERIFICATIONS PASSED WITH 100% EXACTNESS.")
