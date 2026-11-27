"""check_proof.py -- ozawa-entropy-variation, stage 4 (Prove), 2026-11-27.

Sanity checks for PROOF.md.  NOT a certificate: the certificate is cert/OZ-1.py and
cert/OZ-1_x.py (CERT.md).  Every argument in PROOF.md is written out by hand; this
script only re-checks each lemma at its smallest cases and guards against slips.

Parts
  EX  exact checks (fractions.Fraction only): identities of Lemma 4 for integer and
      non-integer rational m, the literal witnesses m = 5, 7, the equality
      Tr(|D| B)^2 = 2 Tr(S B^2) at B = S^{-1}, the rational arithmetic of the by-hand
      reductions (PROOF.md section 5), the faithful witness of Corollary A5.
  NUM floating-point / mpmath checks (status `numerical`): definition-level values
      against the closed form and against the digits copied from CERT.md section 4,
      the lower bound of (A3), Proposition B, Proposition C, monotonicity, and the
      corrected form of section 8.

Run:  python check_proof.py        (exit 0 iff every check passes)
"""
import sys
from fractions import Fraction as F

import mpmath as mp
import numpy as np

FAIL = []
NCHK = [0]


def check(name, ok):
    NCHK[0] += 1
    print(("  ok    " if ok else "  FAIL  ") + name)
    if not ok:
        FAIL.append(name)


# ----------------------------------------------------------------------------
# exact 2x2 helpers
# ----------------------------------------------------------------------------
def mm(X, Y):
    return [[sum(X[i][k] * Y[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def lin(a, X, b, Y):
    return [[a * X[i][j] + b * Y[i][j] for j in range(2)] for i in range(2)]


def sc(a, X):
    return [[a * X[i][j] for j in range(2)] for i in range(2)]


def tr(X):
    return X[0][0] + X[1][1]


def det(X):
    return X[0][0] * X[1][1] - X[0][1] * X[1][0]


def outer(a, b):
    return [[a[i] * b[j] for j in range(2)] for i in range(2)]


def mv(X, a):
    return [X[i][0] * a[0] + X[i][1] * a[1] for i in range(2)]


I2 = [[F(1), F(0)], [F(0), F(1)]]
Z2 = [[F(0), F(0)], [F(0), F(0)]]
RHO = [[F(1), F(0)], [F(0), F(0)]]


def family(m):
    m = F(m)
    N = m * m
    v = [(N - 1) / (N + 1), 2 * m / (N + 1)]
    u = [F(1), -m]
    up = [m, F(1)]
    sigma = outer(v, v)
    A = sc(1 / (N + 1), outer(u, u))
    Ap = sc(1 / (N + 1), outer(up, up))
    return N, v, u, up, sigma, A, Ap


print("EX. exact checks (Fractions)")
for m in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, F(1, 2), F(3, 2), F(7, 3), F(1, 10), F(41, 5)]:
    N, v, u, up, sigma, A, Ap = family(m)
    m_ = F(m)
    s = 2 * m_ / (N + 1)
    x = 1 / (N + 1)
    ok = True
    # (4a) orthogonal frame
    ok &= u[0] * up[0] + u[1] * up[1] == 0
    ok &= u[0] ** 2 + u[1] ** 2 == N + 1 == up[0] ** 2 + up[1] ** 2
    ok &= lin(1, A, 1, Ap) == I2 and mm(A, A) == A and mm(Ap, Ap) == Ap and mm(A, Ap) == Z2
    ok &= tr(A) == 1 and tr(Ap) == 1 and A[0][1] == A[1][0] and A[0][0] >= 0 and A[1][1] >= 0 and det(A) >= 0
    # (4b) e1 and v in the frame
    e1 = [F(1), F(0)]
    ok &= [(u[i] + m_ * up[i]) / (N + 1) for i in range(2)] == e1
    ok &= [(-u[i] + m_ * up[i]) / (N + 1) for i in range(2)] == v
    ok &= v[0] ** 2 + v[1] ** 2 == 1 and mm(sigma, sigma) == sigma and tr(sigma) == 1
    # (4c) D and S
    D = lin(1, RHO, -1, sigma)
    S = lin(1, RHO, 1, sigma)
    E = sc(1 / (N + 1), lin(1, outer(up, u), 1, outer(u, up)))
    ok &= D == sc(s, E) and mm(E, E) == I2 and tr(D) == 0
    ok &= mm(D, D) == sc(s * s, I2)
    ok &= S == lin(2 * N / (N + 1), Ap, 2 / (N + 1), A)
    ok &= mv(S, u) == [2 / (N + 1) * c for c in u] and mv(S, up) == [2 * N / (N + 1) * c for c in up]
    # (4d) the three quantities
    absD = sc(s, I2)
    lhs = tr(mm(absD, A))
    q = tr(mm(S, mm(A, A)))
    ok &= lhs == s and q == 2 / (N + 1) == 2 * x
    W = sc(F(1, 2), S)
    ok &= W == lin(1 - x, Ap, x, A)
    ok &= lhs ** 2 / q == 2 * N / (N + 1)
    # (A4) B = S^{-1}
    B = lin((N + 1) / (2 * N), Ap, (N + 1) / 2, A)
    ok &= mm(S, B) == I2 and B[0][0] > 0 and det(B) > 0
    ok &= tr(B) == (N + 1) ** 2 / (2 * N)
    ok &= tr(mm(absD, B)) ** 2 == 2 * tr(mm(S, mm(B, B)))
    check("m=%s: Lemma 4 (frame, e1, v, D, S, A), LHS = %s, Tr(S A^2) = %s, x = %s; "
          "B = S^-1 gives Tr(|D|B)^2 = 2 Tr(S B^2)" % (m, lhs, q, x), ok)

# smallest case m = 1: commuting states
N, v, u, up, sigma, A, Ap = family(1)
check("m=1 (smallest case): sigma = diag(0,1) commutes with rho; LHS = 1, Tr(S A^2) = 1, x = 1/2",
      sigma == [[F(0), F(0)], [F(0), F(1)]] and A == [[F(1, 2), F(-1, 2)], [F(-1, 2), F(1, 2)]])

# literal witnesses as printed in PROOF.md section 2
LIT = {
    5: ([[F(144, 169), F(60, 169)], [F(60, 169), F(25, 169)]],
        [[F(1, 26), F(-5, 26)], [F(-5, 26), F(25, 26)]], F(5, 13), F(1, 13), F(1, 26)),
    7: ([[F(576, 625), F(168, 625)], [F(168, 625), F(49, 625)]],
        [[F(1, 50), F(-7, 50)], [F(-7, 50), F(49, 50)]], F(7, 25), F(1, 25), F(1, 50)),
}
for m, (sig_l, A_l, s_l, q_l, x_l) in LIT.items():
    N, v, u, up, sigma, A, Ap = family(m)
    D = lin(1, RHO, -1, sig_l)
    S = lin(1, RHO, 1, sig_l)
    check("m=%d: printed matrices equal the family; (rho-sigma)^2 = %s I; Tr(S A^2) = %s; "
          "S u = %s u; S u' = %s u'; (rho+sigma)/2 = (1-x)(1-A) + x A with x = %s"
          % (m, s_l ** 2, q_l, 2 * x_l, 2 * (1 - x_l), x_l),
          sig_l == sigma and A_l == A and mm(D, D) == sc(s_l ** 2, I2)
          and tr(mm(S, mm(A_l, A_l))) == q_l and mv(S, u) == [2 * x_l * c for c in u]
          and mv(S, up) == [2 * (1 - x_l) * c for c in up]
          and sc(F(1, 2), S) == lin(1 - x_l, lin(1, I2, -1, A_l), x_l, A_l))

# entry arithmetic quoted in PROOF.md section 5
check("entry arithmetic: 25^2+60^2 = 4225 = 25*169; 49^2+168^2 = 30625 = 49*625; "
      "313-300 = 13, 60-125 = -65; 1201-1176 = 25, 168-343 = -175; "
      "1565+60 = 1625 = 325*5, 300+25 = 325; 8407+168 = 8575 = 1225*7, 1176+49 = 1225",
      25 ** 2 + 60 ** 2 == 4225 == 25 * 169 and 49 ** 2 + 168 ** 2 == 30625 == 49 * 625
      and 313 - 300 == 13 and 60 - 125 == -65 and 1201 - 1176 == 25 and 168 - 343 == -175
      and 1565 + 60 == 1625 == 325 * 5 and 300 + 25 == 325
      and 8407 + 168 == 8575 == 1225 * 7 and 1176 + 49 == 1225
      and F(325, 169) == F(25, 13) and F(1225, 625) == F(49, 25))

# by-hand reductions (PROOF.md section 5): rational arithmetic only
check("m=5 natural: (1 + 21/4)/26 = 25/104 and 8*(25/104)*(1/13) = (5/13)^2; 2^5 = 32 > 26; 5 < 21/4",
      (1 + F(21, 4)) / 26 == F(25, 104) and 8 * F(25, 104) * F(1, 13) == F(5, 13) ** 2
      and 2 ** 5 > 26 and 5 < F(21, 4))
check("m=7 natural: 8*(49/200)*(1/25) = (7/25)^2; 2^6 = 64 > 50; (1 + 6)/50 = 7/50 < 49/200",
      8 * F(49, 200) * F(1, 25) == F(7, 25) ** 2 and 2 ** 6 > 50 and F(7, 50) < F(49, 200))
check("m=7 base 2: (3/2 + 6)/50 = 3/20 < 49/200",
      (F(3, 2) + 6) / 50 == F(3, 20) and F(3, 20) < F(49, 200))
check("m=5 base 2: 26 = 32*(13/16); ((13/16)*(3/2) + 5)/26 = 199/832 < 200/832 = 25/104",
      26 == 32 * F(13, 16) and (F(13, 16) * F(3, 2) + 5) / 26 == F(199, 832)
      and F(199, 832) < F(25, 104) == F(200, 832))

# (A3): arithmetic of the chain for C = 8 at the first guaranteed m
check("(A3) with C = 8: smallest integer m >= 8*sqrt(2) is 12 (11^2 = 121 < 128 <= 144 = 12^2)",
      11 ** 2 < 128 <= 12 ** 2)

# Corollary A5: faithful witness, m = 7, eps = 1/1000
eps = F(1, 1000)
N, v, u, up, sigma, A, Ap = family(7)
x = F(1, 50)
s = F(7, 25)
half = sc(F(1, 2), I2)
rho_e = lin(1 - eps, RHO, eps, half)
sig_e = lin(1 - eps, sigma, eps, half)
D_e = lin(1, rho_e, -1, sig_e)
S_e = lin(1, rho_e, 1, sig_e)
y = (1 - eps) * x + eps / 2
q_e = tr(mm(S_e, mm(A, A)))
lhs_e = (1 - eps) * s
thr = lhs_e ** 2 / (8 * q_e)
ok = True
ok &= tr(rho_e) == 1 and tr(sig_e) == 1 and det(rho_e) > 0 and det(sig_e) > 0 and rho_e[0][0] > 0 and sig_e[0][0] > 0
ok &= mm(D_e, D_e) == sc(lhs_e ** 2, I2) and tr(D_e) == 0
ok &= sc(F(1, 2), S_e) == lin(1 - y, Ap, y, A)
ok &= y == F(64, 3125) and q_e == F(128, 3125) == 2 * y and lhs_e == F(6993, 25000)
ok &= thr == F(48902049, 204800000)
# spectra of rho_e and sigma_e: 1 - eps/2 and eps/2 (roots of t^2 - t + det)
for R in (rho_e, sig_e):
    ok &= det(R) == (1 - eps / 2) * (eps / 2)
ok &= F(64, 3125) * 7 == F(448, 3125) and F(448, 3125) < thr
ok &= F(64, 3125) * (F(3, 2) + 6) == F(480, 3125) and F(480, 3125) < thr
ok &= F(3125, 64) < 64
check("Corollary A5 (m=7, eps=1/1000): faithful states, |D_eps| = (6993/25000) I, y = 64/3125, "
      "Tr(S_eps A^2) = 128/3125, threshold 48902049/204800000 > 448/3125 and > 480/3125", ok)

# ----------------------------------------------------------------------------
# NUM. numerical checks
# ----------------------------------------------------------------------------
print()
print("NUM. numerical checks (mpmath %s at 50 digits; numpy %s float64) -- status `numerical`"
      % (mp.__version__, np.__version__))
mp.mp.dps = 50


def h_mp(x):
    x = mp.mpf(x)
    return -x * mp.log(x) - (1 - x) * mp.log(1 - x)


def ent_mp(M):
    ev, _ = mp.eigsy(M)
    tot = mp.mpf(0)
    for lam in ev:
        if lam > mp.mpf(10) ** (-40):
            tot -= lam * mp.log(lam)
    return tot


def abs_mp(M):
    ev, Q = mp.eigsy(M)
    return Q * mp.diag([abs(e) for e in ev]) * Q.T


def to_mp(X):
    return mp.matrix([[mp.mpf(X[i][j].numerator) / X[i][j].denominator for j in range(2)] for i in range(2)])


def trunc(val, digits):
    """decimal string of a positive mpf truncated (not rounded) to `digits` decimals."""
    sc_ = mp.floor(val * mp.mpf(10) ** digits)
    sdig = mp.nstr(sc_, digits + 5, strip_zeros=False).split(".")[0]
    sdig = sdig.rjust(digits + 1, "0")
    return sdig[:-digits] + "." + sdig[-digits:]


# digits copied from cert/CERT.md section 4 (as quoted in PROOF.md section 5.5)
CERT4 = {
    5: ("0.16302362949436594046925930", "1.47453848334865481700577",
        "0.23519338181924149141542913", "1.02207219236025795050724"),
    7: ("0.09803911327973198061225941", "2.49900261032501436705753",
        "0.14144054254182064515437899", "1.73217661355872738185832"),
}
for m in (5, 7):
    N, v, u, up, sigma, A, Ap = family(m)
    rho_, sig_, A_ = to_mp(RHO), to_mp(sigma), to_mp(A)
    lhs = (abs_mp(rho_ - sig_) * A_)[0, 0] + (abs_mp(rho_ - sig_) * A_)[1, 1]
    SA2 = (rho_ + sig_) * A_ * A_
    q = SA2[0, 0] + SA2[1, 1]
    delta = ent_mp((rho_ + sig_) / 2) - (ent_mp(rho_) + ent_mp(sig_)) / 2
    x = mp.mpf(1) / (N + 1)
    r2 = lhs ** 2 / (8 * delta * q)
    r2b = r2 * mp.log(2)
    closed = mp.mpf(int(N)) / (4 * ((N + 1) * mp.log(int(N) + 1) - N * mp.log(int(N))))
    d_e, r_e, d_2, r_2 = CERT4[m]
    ok = (abs(lhs - mp.mpf(2 * m) / (N + 1)) < mp.mpf(10) ** (-40)
          and abs(q - mp.mpf(2) / (N + 1)) < mp.mpf(10) ** (-40)
          and abs(delta - h_mp(x)) < mp.mpf(10) ** (-40)
          and abs(r2 - closed) < mp.mpf(10) ** (-38))
    check("m=%d: definition-level LHS, Tr(S A^2), delta agree with 2m/(N+1), 2/(N+1), h(1/(N+1)), "
          "and with the closed form of (A2)" % m, ok)
    check("m=%d: digits quoted from CERT.md section 4 reproduced (truncation): delta_e, ratio_e^2, "
          "delta_2, ratio_2^2" % m,
          trunc(h_mp(x), len(d_e) - 2) == d_e and trunc(r2, len(r_e) - 2) == r_e
          and trunc(h_mp(x) / mp.log(2), len(d_2) - 2) == d_2 and trunc(r2b, len(r_2) - 2) == r_2)

# scalar facts of Lemma 3
check("Lemma 3: 2 < e < 3, ln 2 > 2/3, ln 26 < 21/4, ln 26 <= 5 ln 2 - 3/16, ln 50 < 6 ln 2",
      2 < mp.e < 3 and mp.log(2) > mp.mpf(2) / 3 and mp.log(26) < mp.mpf(21) / 4
      and mp.log(26) <= 5 * mp.log(2) - mp.mpf(3) / 16 and mp.log(50) < 6 * mp.log(2))
ok = True
for k in range(1, 4001):
    yv = mp.mpf(k) / 40
    ok &= mp.log(yv) <= 2 * mp.sqrt(yv) - 2 + mp.mpf(10) ** (-45)
    uu = mp.mpf(k) / 400
    ok &= mp.log(1 + uu) < uu
check("Lemma 3: ln y <= 2 sqrt(y) - 2 on y = k/40, k = 1..4000; ln(1+u) < u on u = k/400", ok)

# (A2)/(A3): elementary lower bounds along the family
ok = True
worst = None
for m in list(range(1, 3001)) + [mp.mpf(k) / 7 for k in range(7, 400)]:
    N = mp.mpf(m) ** 2
    x = 1 / (N + 1)
    r2 = (1 - x) / (4 * h_mp(x))
    lb1 = N / (4 * (1 + mp.log(N + 1)))
    lb2 = mp.mpf(m) / (8 * mp.sqrt(2))
    ok &= r2 > lb1 > lb2
    rel = r2 / lb2
    worst = rel if worst is None else min(worst, rel)
check("(A3): (LHS/RHS)^2 > N/(4(1+ln(N+1))) > m/(8 sqrt 2) for integer m = 1..3000 and m = k/7 in [1, 57) "
      "(smallest quotient ratio^2 / (m/(8 sqrt 2)) = %s)" % mp.nstr(worst, 6), ok)

# monotonicity of the closed form and the two thresholds
ok = True
prev = None
for k in range(100, 5001):
    m = mp.mpf(k) / 100
    x = 1 / (m * m + 1)
    r2 = (1 - x) / (4 * h_mp(x))
    if prev is not None:
        ok &= r2 > prev
    prev = r2


def r2_of(m, base2=False):
    x = 1 / (mp.mpf(m) ** 2 + 1)
    val = (1 - x) / (4 * h_mp(x))
    return val * mp.log(2) if base2 else val


check("Remark 5.6: closed form increasing in m on [1, 50] (grid 1/100); "
      "r2(3) < 1 < r2(4) natural; r2(4) < 1 < r2(5) base 2",
      ok and r2_of(3) < 1 < r2_of(4) and r2_of(4, True) < 1 < r2_of(5, True))

# (A4): range of delta along the family, and h on (0, 1/2]
ok = True
prev = mp.mpf(0)
for k in range(1, 5001):
    xv = mp.mpf(k) / 10000
    hv = h_mp(xv)
    ok &= hv > prev
    prev = hv
ok &= abs(h_mp(mp.mpf(1) / 2) - mp.log(2)) < mp.mpf(10) ** (-45) and h_mp(mp.mpf(10) ** (-30)) < mp.mpf(10) ** (-27)
check("Lemma 3(e): h increasing on (0, 1/2] (grid 1e-4), h(1/2) = ln 2, h(1e-30) < 1e-27", ok)

# Corollary A5 numerically (definition level)
rho_m, sig_m, A_m = to_mp(rho_e), to_mp(sig_e), to_mp(A)
lhs = (abs_mp(rho_m - sig_m) * A_m)[0, 0] + (abs_mp(rho_m - sig_m) * A_m)[1, 1]
SA2 = (rho_m + sig_m) * A_m * A_m
qv = SA2[0, 0] + SA2[1, 1]
dv = ent_mp((rho_m + sig_m) / 2) - (ent_mp(rho_m) + ent_mp(sig_m)) / 2
yv = mp.mpf(64) / 3125
check("Corollary A5: definition-level delta = h(64/3125) - h(1/2000) (= %s), below 448/3125; "
      "(LHS/RHS)^2 = %s natural, %s base 2"
      % (mp.nstr(dv, 12), mp.nstr(lhs ** 2 / (8 * dv * qv), 12), mp.nstr(lhs ** 2 * mp.log(2) / (8 * dv * qv), 12)),
      abs(dv - (h_mp(yv) - h_mp(mp.mpf(1) / 2000))) < mp.mpf(10) ** (-40)
      and dv < mp.mpf(448) / 3125 and lhs ** 2 > 8 * dv * qv and lhs ** 2 * mp.log(2) > 8 * dv * qv
      and h_mp(yv) / mp.log(2) < mp.mpf(480) / 3125)

# ---------------------------------------------------------------- float64 random tests
rng = np.random.default_rng(20261127)


def rand_state(d, rank=None):
    r = d if rank is None else rank
    G = rng.standard_normal((d, r)) + 1j * rng.standard_normal((d, r))
    R = G @ G.conj().T
    return R / np.trace(R).real


def rand_herm(d):
    G = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    return (G + G.conj().T) / 2


def entropy(R):
    w = np.linalg.eigvalsh(R)
    w = w[w > 1e-300]
    return float(-(w * np.log(w)).sum())


def delta_f(r, s_):
    return entropy((r + s_) / 2) - (entropy(r) + entropy(s_)) / 2


def absm(X):
    w, U = np.linalg.eigh(X)
    return (U * np.abs(w)) @ U.conj().T


# Proposition B: Tr(|D|A)^2 <= 2 Tr(S A^2), self-adjoint A
mx = 0.0
cnt = 0
for d in (2, 3, 4, 5):
    for trial in range(3000):
        rk1 = None if trial % 3 else int(rng.integers(1, d + 1))
        rk2 = None if trial % 2 else int(rng.integers(1, d + 1))
        r, s_ = rand_state(d, rk1), rand_state(d, rk2)
        Dm, Sm = r - s_, r + s_
        A_h = rand_herm(d)
        A_p = A_h @ A_h
        for Am in (A_h, A_p):
            num = np.trace(absm(Dm) @ Am).real ** 2
            den = np.trace(Sm @ Am @ Am).real
            if den > 1e-14:
                mx = max(mx, num / den)
                cnt += 1
check("Proposition B: max of Tr(|D|A)^2 / Tr(S A^2) over %d random (pair, A), d = 2..5: %.6f <= 2" % (cnt, mx),
      mx <= 2 + 1e-9)

# Lemma 0: norm of the functional and its Jordan parts (spot check)
ok = True
for d in (2, 3, 4):
    for trial in range(200):
        Dm = rand_herm(d)
        w, U = np.linalg.eigh(Dm)
        X = (U * np.sign(w)) @ U.conj().T
        ok &= abs(np.trace(Dm @ X).real - np.abs(w).sum()) < 1e-10
        Y = rand_herm(d)
        Y = Y / np.linalg.norm(Y, 2)
        ok &= abs(np.trace(Dm @ Y)) <= np.abs(w).sum() + 1e-10
check("Lemma 0(i): |Tr(D X)| <= Tr|D| for ||X|| <= 1, equality at X = sign(D) (600 random D)", ok)

# Proposition C: commuting states, constant 8 (and 4), general PSD and self-adjoint A
mx8 = 0.0
mx_pt = 0.0
for d in (2, 3, 4, 5):
    for trial in range(3000):
        p = rng.dirichlet(np.ones(d) * rng.choice([0.2, 1.0, 5.0]))
        qv_ = rng.dirichlet(np.ones(d) * rng.choice([0.2, 1.0, 5.0]))
        if trial % 5 == 0:
            p = p.copy()
            p[rng.integers(0, d)] = 0.0
            p = p / p.sum()
        if trial % 7 == 0:
            qv_ = p + 1e-3 * (qv_ - p)
        r, s_ = np.diag(p).astype(complex), np.diag(qv_).astype(complex)
        dl = delta_f(r, s_)
        # delta is a difference of O(1) entropies (absolute float error about 1e-15); the
        # quotient tends to 1/2 as q -> p, so pairs with delta < 1e-6 are skipped: there the
        # relative error of delta exceeds the tolerance (first run: 0.500004 at delta ~ 1e-10).
        if dl < 1e-6:
            continue
        A_h = rand_herm(d)
        for Am in (A_h, A_h @ A_h):
            num = np.trace(absm(r - s_) @ Am).real ** 2
            den = 8 * dl * np.trace((r + s_) @ Am @ Am).real
            mx8 = max(mx8, num / den)
        tot = p + qv_
        mask = tot > 0
        chi = ((p - qv_)[mask] ** 2 / tot[mask]).sum()
        mx_pt = max(mx_pt, chi / (8 * dl))
check("Proposition C: commuting states, max LHS^2 / (8 delta Tr(S A^2)) = %.6f <= 1/2 (constant 4 remark), "
      "max sum (p-q)^2/(p+q) / (8 delta) = %.6f <= 1/2" % (mx8, mx_pt), mx8 <= 0.5 + 1e-6 and mx_pt <= 0.5 + 1e-6)

# two-point inequality (7.1) with the boundary case p = 0
ok = True
for trial in range(20000):
    p_, q_ = rng.random(), rng.random()
    if trial % 10 == 0:
        p_ = 0.0
    a_ = (p_ + q_) / 2
    f = lambda t: 0.0 if t == 0 else t * np.log(t)
    lhs_ = (f(p_) + f(q_)) / 2 - f(a_)
    ok &= lhs_ >= (p_ - q_) ** 2 / (8 * (p_ + q_)) - 1e-13
check("(7.1): (f(p)+f(q))/2 - f((p+q)/2) >= (p-q)^2/(8(p+q)), 20000 random pairs incl. p = 0", ok)

# section 8 (corrected form, proposed, NOT claimed): |Tr(D A)|^2 <= 4 delta Tr(S A^2)
mxc = 0.0
mxq = 0.0
for d in (2, 3, 4):
    for trial in range(3000):
        rk1 = None if trial % 3 else int(rng.integers(1, d + 1))
        r = rand_state(d, rk1)
        s_ = rand_state(d) if trial % 4 else rand_state(d, int(rng.integers(1, d + 1)))
        if trial % 5 == 0:
            s_ = (1 - 0.05) * r + 0.05 * s_
        dl = delta_f(r, s_)
        if dl < 1e-9:
            continue
        Dm, Sm = r - s_, r + s_
        A_h = rand_herm(d)
        num = np.trace(Dm @ A_h).real ** 2
        den = 4 * dl * np.trace(Sm @ A_h @ A_h).real
        mxc = max(mxc, num / den)
        w, U = np.linalg.eigh(Sm)
        keep = w > 1e-10
        Dt = U.conj().T @ Dm @ U
        Q = 0.0
        idx = np.where(keep)[0]
        for i in idx:
            for j in idx:
                a_, b_ = w[i], w[j]
                k = 1 / a_ if abs(a_ - b_) < 1e-9 * max(a_, b_) else (np.log(a_) - np.log(b_)) / (a_ - b_)
                Q += abs(Dt[i, j]) ** 2 * k
        mxq = max(mxq, Q / (4 * dl))
check("section 8 (proposed, not claimed): max |Tr(D A)|^2 / (4 delta Tr(S A^2)) = %.6f, "
      "max Q_BKM(S,D) / (4 delta) = %.6f, both <= 1 over random pairs d = 2..4" % (mxc, mxq),
      mxc <= 1 + 1e-6 and mxq <= 1 + 1e-6)

print()
if FAIL:
    print("RESULT: %d of %d check(s) FAILED: %s" % (len(FAIL), NCHK[0], FAIL))
    sys.exit(1)
print("RESULT: all %d checks passed." % NCHK[0])
print("versions: python %s | mpmath %s | numpy %s" % (sys.version.split()[0], mp.__version__, np.__version__))
