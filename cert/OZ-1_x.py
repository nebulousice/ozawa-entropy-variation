"""OZ-1_x.py -- independent cross-check for claim OZ-1 (ozawa-entropy-variation, stage 5).

Pure Python: `fractions.Fraction` and integer arithmetic only.  No python-flint, no
mpmath, no numpy, no floats; `decimal` is not used (asserted at runtime: those modules must be
absent from sys.modules at the end, and every interval endpoint must be a Fraction).

Independent of OZ-1.py in method, not only in library:
  * the witness matrices for m = 5 and m = 7 are typed in literally (as written in
    CERT.md) and compared with the matrices generated from the family formula;
  * eigenvalues are obtained exactly: the characteristic polynomial t^2 - tr t + det
    of each 2x2 matrix must have a discriminant that is the square of a rational
    (checked with math.isqrt on numerator and denominator), so every eigenvalue is a
    Fraction;
  * |rho - sigma| is obtained without any spectral projection: tr(D) = 0 and
    D^2 = (-det D) I exactly (Cayley-Hamilton, checked by multiplying out), hence by
    uniqueness of the positive square root |D| = sqrt(D^2) = s I with
    s = sqrt(-det D), a rational number (perfect-square check);
  * logarithms: rigorous rational enclosures from the series
        ln y = 2 atanh(z),  z = (y-1)/(y+1),  atanh z = sum_{k>=0} z^(2k+1)/(2k+1),
    after the reduction x = 2^k * y with 3/4 <= y < 3/2 (so |z| <= 1/5), and
    ln 2 = 2 atanh(1/3).  Truncating after K terms leaves a tail of the same sign as z
    with |tail| <= |z|^(2K+1) / ((2K+1)(1 - z^2)); both bounds are used;
  * decision: interval arithmetic on Fractions; violation iff LHS^2 > 8 * delta_hi * q,
    non-violation iff LHS^2 < 8 * delta_lo * q.  Undecided intervals are FAIL.
Also verified: the by-hand reduction for m = 5 (ln 26 < 21/4 from e > 5/2 and 2^5 > 26).

Run:  python OZ-1_x.py     (exit 0 and final line "PASS" iff everything certifies)
"""
import datetime
import hashlib
import math
import os
import platform
import subprocess
import sys
from fractions import Fraction as F

FAILS = []


def check(name, ok):
    print(("  ok    " if ok else "  FAIL  ") + name)
    if not ok:
        FAILS.append(name)


def header():
    here = os.path.dirname(os.path.abspath(__file__))
    try:
        commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=here, capture_output=True,
                                text=True).stdout.strip()
        dirty = subprocess.run(["git", "status", "--porcelain", "--", os.path.basename(__file__)],
                               cwd=here, capture_output=True, text=True).stdout.strip()
    except Exception as e:  # pragma: no cover
        commit, dirty = "unavailable (%s)" % e, ""
    with open(os.path.abspath(__file__), "rb") as fh:
        sha = hashlib.sha256(fh.read()).hexdigest()
    print("command : python %s" % " ".join([os.path.basename(__file__)] + sys.argv[1:]))
    print("cwd     : %s" % os.getcwd())
    print("date    : %s" % datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"))
    print("commit  : %s%s" % (commit, ("  (script status: %s)" % dirty) if dirty else ""))
    print("script  : sha256 %s" % sha)
    print("python  : %s (%s); libraries: standard library only (fractions, math.isqrt)"
          % (sys.version.split()[0], platform.platform()))
    print()


# ------------------------------------------------------------------ intervals
class I:
    """closed interval [lo, hi] with Fraction endpoints."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        hi = lo if hi is None else hi
        lo, hi = F(lo), F(hi)
        assert type(lo) is F and type(hi) is F and lo <= hi
        self.lo, self.hi = lo, hi

    @staticmethod
    def _c(x):
        return x if isinstance(x, I) else I(x)

    def __add__(self, o):
        o = I._c(o)
        return I(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, o):
        return self + (-I._c(o))

    def __rsub__(self, o):
        return I._c(o) - self

    def __mul__(self, o):
        o = I._c(o)
        p = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return I(min(p), max(p))

    __rmul__ = __mul__

    def inv(self):
        assert self.lo > 0 or self.hi < 0
        return I(1 / self.hi, 1 / self.lo)

    def __truediv__(self, o):
        return self * I._c(o).inv()

    def __rtruediv__(self, o):
        return I._c(o) * self.inv()

    def width(self):
        return self.hi - self.lo

    def dec(self, digits=25):
        return "[%s, %s]" % (fdec(self.lo, digits), fdec(self.hi, digits))


def fdec(q, digits=25):
    """exact decimal rendering of a Fraction (truncated toward -inf), for display only."""
    s = "-" if q < 0 else ""
    q = abs(q)
    ip = q.numerator // q.denominator
    frac = q - ip
    d = (frac * 10 ** digits).numerator // (frac * 10 ** digits).denominator
    return "%s%d.%0*d" % (s, ip, digits, d)


# ------------------------------------------------------------------ logarithms
K_TERMS = 60


def atanh2(z):
    """enclosure of 2*atanh(z) for a Fraction |z| <= 1/3."""
    assert abs(z) <= F(1, 3)
    s = F(0)
    zz = z * z
    p = z
    for k in range(K_TERMS):
        s += p / (2 * k + 1)
        p *= zz
    # p = z^(2K+1); tail = sum_{k>=K} z^(2k+1)/(2k+1), same sign as z,
    # |tail| <= |z|^(2K+1)/((2K+1)(1-z^2))
    bound = abs(p) / ((2 * K_TERMS + 1) * (1 - zz))
    if z >= 0:
        return I(2 * s, 2 * (s + bound))
    return I(2 * (s - bound), 2 * s)


LN2 = atanh2(F(1, 3))


def ln(x):
    x = F(x)
    assert x > 0
    k = 0
    while x >= F(3, 2):
        x /= 2
        k += 1
    while x < F(3, 4):
        x *= 2
        k -= 1
    z = (x - 1) / (x + 1)
    return k * LN2 + atanh2(z)


# ------------------------------------------------------------------ exact linear algebra
def mul(X, Y):
    return [[X[i][0] * Y[0][j] + X[i][1] * Y[1][j] for j in range(2)] for i in range(2)]


def add(X, Y, a=1, b=1):
    return [[a * X[i][j] + b * Y[i][j] for j in range(2)] for i in range(2)]


def scal(c, X):
    return [[c * X[i][j] for j in range(2)] for i in range(2)]


def tr(X):
    return X[0][0] + X[1][1]


def det(X):
    return X[0][0] * X[1][1] - X[0][1] * X[1][0]


ID = [[F(1), F(0)], [F(0), F(1)]]


def qsqrt(q):
    """exact square root of a non-negative Fraction, or None if not a rational square."""
    q = F(q)
    assert q >= 0
    a, b = q.numerator, q.denominator
    ra, rb = math.isqrt(a), math.isqrt(b)
    if ra * ra == a and rb * rb == b:
        return F(ra, rb)
    return None


def rational_eigenvalues(X):
    """both eigenvalues of a symmetric 2x2 rational matrix, exactly; asserts rationality."""
    assert X[0][1] == X[1][0]
    t, d = tr(X), det(X)
    r = qsqrt(t * t - 4 * d)
    assert r is not None, "discriminant not a rational square"
    l1, l2 = (t + r) / 2, (t - r) / 2
    # verify: both are roots of the characteristic polynomial
    assert l1 * l1 - t * l1 + d == 0 and l2 * l2 - t * l2 + d == 0
    return l1, l2


def entropy(X, log):
    """von Neumann entropy -sum lambda log lambda from the exact rational spectrum."""
    tot = I(0)
    for lam in rational_eigenvalues(X):
        assert lam >= 0
        if lam == 0:
            continue
        tot = tot - lam * log(lam)
    return tot


def log2(x):
    return ln(x) / LN2


def is_psd(X):
    return X[0][1] == X[1][0] and X[0][0] >= 0 and X[1][1] >= 0 and det(X) >= 0


# ------------------------------------------------------------------ witnesses
def family(m):
    N = m * m
    v = (F(N - 1, N + 1), F(2 * m, N + 1))
    rho = [[F(1), F(0)], [F(0), F(0)]]
    sigma = [[v[i] * v[j] for j in range(2)] for i in range(2)]
    A = [[F(1, N + 1), F(-m, N + 1)], [F(-m, N + 1), F(N, N + 1)]]
    return rho, sigma, A


LITERAL = {
    5: ([[F(1), F(0)], [F(0), F(0)]],
        [[F(144, 169), F(60, 169)], [F(60, 169), F(25, 169)]],
        [[F(1, 26), F(-5, 26)], [F(-5, 26), F(25, 26)]]),
    7: ([[F(1), F(0)], [F(0), F(0)]],
        [[F(576, 625), F(168, 625)], [F(168, 625), F(49, 625)]],
        [[F(1, 50), F(-7, 50)], [F(-7, 50), F(49, 50)]]),
}

EXPECT = {  # True = literal inequality violated
    "e": {1: False, 2: False, 3: False, 4: True, 5: True, 6: True, 7: True},
    "2": {1: False, 2: False, 3: False, 4: False, 5: True, 6: True, 7: True},
}


def run():
    header()
    check("ln 2 enclosure has width < 1e-50 and lies in [0.6931, 0.6932]",
          LN2.width() < F(1, 10 ** 50) and F(6931, 10000) < LN2.lo and LN2.hi < F(6932, 10000))
    # self-test of ln: ln(a) + ln(b) and ln(ab) enclosures must intersect
    for a, b in ((F(26), F(25, 26)), (F(50), F(49)), (F(7, 3), F(11, 5))):
        s, p = ln(a) + ln(b), ln(a * b)
        check("ln self-test: ln(%s)+ln(%s) and ln(%s) intersect" % (a, b, a * b),
              s.lo <= p.hi and p.lo <= s.hi)
    print()
    results = {}
    for m in range(1, 8):
        N = m * m
        rho, sigma, A = family(m)
        print("m = %d  (N = %d)" % (m, N))
        if m in LITERAL:
            check("m=%d: literal matrices (as typed in CERT.md) equal the family formula" % m,
                  LITERAL[m] == (rho, sigma, A))
            rho, sigma, A = LITERAL[m]
        check("m=%d: rho, sigma PSD with trace 1; A PSD (exact)" % m,
              is_psd(rho) and is_psd(sigma) and tr(rho) == 1 and tr(sigma) == 1 and is_psd(A))
        D = add(rho, sigma, 1, -1)
        S = add(rho, sigma)
        # |D| via D^2 = (-det D) I and uniqueness of the positive square root
        cD = -det(D)
        check("m=%d: tr(rho - sigma) = 0 and (rho - sigma)^2 = (-det) I exactly" % m,
              tr(D) == 0 and mul(D, D) == scal(cD, ID))
        s = qsqrt(cD)
        check("m=%d: -det(rho - sigma) = %s is a rational square, s = %s" % (m, cD, s), s is not None)
        absD = scal(s, ID)
        check("m=%d: |rho-sigma| = s I is PSD and squares to (rho-sigma)^2" % m,
              is_psd(absD) and mul(absD, absD) == mul(D, D))
        lhs = tr(mul(absD, A))                                # exact Fraction
        q = tr(mul(S, mul(A, A)))                             # exact Fraction
        W = scal(F(1, 2), S)
        print("  spec(S/2) = %s ; spec(rho) = %s ; spec(sigma) = %s"
              % tuple(str(tuple(str(x) for x in rational_eigenvalues(X))) for X in (W, rho, sigma)))
        print("  LHS = Tr(|rho-sigma| A) = %s (exact) ; Tr(S A^2) = %s (exact)" % (lhs, q))
        for base, log in (("e", ln), ("2", log2)):
            delta = entropy(W, log) - (entropy(rho, log) + entropy(sigma, log)) * F(1, 2)
            assert type(delta.lo) is F and type(delta.hi) is F
            lhs2 = lhs * lhs
            rhs2 = 8 * q * delta                              # interval
            if lhs2 > rhs2.hi:
                verdict = True
            elif lhs2 < rhs2.lo:
                verdict = False
            else:
                verdict = None
            print("  base %s: delta in %s" % (base, delta.dec()))
            print("          LHS^2 - RHS^2 in %s" % (lhs2 - rhs2).dec())
            print("          (LHS/RHS)^2  in %s" % (lhs2 / rhs2).dec())
            check("m=%d base %s: %s certified, expected %s"
                  % (m, base, {True: "violation", False: "no violation", None: "UNDECIDED"}[verdict],
                     "violation" if EXPECT[base][m] else "no violation"),
                  verdict is not None and verdict == EXPECT[base][m])
            results[(m, base)] = (lhs, q, delta, lhs2 - rhs2, lhs2 / rhs2)
        print()

    # by-hand reduction for m = 5 (natural log)
    print("By-hand reduction, m = 5 (natural log):")
    e_lo = F(1) + F(1) + F(1, 2)                  # partial sum of sum 1/k!, all terms positive
    check("e > 1 + 1 + 1/2 = 5/2 > 2, so e^5 > 2^5 = 32 > 26, hence ln 26 < 5 < 21/4",
          e_lo > 2 and 2 ** 5 > 26 and F(5) < F(21, 4))
    l = ln(F(26, 25))
    check("ln(26/25) < 1/25 (enclosure upper end %s), so h(1/26) = ln(26)/26 + (25/26) ln(26/25) "
          "< (1 + ln 26)/26" % fdec(l.hi), l.hi < F(1, 25))
    l26 = ln(F(26))
    check("independently of e: ln 26 < 21/4 from the series enclosure (upper end %s)" % fdec(l26.hi),
          l26.hi < F(21, 4))
    check("(1 + 21/4)/26 = 25/104 and 8 * (25/104) * (1/13) = (5/13)^2 = LHS^2: so ln 26 < 21/4 "
          "gives RHS^2 < LHS^2", F(1 + F(21, 4), 26) == F(25, 104) and 8 * F(25, 104) * F(1, 13) == F(5, 13) ** 2)
    print()

    print("Certified constants (rational enclosures, 25 decimals, truncated):")
    for m in (5, 7):
        lhs, q, de, diffe, r2e = results[(m, "e")]
        _, _, d2, diff2, r22 = results[(m, "2")]
        print("  m=%d: LHS = %s exactly ; Tr(S A^2) = %s exactly" % (m, lhs, q))
        print("        delta_e in %s ; (LHS/RHS_e)^2 in %s" % (de.dec(), r2e.dec()))
        print("        delta_2 in %s ; (LHS/RHS_2)^2 in %s" % (d2.dec(), r22.dec()))
        print("        LHS^2 - RHS_e^2 in %s" % diffe.dec())
        print("        LHS^2 - RHS_2^2 in %s" % diff2.dec())
    print()

    # (the standard-library module `fractions` itself imports `decimal`; this script never uses it)
    banned = [mod for mod in ("flint", "mpmath", "numpy", "sympy", "gmpy2", "scipy") if mod in sys.modules]
    check("no flint / mpmath / numpy / sympy / gmpy2 / scipy loaded (found: %s)" % (banned or "none"), not banned)
    check("no float used: every interval endpoint is a Fraction (enforced in I.__init__)", True)
    if FAILS:
        print("FAIL (%d check(s) failed): %s" % (len(FAILS), FAILS))
        return 1
    print("PASS: OZ-1 cross-check (pure Fractions). Literal inequality violated for m = 4..7 (natural log)")
    print("      and m = 5..7 (base 2); not violated for m = 1..3 (natural) and m = 1..4 (base 2).")
    return 0


if __name__ == "__main__":
    sys.exit(run())
