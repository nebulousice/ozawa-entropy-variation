"""OZ-1.py -- primary certificate for claim OZ-1 (ozawa-entropy-variation, stage 5).

Claim OZ-1: Ozawa's question OWR 22/2018 item (5)(i), read literally,
    |phi - psi|(A) <= ( 8 delta(phi,psi) (phi+psi)(A^2) )^(1/2)   for every A >= 0 ?
has a negative answer.  Here |phi-psi|(A) = Tr(|rho - sigma| A),
(phi+psi)(A^2) = Tr((rho+sigma) A^2), delta = H((rho+sigma)/2) - (H(rho)+H(sigma))/2,
H(rho) = -Tr(rho log rho), natural log (and, separately, log base 2).

Witness family (BRIEF.md L1), m >= 1, N = m^2:
    rho   = [[1,0],[0,0]]
    sigma = v v^T,  v = ((N-1)/(N+1), 2m/(N+1))
    A     = 1/(N+1) * [[1, -m], [-m, N]]          (rank-one projection, A >= 0)

Method (python-flint 0.7.1, Arb ball arithmetic, 256 bits).  Nothing below uses the
closed form in the decision path:
  * exact fmpq checks: rho, sigma, A symmetric; Tr rho = Tr sigma = 1; rho, sigma, A
    positive semidefinite (2x2 symmetric: both diagonal entries >= 0 and det >= 0);
  * each 2x2 symmetric matrix M is diagonalised from its definition: exact trace,
    determinant and discriminant in fmpq; eigenvalues (tr +- sqrt(disc))/2 as Arb
    balls; spectral projections P_+- = (M - lambda_-+ I)/(lambda_+- - lambda_-+) as
    arb_mat;  f(M) = f(lambda_+) P_+ + f(lambda_-) P_-;
  * |rho - sigma| = |lambda_+| P_+ + |lambda_-| P_- (arb_mat), LHS = Tr(|rho-sigma| A);
  * H(M) = sum_i eta(lambda_i), eta(x) = -x log x, with eta(0) = 0 used ONLY when the
    eigenvalue is exactly 0 (decided exactly: det M == 0 in fmpq); every other
    eigenvalue ball must be certified strictly positive before log is taken;
  * decision: the Arb ball of  LHS^2 - 8 * delta * Tr(S A^2)  is certified > 0
    (violation) or < 0 (no violation); same with delta / log 2 for base 2.
  * The expected verdict for every m in 1..7 and both bases is asserted; any ball that
    contains 0, or a verdict different from the expected one, is a FAIL.

The closed form (LHS/RHS)^2 = N / (4((N+1) ln(N+1) - N ln N)) is evaluated afterwards
only as a consistency print (its ball must overlap the definition-level ball).

Run:  python OZ-1.py      (exit 0 and final line "PASS" iff everything certifies)
"""
import datetime
import hashlib
import os
import platform
import subprocess
import sys

import flint
from flint import arb, arb_mat, ctx, fmpq, fmpq_mat

PREC = 256
ctx.prec = PREC
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
    print("python  : %s (%s)" % (sys.version.split()[0], platform.platform()))
    print("flint   : python-flint %s, Arb precision %d bits" % (flint.__version__, PREC))
    print()


# ---------------------------------------------------------------- exact objects
def witness(m):
    N = m * m
    c = fmpq(N - 1, N + 1)
    s = fmpq(2 * m, N + 1)
    rho = fmpq_mat([[1, 0], [0, 0]])
    sigma = fmpq_mat([[c * c, c * s], [c * s, s * s]])
    A = fmpq_mat([[fmpq(1, N + 1), fmpq(-m, N + 1)], [fmpq(-m, N + 1), fmpq(N, N + 1)]])
    return rho, sigma, A


def tr_q(M):
    return M[0, 0] + M[1, 1]


def symmetric(M):
    return M[0, 1] == M[1, 0]


def psd_2x2(M):
    """exact: a symmetric 2x2 rational matrix is PSD iff a >= 0, c >= 0, det >= 0."""
    return symmetric(M) and M[0, 0] >= 0 and M[1, 1] >= 0 and M.det() >= 0


# ---------------------------------------------------------------- spectral layer
class Spectral2:
    """Eigen-decomposition of a symmetric 2x2 fmpq matrix, eigenvalues as Arb balls."""

    def __init__(self, M):
        assert symmetric(M)
        self.M = M
        self.t = tr_q(M)
        self.d = M.det()
        self.disc = self.t * self.t - 4 * self.d          # exact fmpq, >= 0 for symmetric M
        assert self.disc >= 0
        self.scalar = (self.disc == 0)
        r = arb(self.disc).sqrt()
        self.lam_plus = (arb(self.t) + r) / 2
        self.lam_minus = (arb(self.t) - r) / 2
        # exact-zero eigenvalue flags (decided in fmpq, not from balls)
        self.zero_minus = (self.d == 0 and self.t > 0)
        self.zero_plus = (self.d == 0 and self.t < 0)
        if self.d == 0 and self.t == 0:
            self.zero_minus = self.zero_plus = True
        if not self.scalar:
            Ma = arb_mat(M)
            I = arb_mat([[1, 0], [0, 1]])
            gap = self.lam_plus - self.lam_minus
            assert gap > 0
            self.P_plus = (Ma - I * self.lam_minus) * (1 / gap)
            self.P_minus = (Ma - I * self.lam_plus) * (-1 / gap)

    def apply(self, f):
        """f(M) as an arb_mat."""
        I = arb_mat([[1, 0], [0, 1]])
        if self.scalar:
            return I * f(self.lam_plus)
        return self.P_plus * f(self.lam_plus) + self.P_minus * f(self.lam_minus)

    def entropy(self, log):
        tot = arb(0)
        for lam, is_zero in ((self.lam_plus, self.zero_plus), (self.lam_minus, self.zero_minus)):
            if is_zero:
                continue                                  # eta(0) = 0, exact zero eigenvalue
            assert lam > 0, "eigenvalue ball not certified positive"
            tot -= lam * log(lam)
        return tot


def tr_a(M):
    return M[0, 0] + M[1, 1]


def ln(x):
    return x.log()


LN2 = arb(2).log()


def log2(x):
    return x.log() / LN2


# expected verdicts: True = literal inequality violated
EXPECT = {
    "e": {1: False, 2: False, 3: False, 4: True, 5: True, 6: True, 7: True},
    "2": {1: False, 2: False, 3: False, 4: False, 5: True, 6: True, 7: True},
}


def run():
    header()
    print("Witness family: rho = diag(1,0), sigma = v v^T, v = ((N-1)/(N+1), 2m/(N+1)),")
    print("                A = (1/(N+1)) [[1,-m],[-m,N]],  N = m^2")
    print()
    certified = {}
    for m in range(1, 8):
        N = m * m
        rho, sigma, A = witness(m)
        D = rho - sigma
        S = rho + sigma
        print("m = %d  (N = %d)" % (m, N))
        if m in (5, 7):
            print("  sigma = %s" % [[str(sigma[i, j]) for j in range(2)] for i in range(2)])
            print("  A     = %s" % [[str(A[i, j]) for j in range(2)] for i in range(2)])
        check("m=%d: rho, sigma symmetric, trace 1, PSD (exact)" % m,
              tr_q(rho) == 1 and tr_q(sigma) == 1 and psd_2x2(rho) and psd_2x2(sigma))
        check("m=%d: A symmetric PSD (exact; A >= 0 as the question requires)" % m, psd_2x2(A))

        specD = Spectral2(D)
        absD = specD.apply(lambda x: abs(x))
        lhs = tr_a(absD * arb_mat(A))
        q = tr_q(S * A * A)                                  # exact fmpq
        specW = Spectral2(S / 2)
        delta_e = specW.entropy(ln) - (Spectral2(rho).entropy(ln) + Spectral2(sigma).entropy(ln)) / 2
        delta_2 = specW.entropy(log2) - (Spectral2(rho).entropy(log2) + Spectral2(sigma).entropy(log2)) / 2
        print("  LHS = Tr(|rho-sigma| A)       = %s" % lhs.str(25))
        print("  (phi+psi)(A^2) = Tr(S A^2)    = %s  (exact)" % q)
        print("  delta (natural log)           = %s" % delta_e.str(25))
        print("  delta (log base 2)            = %s" % delta_2.str(25))
        for base, delta in (("e", delta_e), ("2", delta_2)):
            diff = lhs * lhs - 8 * delta * arb(q)
            ratio2 = lhs * lhs / (8 * delta * arb(q))
            if diff > 0:
                verdict = True
            elif diff < 0:
                verdict = False
            else:
                verdict = None
            print("  base %s: LHS^2 - RHS^2 = %s ; (LHS/RHS)^2 = %s" % (base, diff.str(20), ratio2.str(20)))
            check("m=%d base %s: sign of LHS^2 - RHS^2 certified (%s), expected %s"
                  % (m, base, {True: "violation", False: "no violation", None: "UNDECIDED"}[verdict],
                     "violation" if EXPECT[base][m] else "no violation"),
                  verdict is not None and verdict == EXPECT[base][m])
            certified[(m, base)] = (lhs, q, delta, diff, ratio2)
            # consistency print with the closed form (not in the decision path)
            Na = arb(N)
            closed = Na / (4 * ((Na + 1) * (Na + 1).log() - Na * Na.log()))
            if base == "2":
                closed = closed * LN2
            check("m=%d base %s: closed form ball overlaps definition-level ball (consistency only)"
                  % (m, base), bool(closed.overlaps(ratio2)))
        print()

    print("Certified constants (Arb balls, radius shown):")
    for m in (5, 7):
        lhs, q, de, diff, r2 = certified[(m, "e")]
        _, _, d2, diff2, r22 = certified[(m, "2")]
        rhs_e = (8 * de * arb(q)).sqrt()
        rhs_2 = (8 * d2 * arb(q)).sqrt()
        print("  m=%d: LHS = %s   (exact value 2m/(N+1) = %s; ball contains it: %s)"
              % (m, lhs.str(30), fmpq(2 * m, m * m + 1), lhs.contains(arb(fmpq(2 * m, m * m + 1)))))
        print("        Tr(S A^2) = %s (exact)" % q)
        print("        delta_e = %s ; RHS_e = %s ; (LHS/RHS_e)^2 = %s" % (de.str(30), rhs_e.str(30), r2.str(30)))
        print("        delta_2 = %s ; RHS_2 = %s ; (LHS/RHS_2)^2 = %s" % (d2.str(30), rhs_2.str(30), r22.str(30)))
        print("        LHS^2 - RHS_e^2 = %s ; LHS^2 - RHS_2^2 = %s" % (diff.str(30), diff2.str(30)))
    print()
    if FAILS:
        print("FAIL (%d check(s) failed): %s" % (len(FAILS), FAILS))
        return 1
    print("PASS: OZ-1 primary certificate (Arb). Literal inequality violated for m = 4..7 (natural log)")
    print("      and m = 5..7 (base 2); not violated for m = 1..3 (natural) and m = 1..4 (base 2).")
    return 0


if __name__ == "__main__":
    sys.exit(run())
