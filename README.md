# Ozawa's entropy–variation question, read literally, has a negative answer

> **In one line:** at Oberwolfach in 2018, Narutaka Ozawa asked whether $`\lvert\varphi-\psi\rvert(A)\le(8\delta(\varphi,\psi)(\varphi+\psi)(A^2))^{1/2}`$ for all quantum states $`\varphi,\psi`$ and all $`A\ge 0`$, where $`\delta`$ is the quantum Jensen–Shannon divergence. Read literally, the answer is no. An explicit pair of pure qubit states with rational entries violates the bound, with the natural logarithm and with base 2. The violation is proved by hand, confirmed by two independent rigorous computations, and formalized in Lean 4 with Mathlib. The hand proofs have not yet been independently reviewed.

## Summary

**Theorem.** Let

```math
\rho=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
\sigma=\frac{1}{169}\begin{pmatrix}144&60\\60&25\end{pmatrix},\qquad
A=\frac{1}{26}\begin{pmatrix}1&-5\\-5&25\end{pmatrix}.
```

Then $`\rho`$ and $`\sigma`$ are density matrices of pure states on $`M_2(\mathbb{C})`$, $A$ is positive semidefinite, and

```math
\mathrm{Tr}\bigl(|\rho-\sigma|A\bigr)=\frac{5}{13},\qquad \mathrm{Tr}\bigl((\rho+\sigma)A^2\bigr)=\frac{1}{13},\qquad \delta(\rho,\sigma)=h\Bigl(\frac{1}{26}\Bigr),
```

```math
\mathrm{Tr}\bigl(|\rho-\sigma|A\bigr)\ >\ \Bigl(8\,\delta(\rho,\sigma)\,\mathrm{Tr}\bigl((\rho+\sigma)A^2\bigr)\Bigr)^{1/2},
```

both with the natural logarithm and with base 2. Here $h$ is the binary entropy and $`\delta`$ is Ozawa's quantity (both defined under Setup and Notation below). A second rational example, the case $m=7$ of the family under Notation, is also in Theorem 5.2. So the answer to question (5)(i) of [Oberwolfach Report 22/2018](https://doi.org/10.4171/OWR/2018/22) (Ozawa, p. 1373), read literally, is **no**. This is Theorem 5.2 of [`PROOF.md`](PROOF.md) and [`paper.tex`](paper.tex).

Further results, all proved by hand in [`PROOF.md`](PROOF.md) and not yet reviewed:
- **No constant works.** On a one-parameter family of pure qubit states the ratio of the two sides is unbounded (Theorem 6.1).
- **No function of $`\delta`$ works.** With the test matrix $`A=(\rho+\sigma)^{-1}`$ on the same family, the squared left side is exactly twice $`\mathrm{Tr}((\rho+\sigma)A^2)`$, at every value of $`\delta`$ in $`(0,\ln 2]`$ (Theorem 6.2). The factor 2 is optimal in all dimensions (Proposition 6.3).
- **Exact threshold.** The literal inequality holds whenever $`\delta\ge 1/4`$, and fails for some pure qubit pair at every value $`\delta\lt 1/4`$ (Corollary 6.4).
- **Variants.** The failure persists for faithful (full-rank) states and in every dimension $`d\ge 2`$ (Corollary 6.5).
- **Commuting states.** For commuting states the literal inequality is true (Proposition 7.2).

**Priority.**
- The question is Narutaka Ozawa's: Oberwolfach Report 22/2018, "Open Problems", item (5)(i), p. 1373.
- The counterexample family (the qubit pure states $`\lvert 0\rangle`$ and $`\lvert\theta\rangle`$, with $A$ an eigenprojection of $`\rho+\sigma`$) was first pointed out in an **unpublished external vetting report** supplied to this project on 2026-11-27. This repository re-derives it, chooses rational examples, writes complete proofs, and verifies them by computer and in Lean.
- A priority search on 2026-11-27 found no published answer to this question, no claim, and no active work on it ([`LITERATURE_CHECK.md`](LITERATURE_CHECK.md)). Some sources could not be completed in that search. To our knowledge as of that search, the negative answer appears in no public source. The search must be repeated before any release.
- The commuting case is not new in substance. It follows from the commutative argument of Ozawa's own paper ([arXiv:2009.00837](https://arxiv.org/abs/2009.00837)) and the Cauchy–Schwarz inequality; Topsøe's inequality ([doi:10.1109/18.850703](https://doi.org/10.1109/18.850703)) even gives the constant 4.
- **No novelty or priority is claimed.** Credit lines have not yet been drafted or approved.

**Method.**
1. *Literal reading.* For states with density matrices $`\rho,\sigma`$, the absolute value of the functional $`\varphi-\psi`$ is $`X\mapsto\mathrm{Tr}(\lvert\rho-\sigma\rvert X)`$ (Lemma 2.1).
2. *A family with closed forms.* For two pure qubit states at angle $`\theta`$, $`\lvert\rho-\sigma\rvert`$ is a multiple of the identity. Take $A$ to be the eigenprojection of $`\rho+\sigma`$ for its small eigenvalue. A rational parametrisation by $`m=\cot(\theta/2)`$ makes every quantity explicit (Proposition 4.2).
3. *Explicit examples.* At $m=5$ and $m=7$ the violation reduces to four elementary logarithm inequalities, proved by hand (Lemma 5.1, Theorem 5.2).
4. *Robustness.* The test matrix $`(\rho+\sigma)^{-1}`$ gives the quotient 2 at every $`\delta`$, and a Cauchy–Schwarz argument shows 2 is the largest possible value (Theorem 6.2, Proposition 6.3).
5. *Commuting case.* A two-point Taylor bound for $`t\ln t`$ and the Cauchy–Schwarz inequality (Lemma 7.1, Proposition 7.2).
6. *Checks.* Two independent rigorous programs decide the sign of the violation for $`m=1,\dots,7`$ in both bases. Lean 4 checks the examples and the negative answer with every quantity defined from the matrices.

**Side facts** (proved by hand, not yet reviewed, unless marked):
- On the family, the squared ratio of the two sides is $(1-x)/(4h(x))$ with $`x=\sin^2(\theta/2)`$. It is unbounded as $`\theta\to 0`$.
- The first violating integer in the family is $m=4$ with the natural logarithm and $m=5$ in base 2. This combines a hand monotonicity argument with the certified signs.
- Over all states and all hermitian $A$, the squared left side is at most twice $`\mathrm{Tr}((\rho+\sigma)A^2)`$; this is attained on the family.

**Verification.**
- *Certificates.* Two independent programs compute both sides from the definitions for $`m=1,\dots,7`$, in both logarithm bases. One uses Arb ball arithmetic at 256 bits (python-flint 0.7.1); the other uses only exact Python fractions with its own rigorous logarithm enclosures. Both passed on 2026-11-27, and all 14 verdicts agree ([`cert/OZ-1.out`](cert/OZ-1.out), [`cert/OZ-1_x.out`](cert/OZ-1_x.out)).
- *Lean.* The theorem `ozawa_question_literal_false` (with variants `_bits` for base 2 and `_rpow`) states that the literal inequality, for all $`2\times 2`$ complex density matrices and all positive semidefinite $A$, is false. The four theorems `ozawa_literal_fails_m5`, `_m5_bits`, `_m7`, `_m7_bits` state the examples. The check (build passes, no `sorry`, only the standard axioms `propext`, `Classical.choice`, `Quot.sound`) passed twice on 2026-11-27 ([`cert/OZ-1_lean.out`](cert/OZ-1_lean.out)). Two stated deviations: dimension 2, and real parts of traces ([`LEAN.md`](LEAN.md)).
- *Reviews.* The hand proofs have **not** yet been through the project's two-of-three independent AI review; review round 1 is pending. The final priority check has not been re-run ([`REVIEWS.md`](REVIEWS.md)).
- **Expert verification required.** Verified so far with Lean 4 + Mathlib (the main theorem, checked twice), two independent exact computer certificates (Arb interval arithmetic and pure rational arithmetic), and AI referees (Claude models; review in progress) **Expert verification required.** Verified so far with Lean 4 + Mathlib (the main theorem, checked twice), two independent exact computer certificates (Arb interval arithmetic and pure rational arithmetic), and AI referees (Claude models; review in progress)

Status, copied from the project ledger (2026-11-27; agent names replaced by neutral descriptions):

| Claim | Status | Evidence |
| --- | --- | --- |
| Ozawa's OWR 2018/22 question (5)(i), read literally, has a negative answer: for the qubit pure-state family (LHS/RHS)² = (1−x)/(4h(x)) with x = sin²(θ/2), unbounded as θ → 0; exact rational witness from the Pythagorean family (first violation m = 4) | formalized: Ozawa's question (literal reading) is false — Lean theorems `ozawa_question_literal_false` (+ `_bits`, `_rpow`) in `lean/Pipeline/Ozawa/Witness.lean`, all quantities via Mathlib CFC, lean_check PASS (formalization run and independent rerun, 2026-11-27), dimension 2, real parts of traces; also certified for m = 5, 7, both log bases (Arb + independent pure-Fraction); hand proof in PROOF.md (proposed, review pending) | [`PROOF.md`](PROOF.md), [`cert/`](cert/), [`lean/Pipeline/Ozawa/Witness.lean`](lean/Pipeline/Ozawa/Witness.lean) |

**How it was made.** An autonomous research pipeline of AI agents (Anthropic's Claude models in separate roles: priority search, planning, proof writing, certification, formalization and write-up), run in a private repository on 2026-11-27 and directed by the repository owner. The starting observation came from the external vetting report mentioned above. Nothing has been posted or published.

## Where to start

| If you want… | Read |
| --- | --- |
| The theorem and every proof | [`PROOF.md`](PROOF.md) (Markdown) or [`paper.tex`](paper.tex) (LaTeX, same numbering) |
| To rerun the certificates | `pip install python-flint==0.7.1`, then `python cert/OZ-1.py` and `python cert/OZ-1_x.py` ([`REPRODUCE.md`](REPRODUCE.md)) |
| To rebuild the Lean proof | [`LEAN.md`](LEAN.md) and [`REPRODUCE.md`](REPRODUCE.md) |
| Priority and related work | [`LITERATURE_CHECK.md`](LITERATURE_CHECK.md) |
| What has and has not been reviewed | [`REVIEWS.md`](REVIEWS.md) |

---

## Research log

### Setup

The question, verbatim from the source ([doi:10.4171/OWR/2018/22](https://doi.org/10.4171/OWR/2018/22), p. 1373):

> (5) Narutaka Ozawa:
> (i) Let $`H(\varphi)`$ denote the von Neumann entropy of $`\varphi`$ and
>
> ```math
> \delta(\varphi,\psi)=H\bigl((\varphi+\psi)/2\bigr)-\bigl(H(\varphi)+H(\psi)\bigr)/2 .
> ```
>
> Is it true that $`\lvert\varphi-\psi\rvert(A)\le\bigl(8\delta(\varphi,\psi)(\varphi+\psi)(A^2)\bigr)^{1/2}`$ for every $`A\ge 0`$?

Terms used:
- A *density matrix* is a positive semidefinite complex matrix with trace 1. A *state* $`\varphi`$ is the functional $`X\mapsto\mathrm{Tr}(\rho X)`$ for a density matrix $`\rho`$. Below, $`\varphi,\psi`$ have density matrices $`\rho,\sigma`$, so $`(\varphi+\psi)(A^2)=\mathrm{Tr}((\rho+\sigma)A^2)`$.
- A state is *pure* if its density matrix is a rank-one orthogonal projection, and *faithful* if its density matrix is invertible.
- The *von Neumann entropy* of a density matrix with eigenvalues $`\lambda_j`$ is $`H=-\sum_j\lambda_j\ln\lambda_j`$, with $`0\ln 0=0`$. Ozawa's $`\delta`$ is the *quantum Jensen–Shannon divergence*. The source does not fix the logarithm base; we treat the natural logarithm and base 2.
- For a hermitian matrix $D$ with eigenvalues $`\lambda_j`$ and spectral projections $`P_j`$, $`\lvert D\rvert=\sum_j\lvert\lambda_j\rvert P_j`$. The *literal reading* takes $`\lvert\varphi-\psi\rvert`$ to be the absolute value of the functional $`\varphi-\psi`$, which is $`X\mapsto\mathrm{Tr}(\lvert\rho-\sigma\rvert X)`$. So the question asks whether, for every positive semidefinite $A$,

```math
\mathrm{Tr}\bigl(|\rho-\sigma|A\bigr)\le\Bigl(8\,\delta(\rho,\sigma)\,\mathrm{Tr}\bigl((\rho+\sigma)A^2\bigr)\Bigr)^{1/2}.
```

- LHS and RHS denote the left and right sides of this inequality.
- *CFC* is Mathlib's continuous functional calculus, which defines functions of matrices such as $`\lvert X\rvert`$ and $`\log X`$.

This repository does not address the other possible reading, with $`\lvert(\varphi-\psi)(A)\rvert`$ on the left, and makes no claim about it.

### Notation

Binary entropy:

```math
h(x)=-x\ln x-(1-x)\ln(1-x),\qquad 0<x<1 .
```

The family of pure qubit states, for real $m>0$ and $N=m^2$:

```math
\rho=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
\sigma_m=vv^{T},\quad v=\Bigl(\frac{N-1}{N+1},\frac{2m}{N+1}\Bigr),\qquad
A_m=\frac{1}{N+1}\begin{pmatrix}1&-m\\-m&N\end{pmatrix}.
```

Here $`\sigma_m`$ is the projection onto $`(\cos\theta,\sin\theta)`$ with $`m=\cot(\theta/2)`$, and $`1/(N+1)=\sin^2(\theta/2)`$. For integer $m$ the vector $v$ comes from the Pythagorean triple $(N-1,2m,N+1)$, so all entries are rational; this is the "Pythagorean family" of the ledger row. The two examples are $m=5$ (triple 12, 5, 13) and $m=7$ (triple 24, 7, 25). On the family:

```math
\mathrm{Tr}\bigl(|\rho-\sigma_m|A_m\bigr)=\frac{2m}{N+1},\qquad
\mathrm{Tr}\bigl((\rho+\sigma_m)A_m^2\bigr)=\frac{2}{N+1},\qquad
\delta(\rho,\sigma_m)=h\Bigl(\frac{1}{N+1}\Bigr).
```

### Results along the way

Status words: **proposed** = complete hand proof, not yet reviewed; **certified** = rigorous computation in two independent implementations that agree, output archived; **formalized** = checked in Lean 4 with Mathlib (build passes, no `sorry`, standard axioms only); **numerical** = floating-point evidence only; **heuristic** = plausible, not proved.

| # | Statement | Status | Evidence |
| --- | --- | --- | --- |
| 1 | The question as printed (verbatim, p. 1373) and its literal meaning: the absolute value of the functional is $`\mathrm{Tr}(\lvert\rho-\sigma\rvert\cdot)`$ | proposed (Lemma 2.1) | [`PROOF.md`](PROOF.md) §§1–2 |
| 2 | Closed form on the family: squared ratio $(1-x)/(4h(x))$, $x=1/(m^2+1)$ | proposed | [`PROOF.md`](PROOF.md) Proposition 4.2 |
| 3 | $m=5$ and $m=7$ violate the literal inequality, natural log and base 2 | proposed; **certified**; **formalized** | [`PROOF.md`](PROOF.md) Theorem 5.2; [`cert/`](cert/); `ozawa_literal_fails_m5`, `_m5_bits`, `_m7`, `_m7_bits` |
| 4 | **The literal inequality is false** (universal statement over $`2\times 2`$ complex density matrices and $`A\ge 0`$) | **formalized** (dimension 2, real parts of traces); proposed by hand | `ozawa_question_literal_false`, `_bits`, `_rpow` in [`Witness.lean`](lean/Pipeline/Ozawa/Witness.lean) |
| 5 | Sign of the violation for $`m=1,\dots,7`$: violated for $`m=4,\dots,7`$ (natural log) and $m=5,6,7$ (base 2), not for smaller $m$ | **certified** | [`cert/OZ-1.out`](cert/OZ-1.out), [`cert/OZ-1_x.out`](cert/OZ-1_x.out) |
| 6 | First violating integer: $m=4$ (natural log), $m=5$ (base 2) | proposed (monotonicity) + certified (signs) | [`PROOF.md`](PROOF.md) Remark 5.4 |
| 7 | No constant in place of 8 works; ratio unbounded on the family | proposed | [`PROOF.md`](PROOF.md) Theorem 6.1 |
| 8 | No function of $`\delta`$ works: quotient exactly 2 at $`A=(\rho+\sigma)^{-1}`$, at every $`\delta\in(0,\ln 2]`$ | proposed | [`PROOF.md`](PROOF.md) Theorem 6.2 |
| 9 | Quotient at most 2 in all dimensions; hence the literal inequality holds whenever $`\delta\ge 1/4`$, and fails for some pure qubit pair at every $`\delta\lt 1/4`$ | proposed | [`PROOF.md`](PROOF.md) Proposition 6.3, Corollary 6.4 |
| 10 | Faithful states ($`\varepsilon=1/1000`$); every dimension $`d\ge 2`$ | proposed | [`PROOF.md`](PROOF.md) Corollary 6.5 |
| 11 | Commuting states: the literal inequality holds (constant 8) | proposed; follows from published arguments | [`PROOF.md`](PROOF.md) Proposition 7.2 |
| 12 | The literal reading is the intended one | heuristic (evidence only, no claim) | [`PROOF.md`](PROOF.md) Remark 7.4 |

### Timeline

1. **6–12 May 2018:** Oberwolfach workshop; Ozawa's question recorded in the open-problems list of the report.
2. **2 Sep 2020:** Ozawa's paper [arXiv:2009.00837](https://arxiv.org/abs/2009.00837), whose commutative argument matches the shape and constant of the question.
3. **31 Aug 2026:** the question appears in the MathDB catalogue as entry [401593](https://mathdb.com/p/401593), status open.
4. **27 Nov 2026:**
   - an external vetting report, supplied to the project, points out the qubit counterexample family;
   - priority search: no published answer, claim or active work found;
   - rational examples $m=5,7$ chosen; both certificates pass;
   - complete hand proofs written;
   - Lean formalization of the examples and of the negative answer; the check passes, and an independent rerun passes;
   - this write-up.

## Files

| Path | Contents |
| --- | --- |
| [`PROOF.md`](PROOF.md) | **The complete proof**, self-contained, every step with its status word |
| [`paper.tex`](paper.tex) | The same results as an `amsart` paper (no PDF: no TeX engine was available; see [`REPRODUCE.md`](REPRODUCE.md)) |
| [`LITERATURE_CHECK.md`](LITERATURE_CHECK.md) | Priority search (2026-11-27) and comparison with prior and related work |
| [`REVIEWS.md`](REVIEWS.md) | Review history and current review status |
| [`LEAN.md`](LEAN.md) | What is formalized in Lean, what is not, and why |
| [`REPRODUCE.md`](REPRODUCE.md) | Exact commands, versions, runtimes and expected output |
| [`cert/OZ-1.py`](cert/OZ-1.py), [`cert/OZ-1.out`](cert/OZ-1.out) | Primary certificate (Arb ball arithmetic) and its archived output |
| [`cert/OZ-1_x.py`](cert/OZ-1_x.py), [`cert/OZ-1_x.out`](cert/OZ-1_x.out) | Independent cross-check (exact fractions only) and its archived output |
| [`cert/OZ-1_lean.out`](cert/OZ-1_lean.out) | Archived output of the Lean check (independent rerun, 2026-11-27) |
| [`cert/run_cert.sh`](cert/run_cert.sh) | The runner that produced the two archived certificate outputs in the original repository (kept for the record; see [`REPRODUCE.md`](REPRODUCE.md)) |
| [`lean/`](lean/) | Standalone Lean project: `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, root module `Pipeline.lean`, and the five files in `lean/Pipeline/Ozawa/` with their build and axiom logs |
| [`scripts/lean_check.sh`](scripts/lean_check.sh) | The Lean check: build, `sorry` scan, axiom check |
| [`prover/check_proof.py`](prover/check_proof.py), [`prover/out/check_proof.log`](prover/out/check_proof.log) | Sanity checks of every lemma at its smallest cases (not a certificate) and their output |

## Credits

- The question: Narutaka Ozawa (Oberwolfach Report 22/2018).
- The counterexample family: first pointed out in an unpublished external vetting report supplied to the project on 2026-11-27.
- Proofs, certificates, Lean formalization and write-up: Claude models (Anthropic) in an autonomous research pipeline, directed by the repository owner.
- Final credit lines are pending the repository owner's approval.
