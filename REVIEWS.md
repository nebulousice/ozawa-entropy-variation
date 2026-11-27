# Review history and current status

*As of 2026-11-27.*

## Current status

| Check | Status |
| --- | --- |
| Independent AI review of the hand proofs (two-of-three rule, below) | **Not started.** Round 1 is pending. |
| Final priority check before release | **Not run.** The search of 2026-11-27 ([`LITERATURE_CHECK.md`](LITERATURE_CHECK.md)) must be repeated. |
| Rigorous computation (two independent implementations) | **Passed**, 2026-11-27 ([`cert/OZ-1.out`](cert/OZ-1.out), [`cert/OZ-1_x.out`](cert/OZ-1_x.out)). |
| Lean 4 + Mathlib formalization of the main theorem | **Passed twice**, 2026-11-27 ([`cert/OZ-1_lean.out`](cert/OZ-1_lean.out); [`LEAN.md`](LEAN.md)). |
| Human expert review | **None.** **Expert verification required.** Verified so far with Lean 4 + Mathlib (the main theorem, checked twice), two independent exact computer certificates (Arb interval arithmetic and pure rational arithmetic), and AI referees (Claude models; review in progress). |

So the main theorem (Theorem 5.2: the literal inequality fails, with explicit $2\times 2$ examples) is machine-checked in Lean and certified by computation. Every other result in [`PROOF.md`](PROOF.md) rests on its hand proof alone, and no hand proof has yet been reviewed.

## The review rule

The project's rule for calling a hand proof "proved":
1. **Round 1.** Two AI referees on different models review the same commit, blind to each other and to the working notes. If both accept with zero issues, the proof passes.
2. **Otherwise** every issue is fixed or rebutted in a new commit. Then three referees (the two above and a third, fresh, on a third model) review that commit. The proof passes if at least two of the three accept with zero issues and no reviewer has an unresolved major issue.
3. A major issue from any reviewer always blocks. After a fixed number of rounds without a pass, the matter goes to the repository owner.

A formalized step counts as verified, but it never replaces the review vote on the whole proof.

## Rounds

None yet. This section will record, for each round: the commit reviewed, each referee's model, the verdict, every issue raised, and how it was fixed or rebutted.

## Checks so far (these are not reviews)

| Date | Check | Result |
| --- | --- | --- |
| 2026-11-27 | Priority search | No published answer, claim or active work found; some sources not completed ([`LITERATURE_CHECK.md`](LITERATURE_CHECK.md)). |
| 2026-11-27 | Primary certificate, Arb ball arithmetic at 256 bits (python-flint 0.7.1) | PASS: violation for $m=4,\dots,7$ (natural log) and $m=5,6,7$ (base 2); none for smaller $m$. |
| 2026-11-27 | Independent cross-check, exact fractions only | PASS; all 14 verdicts agree with the primary certificate. |
| 2026-11-27 | Lean, first version (identities over the rationals and the four scalar inequalities) | PASS. |
| 2026-11-27 | Lean, full version (every quantity defined from the matrices; the negative answer as a universal statement) | PASS in the run that produced it (build log in [`lean/Pipeline/Ozawa/build.log`](lean/Pipeline/Ozawa/build.log)). |
| 2026-11-27 | Lean, independent rerun of the full version | PASS: build succeeded, no `sorry`, all 28 axiom reports standard ([`cert/OZ-1_lean.out`](cert/OZ-1_lean.out)). |
| 2026-11-27 | Sanity script [`prover/check_proof.py`](prover/check_proof.py): smallest cases and exact identities | All 42 checks pass ([`prover/out/check_proof.log`](prover/out/check_proof.log)). |
| 2026-11-27 | Write-up self-check: the paper reread as a skeptical outside referee | Points found and fixed in the write-up are listed below. |

## Points found while writing up

These were found in the first draft of this write-up and fixed before it was saved. None affects a mathematical claim.
1. The introduction of [`paper.tex`](paper.tex) first said that no statement in the paper uses a computation. Remark 5.4 (the first violating integer in the family) does combine a hand argument with certified signs. The text now says so.
2. The proof of Theorem 5.2 now states explicitly why $A_m\ge0$ (it is an orthogonal projection).
3. The proof that $\delta_\varepsilon>0$ in Corollary 6.5 now cites the monotonicity of $h$ explicitly.
4. Lemma 2.1, step (c), now says why $B$ is hermitian: $\langle\xi,B\xi\rangle\ge0$ for all complex vectors $\xi$ forces it.
5. Corollary 6.4(i) in the paper now says explicitly that both sides are nonnegative before square roots are taken.
6. The original certificate description said that each quoted constant "lies in the rational interval" of the cross-check output. The four values of $\delta$ are quoted to 26 decimals, but the cross-check prints only 25. The write-up now says what was checked: each constant is a truncation of the ball printed by the primary certificate, and agrees with the cross-check's printed interval to all 25 decimals it prints.

Open points for the referees to check with particular care:
- **Lemma 2.1** carries the whole interpretation: that the printed $\lvert\varphi-\psi\rvert(A)$ means $\mathrm{Tr}(\lvert\rho-\sigma\rvert A)$. The Lean formalization takes this as a definition and does not check it.
- **Remark 7.4** (which reading Ozawa intended) is evidence only. If the intended reading was $\lvert(\varphi-\psi)(A)\rvert$, the main theorem does not address it.
- The citation of Topsøe (2000) is from secondary sources; the paper was not read.

## Ledger row (verbatim)

The project's claims ledger holds one row for this result. It is copied here verbatim, internal labels included, for traceability.

| ID | Claim | Status | Evidence | Reviews | Date |
| --- | --- | --- | --- | --- | --- |
| OZ-1 | Ozawa's OWR 2018/22 question (5)(i), read literally, has a negative answer: for the qubit pure-state family (LHS/RHS)² = (1−x)/(4h(x)) with x = sin²(θ/2), unbounded as θ → 0; exact rational witness from the Pythagorean family (first violation m = 4) | formalized: Ozawa's question (literal reading) is false — Lean theorems ozawa_question_literal_false (+ _bits, _rpow) in lean/Pipeline/Ozawa/Witness.lean, all quantities via Mathlib CFC, lean_check PASS (formaliser and independent orchestrator rerun, 2026-11-27), dimension 2, real parts of traces; also certified for m = 5, 7, both log bases (Arb + independent pure-Fraction); hand proof in PROOF.md (proposed, review pending) | `targets/ozawa-entropy-variation/BRIEF.md`, `scripts/rows.py`, `targets/ozawa-entropy-variation/cert/CERT.md`, `lean/Pipeline/Ozawa/Main.lean` | none | 2026-11-27 |

The evidence paths in that row refer to the original private pipeline repository. In this repository the corresponding files are [`PROOF.md`](PROOF.md), [`cert/`](cert/) and [`lean/Pipeline/Ozawa/`](lean/Pipeline/Ozawa/).

**Not yet in the ledger.** The row above covers the negative answer, the closed form on the family, its unboundedness, and the first violation. The following results of [`PROOF.md`](PROOF.md) are stated here with status "proposed" but have no ledger row of their own yet: Theorem 6.2 (no function of $\delta$), Proposition 6.3 and Corollary 6.4 (the bound 2 and the threshold $1/4$), Corollary 6.5 (faithful states, all dimensions), and Proposition 7.2 (commuting states).
