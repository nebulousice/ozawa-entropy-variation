# Lean 4 formalization

*As of 2026-11-27.*

## Summary

- **Formalized:** the main theorem. For the two explicit $2\times 2$ examples ($m=5$ and $m=7$) and both logarithm bases, the states are density matrices, $A$ is positive semidefinite, and the literal inequality fails strictly. Also formalized: the negative answer as a universally quantified statement ("for all $2\times 2$ complex density matrices $\rho,\sigma$ and all positive semidefinite $A$, the inequality holds" is false). Every quantity is defined from the matrices; no value is supplied by hand.
- **Toolchain:** Lean `leanprover/lean4:v4.37.0-rc1`, Mathlib commit `8ec7bd8e5f837ab7e335374928e18341c4e9f385` (pinned in [`lean/lake-manifest.json`](lean/lake-manifest.json)).
- **Check:** [`scripts/lean_check.sh`](scripts/lean_check.sh) `Ozawa`. It passes only if (1) `lake build` succeeds, (2) the files contain no `sorry` or `admit`, and (3) every `#print axioms` line of `Main.lean` reports only `propext`, `Classical.choice` and `Quot.sound`.
- **Result:** PASS twice on 2026-11-27: in the run that produced the full version, and in an independent rerun ([`cert/OZ-1_lean.out`](cert/OZ-1_lean.out)). No `native_decide` is used anywhere.
- **Not formalized:** everything in [`PROOF.md`](PROOF.md) beyond the main theorem and its ingredients (list below).

## Files

All in [`lean/Pipeline/Ozawa/`](lean/Pipeline/Ozawa/). They are byte-identical copies of the files that passed the check.

| File | Lines | Contents |
| --- | --- | --- |
| [`Rational.lean`](lean/Pipeline/Ozawa/Rational.lean) | 114 | First version: exact identities over $\mathbb{Q}$ for both examples (projections, traces, $(\rho-\sigma)^2=s^2I$, the spectral form of the midpoint). Not used by the final theorems, which re-prove the identities over $\mathbb{C}$. |
| [`Scalar.lean`](lean/Pipeline/Ozawa/Scalar.lean) | 108 | First version: the four scalar inequalities of Lemma 5.1, with Mathlib's `Real.log` and `Real.binEntropy`. |
| [`Spectral.lean`](lean/Pipeline/Ozawa/Spectral.lean) | 96 | General lemmas about the continuous functional calculus, valid in any algebra with a real continuous functional calculus for self-adjoint elements. |
| [`Witness.lean`](lean/Pipeline/Ozawa/Witness.lean) | 339 | Definitions of entropy and $\delta$, the complex examples, the absolute values and entropies of the examples, and the final theorems. |
| [`Main.lean`](lean/Pipeline/Ozawa/Main.lean) | 61 | Imports the four files and ends with 28 `#print axioms` lines (lines 34–61). |
| [`build.log`](lean/Pipeline/Ozawa/build.log), [`axioms.log`](lean/Pipeline/Ozawa/axioms.log) | | Logs of the independent rerun. The build log covers the whole shared project of the original repository, so it also mentions files of other projects. |

The standalone project in [`lean/`](lean/) adds a root module [`lean/Pipeline.lean`](lean/Pipeline.lean) that imports only `Pipeline.Ozawa.Main`. Build instructions are in [`REPRODUCE.md`](REPRODUCE.md).

## Definitions (`Witness.lean`, lines 31–44)

With `open scoped MatrixOrder ComplexOrder`:
- `vnEntropy X = (-(X * cfc Real.log X).trace).re`: the von Neumann entropy $H(X)=-\mathrm{Tr}(X\log X)$, natural logarithm. The matrix logarithm `cfc Real.log X` is the body of Mathlib's `CFC.log`, which is declared only for normed rings. Mathlib's convention `Real.log 0 = 0` gives $0\log 0=0$.
- `vnEntropy₂`: the same with `Real.logb 2`.
- `ozawaDelta ρ σ = vnEntropy ((1/2 : ℝ) • (ρ + σ)) - (vnEntropy ρ + vnEntropy σ) / 2`, and `ozawaDelta₂` in base 2. This is $\delta$ exactly as in the source.
- $\lvert\varphi-\psi\rvert(A)$ is `(CFC.abs (ρ - σ) * A).trace.re`. Mathlib's `CFC.abs X` is `CFC.sqrt (star X * X)`; for hermitian $X$ it is the positive semidefinite square root of $X^2$, the matrix $\lvert X\rvert$ of [`PROOF.md`](PROOF.md) §2.1.
- $(\varphi+\psi)(A^2)$ is `((ρ + σ) * A ^ 2).trace.re`. The power $1/2$ is `Real.sqrt` (and `Real.rpow` in the `_rpow` variant).
- A state is a `Matrix (Fin 2) (Fin 2) ℂ` with `PosSemidef` and `trace = 1`; $A\ge 0$ is `A.PosSemidef`.

## Theorems

Line numbers refer to the files in this repository.

**General lemmas** (`Spectral.lean`):
- `spectrum_twoProj_subset` (line 34): for a self-adjoint idempotent $P$, the spectrum of $aP+b(1-P)$ lies in $\lbrace a,b\rbrace$.
- `cfc_twoProj` (line 55): if moreover $a\ne b$, then `cfc f (a • P + b • (1 - P)) = f a • P + f b • (1 - P)` for every $f:\mathbb{R}\to\mathbb{R}$. This gives Lemma 3.2(b) for $x\ne 1/2$.
- `cfc_norm_of_mul_self` (line 81): if $D$ is self-adjoint, $D\cdot D=s^2\cdot 1$ and $s\ge 0$, then `cfc (‖·‖) D = s • 1`. This is Lemma 3.1.

**The two examples** (`Witness.lean`):
- Absolute values: `abs5C` (line 143), `CFC.abs (rhoC - sig5C) = (5/13) • 1`; `abs7C` (line 248), with $7/25$.
- Entropy gaps: `delta5C` (line 158), `ozawaDelta rhoC sig5C = Real.binEntropy (1/26)`; `delta5C₂` (line 169), the same divided by `Real.log 2`; `delta7C` (line 261) and `delta7C₂` (line 272) with $1/50$.
- Values: `lhs5C` (line 148) and `q5C` (line 153) show that the complex traces equal $5/13$ and $1/13$; `lhs7C` (line 252) and `q7C` (line 256) give $7/25$ and $1/25$.
- Supporting lemmas: `negTrace_twoProj` (line 57), `negTrace_proj` (line 70, pure states have entropy 0), `psd_of_proj` (line 79), `W5C_two` (line 132), `D5C_sq` (line 137), `W7C_two` (line 237), `D7C_sq` (line 242).

**Scalar inequalities** (`Scalar.lean`; Lemma 5.1):
- `ozawa_m5_nat` (line 74): `8 * binEntropy (1/26) * (1/13) < (5/13)^2`.
- `ozawa_m5_base2` (line 80): `8 * (binEntropy (1/26) / log 2) * (1/13) < (5/13)^2`.
- `ozawa_m7_nat` (line 91) and `ozawa_m7_base2` (line 98): the same with $1/50$, $1/25$ and $7/25$.
- Helpers: `log_26_lt` (line 38), `log_26_le_log2` (line 48), `log_50_le_log2` (line 55). The proofs use only `log x ≤ x − 1`, `x + 1 ≤ exp x` and Mathlib's bounds on `log 2`.

**Final theorems** (`Witness.lean`):
- `ozawa_literal_fails_m5` (line 182), `ozawa_literal_fails_m5_bits` (line 193), `ozawa_literal_fails_m7` (line 284), `ozawa_literal_fails_m7_bits` (line 295). Each states that $\rho$ and $\sigma$ are positive semidefinite with trace 1, that $A$ is positive semidefinite, and that

  ```
  Real.sqrt (8 * ozawaDelta ρ σ * ((ρ + σ) * A ^ 2).trace.re) < (CFC.abs (ρ - σ) * A).trace.re
  ```

  (with `ozawaDelta₂` in the `_bits` versions). This is Theorem 5.2.
- `ozawa_question_literal_false` (line 311), `ozawa_question_literal_false_bits` (line 321), `ozawa_question_literal_false_rpow` (line 331):

  ```
  ¬ ∀ ρ σ A : Matrix (Fin 2) (Fin 2) ℂ, ρ.PosSemidef → ρ.trace = 1 → σ.PosSemidef →
      σ.trace = 1 → A.PosSemidef →
      (CFC.abs (ρ - σ) * A).trace.re ≤ Real.sqrt (8 * ozawaDelta ρ σ * ((ρ + σ) * A ^ 2).trace.re)
  ```

  (base 2 in `_bits`; `(·) ^ (1 / (2 : ℝ))` in place of `Real.sqrt` in `_rpow`). All three are derived from the $m=5$ example. This is the negative answer.

**First version** (`Rational.lean`, over $\mathbb{Q}$): `rho_idem`, `sig5_idem`, `sig5_trace`, `sig5_eq_outer`, `A5_eq_outer`, `A5_idem`, `A5_trace`, `D5_sq`, `D5_trace`, `W5_spectral`, `W5_proj_orth`, `q5`, `lhs5`, and the same for $m=7$.

## Build output

The independent rerun ([`cert/OZ-1_lean.out`](cert/OZ-1_lean.out)) ends with:

```
Build completed successfully (6965 jobs).
== sorry / admit scan
== axioms
'Pipeline.Ozawa.ozawa_question_literal_false' depends on axioms: [propext, Classical.choice, Quot.sound]
...   (28 lines, all [propext, Classical.choice, Quot.sound])
PASS lean_check Ozawa (Lean (version 4.37.0-rc1, x86_64-w64-windows-gnu, commit 0b77e12952ad39077d80d8bd6b66d601f225c321, Release))
```

The job count 6965 is that of the shared project in the original repository, which also contained other projects. A standalone build will report a different count.

Warnings in the build log for these files: Mathlib's notices "consider adding `module`", one deprecation (`Real.exp_nat_mul`, `Scalar.lean` line 42), and eight unused-simp-argument linter warnings in `Rational.lean`. None is an error.

## Deviations from the source

1. **Real parts of traces.** In Lean the trace of a complex matrix is a complex number, and the theorems take `.re`. The source's quantities are real for hermitian arguments. For the examples, the complex traces are proved equal to the real numbers $5/13$, $1/13$, $7/25$ and $1/25$ (`lhs5C`, `q5C`, `lhs7C`, `q7C`). So nothing is lost for the counterexample.
2. **Dimension 2.** The theorems quantify over $2\times 2$ complex matrices. This restricts the counterexample, not the question: a counterexample in $M_2(\mathbb{C})$ is a counterexample to the question as printed.

There is no other weakening: the constant 8, the condition $A\ge 0$ and the definition of $\delta$ are those of the source.

## What is not formalized, and why

| Result of [`PROOF.md`](PROOF.md) | Why not |
| --- | --- |
| Lemma 2.1 (the absolute value of the functional $\varphi-\psi$ is $\mathrm{Tr}(\lvert\rho-\sigma\rvert\cdot)$) | The Lean statement takes the matrix absolute value as the definition of $\lvert\varphi-\psi\rvert(A)$. Formalizing the Jordan decomposition of functionals was not attempted. |
| Lemma 4.1 and Proposition 4.2 for general real $m$ | Not needed for the negative answer, which uses two fixed examples. |
| Remark 5.4 and the family at $m=1,2,3,4,6$ | Each value of $m$ would need its own scalar inequality. Feasible with the same method, but not done; these signs are certified by computation only. |
| Theorem 6.1 (no constant) and Theorem 6.2 (no function of $\delta$) | Not attempted. They need the closed form for general $m$ and real-analysis estimates. |
| Proposition 6.3, Corollaries 6.4 and 6.5 | Not attempted; they need general dimension, or a third example. |
| Lemma 7.1 and Proposition 7.2 (commuting states) | Not attempted. |
| The decimal values of the certificates | They are outputs of the two certificate programs, not theorems. |
| The other reading, $\lvert(\varphi-\psi)(A)\rvert$ | Not claimed, so not formalized. |
