import Pipeline.Ozawa.Rational
import Pipeline.Ozawa.Scalar
import Pipeline.Ozawa.Spectral
import Pipeline.Ozawa.Witness

/-!
# OZ-1: the literal reading of Ozawa's question OWR 22/2018 (5)(i) is false (m = 5, m = 7)

Literal question: is `Tr(|ρ - σ| A) ≤ (8 δ(ρ,σ) Tr((ρ+σ) A²))^{1/2}` for every `A ≥ 0`, with
`δ = H((ρ+σ)/2) - (H ρ + H σ)/2` (von Neumann entropy)?

Witness (m = 5): `ρ = diag(1,0)`, `σ = v vᵀ`, `v = (12/13, 5/13)`, `A = (1/26) u uᵀ`, `u = (1,-5)`.
Witness (m = 7): `σ = v vᵀ`, `v = (24/25, 7/25)`, `A = (1/50) u uᵀ`, `u = (1,-7)`.

Files:
* `Rational.lean` — exact identities over `ℚ` (first version, kept for CERT.md's references).
* `Scalar.lean` — strict inequalities with `Real.log`, `Real.binEntropy` (first version).
* `Spectral.lean` — generic CFC lemmas: two-projection lemma `cfc_twoProj` and
  `cfc_norm_of_mul_self` (`D * D = s² • 1`, `s ≥ 0` ⇒ `cfc ‖·‖ D = s • 1`).
* `Witness.lean` — definitions of von Neumann entropy and `δ` through `cfc`, the complex witnesses,
  `|ρ - σ| = s • 1` with Mathlib's `CFC.abs` (`abs5C`, `abs7C`), `δ = binEntropy x`
  (`delta5C`, `delta7C`, and the base-2 versions), and the final theorems.

Main theorems (all quantities computed from the matrices via Mathlib's continuous functional
calculus; no hand steps):
* `ozawa_literal_fails_m5`, `ozawa_literal_fails_m5_bits`, `ozawa_literal_fails_m7`,
  `ozawa_literal_fails_m7_bits`: the witnesses are density matrices / `A` is PSD, and
  `√(8 δ Tr((ρ+σ)A²)) < Tr(|ρ-σ| A)` (natural log, resp. log base 2);
* `ozawa_question_literal_false` (natural log), `ozawa_question_literal_false_bits` (base 2),
  `ozawa_question_literal_false_rpow` (power `1/2` as `rpow`): the universally quantified literal
  inequality over `2 × 2` complex density matrices is false.
-/

#print axioms Pipeline.Ozawa.ozawa_question_literal_false
#print axioms Pipeline.Ozawa.ozawa_question_literal_false_bits
#print axioms Pipeline.Ozawa.ozawa_question_literal_false_rpow
#print axioms Pipeline.Ozawa.ozawa_literal_fails_m5
#print axioms Pipeline.Ozawa.ozawa_literal_fails_m5_bits
#print axioms Pipeline.Ozawa.ozawa_literal_fails_m7
#print axioms Pipeline.Ozawa.ozawa_literal_fails_m7_bits
#print axioms Pipeline.Ozawa.cfc_twoProj
#print axioms Pipeline.Ozawa.cfc_norm_of_mul_self
#print axioms Pipeline.Ozawa.abs5C
#print axioms Pipeline.Ozawa.abs7C
#print axioms Pipeline.Ozawa.delta5C
#print axioms Pipeline.Ozawa.delta5C₂
#print axioms Pipeline.Ozawa.delta7C
#print axioms Pipeline.Ozawa.delta7C₂
#print axioms Pipeline.Ozawa.D5_sq
#print axioms Pipeline.Ozawa.W5_spectral
#print axioms Pipeline.Ozawa.q5
#print axioms Pipeline.Ozawa.A5_eq_outer
#print axioms Pipeline.Ozawa.D7_sq
#print axioms Pipeline.Ozawa.W7_spectral
#print axioms Pipeline.Ozawa.q7
#print axioms Pipeline.Ozawa.A7_eq_outer
#print axioms Pipeline.Ozawa.log_26_lt
#print axioms Pipeline.Ozawa.ozawa_m5_nat
#print axioms Pipeline.Ozawa.ozawa_m5_base2
#print axioms Pipeline.Ozawa.ozawa_m7_nat
#print axioms Pipeline.Ozawa.ozawa_m7_base2
