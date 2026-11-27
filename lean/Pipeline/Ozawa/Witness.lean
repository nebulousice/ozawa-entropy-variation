import Pipeline.Ozawa.Spectral
import Pipeline.Ozawa.Scalar
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# OZ-1, linking layer: the literal Ozawa inequality fails (m = 5 and m = 7)

All quantities are defined from the matrices through Mathlib's continuous functional calculus:

* `|X|` is Mathlib's `CFC.abs X = CFC.sqrt (star X * X)` (with the `MatrixOrder` instances);
* the matrix logarithm is `cfc Real.log X` (this is the definition of Mathlib's `CFC.log`, which
  is only set up for normed algebras; Mathlib's convention `Real.log 0 = 0` gives `0 log 0 = 0`);
* von Neumann entropy `H(X) = -Tr(X log X)` (`vnEntropy`, natural log) and
  `H₂(X) = -Tr(X log₂ X)` (`vnEntropy₂`, `log₂ = Real.logb 2`), real parts of the traces;
* `δ(ρ,σ) = H((ρ+σ)/2) - (H ρ + H σ)/2` (`ozawaDelta`, `ozawaDelta₂`).

States are `2 × 2` complex density matrices (`PosSemidef`, trace `1`); `A ≥ 0` is `PosSemidef`;
`|φ-ψ|(A) = Tr(|ρ-σ| A)`, `(φ+ψ)(A²) = Tr((ρ+σ) A²)`; the power `1/2` is `Real.sqrt`.
-/

namespace Pipeline.Ozawa

open Matrix
open scoped MatrixOrder ComplexOrder

section Defs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- von Neumann entropy, natural logarithm: `H(X) = -Tr(X log X)` with `log X = cfc Real.log X`. -/
noncomputable def vnEntropy (X : Matrix n n ℂ) : ℝ :=
  (-(X * cfc Real.log X).trace).re

/-- von Neumann entropy in bits: `H₂(X) = -Tr(X log₂ X)` with `log₂ X = cfc (Real.logb 2) X`. -/
noncomputable def vnEntropy₂ (X : Matrix n n ℂ) : ℝ :=
  (-(X * cfc (Real.logb 2) X).trace).re

/-- Ozawa's `δ(ρ,σ) = H((ρ+σ)/2) - (H(ρ) + H(σ))/2`, natural logarithm. -/
noncomputable def ozawaDelta (ρ σ : Matrix n n ℂ) : ℝ :=
  vnEntropy ((1/2 : ℝ) • (ρ + σ)) - (vnEntropy ρ + vnEntropy σ) / 2

/-- Ozawa's `δ`, entropy in bits. -/
noncomputable def ozawaDelta₂ (ρ σ : Matrix n n ℂ) : ℝ :=
  vnEntropy₂ ((1/2 : ℝ) • (ρ + σ)) - (vnEntropy₂ ρ + vnEntropy₂ σ) / 2

/-- `X * cfc g X = cfc (t ↦ t * g t) X` for a Hermitian matrix (any `g`: the spectrum is finite). -/
lemma mul_cfc_eq_cfc_mul (X : Matrix n n ℂ) (hX : IsSelfAdjoint X) (g : ℝ → ℝ) :
    X * cfc g X = cfc (fun t => t * g t) X := by
  rw [cfc_mul (fun t : ℝ => t) g X ((Matrix.finite_real_spectrum (A := X)).continuousOn _)
    ((Matrix.finite_real_spectrum (A := X)).continuousOn _), cfc_id' ℝ X hX]

end Defs

section TwoByTwo

/-- `-Tr(M · lg(M))` for `M = a • P + b • (1 - P)`, `P` a rank-one projection in `M₂(ℂ)`. -/
lemma negTrace_twoProj {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsSelfAdjoint P) (hPP : P * P = P)
    (htr : P.trace = 1) {a b : ℝ} (hab : a ≠ b) (lg : ℝ → ℝ) :
    (-((a • P + b • (1 - P)) * cfc lg (a • P + b • (1 - P))).trace).re
      = -(a * lg a) - b * lg b := by
  rw [mul_cfc_eq_cfc_mul _ (isSelfAdjoint_twoProj hP a b), cfc_twoProj hP hPP hab,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_sub, htr,
    Matrix.trace_one]
  simp only [Fintype.card_fin, Nat.cast_ofNat, Complex.real_smul]
  rw [show (2 : ℂ) - 1 = 1 by norm_num, mul_one, mul_one, ← Complex.ofReal_add,
    ← Complex.ofReal_neg, Complex.ofReal_re]
  ring

/-- A rank-one projection (pure state) has `-Tr(P · lg(P)) = 0` whenever `lg 1 = 0`. -/
lemma negTrace_proj {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsSelfAdjoint P) (hPP : P * P = P)
    (htr : P.trace = 1) (lg : ℝ → ℝ) (hlg : lg 1 = 0) :
    (-(P * cfc lg P).trace).re = 0 := by
  have h := negTrace_twoProj hP hPP htr (a := 1) (b := 0) one_ne_zero lg
  have e : (1 : ℝ) • P + (0 : ℝ) • (1 - P) = P := by simp
  rw [e] at h
  rw [h, hlg]
  ring

lemma psd_of_proj {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsSelfAdjoint P) (hPP : P * P = P) :
    P.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [← Matrix.star_eq_conjTranspose, hP.star_eq, hPP] at h

end TwoByTwo

/-! ## The witnesses as complex matrices -/

/-- `ρ = |0⟩⟨0|`. -/
def rhoC : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

lemma rhoC_sa : IsSelfAdjoint rhoC := by
  rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;> simp [rhoC, Matrix.conjTranspose_apply]

lemma rhoC_idem : rhoC * rhoC = rhoC := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rhoC, Matrix.mul_apply, Fin.sum_univ_two]

lemma rhoC_trace : rhoC.trace = 1 := by simp [rhoC, Matrix.trace_fin_two]

section m5

/-- `σ = v vᵀ`, `v = (12/13, 5/13)`. -/
noncomputable def sig5C : Matrix (Fin 2) (Fin 2) ℂ := !![144/169, 60/169; 60/169, 25/169]
/-- `A = (1/26) u uᵀ`, `u = (1, -5)`. -/
noncomputable def A5C : Matrix (Fin 2) (Fin 2) ℂ := !![1/26, -5/26; -5/26, 25/26]

lemma sig5C_sa : IsSelfAdjoint sig5C := by
  rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sig5C, Matrix.conjTranspose_apply]

lemma A5C_sa : IsSelfAdjoint A5C := by
  rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A5C, Matrix.conjTranspose_apply]

lemma sig5C_idem : sig5C * sig5C = sig5C := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sig5C, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

lemma A5C_idem : A5C * A5C = A5C := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A5C, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

lemma sig5C_trace : sig5C.trace = 1 := by
  simp [sig5C, Matrix.trace_fin_two]; norm_num

lemma A5C_trace : A5C.trace = 1 := by
  simp [A5C, Matrix.trace_fin_two]; norm_num

/-- `(ρ+σ)/2 = (1/26) A + (25/26) (1 - A)`. -/
lemma W5C_two : (1/2 : ℝ) • (rhoC + sig5C) = (1/26 : ℝ) • A5C + (25/26 : ℝ) • (1 - A5C) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rhoC, sig5C, A5C, Complex.real_smul] <;> norm_num

/-- `(ρ - σ)² = (5/13)² • 1`. -/
lemma D5C_sq : (rhoC - sig5C) * (rhoC - sig5C) = ((5 : ℝ) / 13) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rhoC, sig5C, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul] <;>
    norm_num

/-- **G1 (m = 5)**: `|ρ - σ| = (5/13) • 1`, with Mathlib's `CFC.abs`. -/
theorem abs5C : CFC.abs (rhoC - sig5C) = ((5 : ℝ) / 13) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hD : IsSelfAdjoint (rhoC - sig5C) := rhoC_sa.sub sig5C_sa
  rw [CFC.abs_eq_cfc_norm _ hD, cfc_norm_of_mul_self hD (by norm_num) D5C_sq]

/-- `Tr(|ρ - σ| A) = 5/13`. -/
lemma lhs5C : (CFC.abs (rhoC - sig5C) * A5C).trace = ((5 / 13 : ℝ) : ℂ) := by
  rw [abs5C, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, A5C_trace, Complex.real_smul,
    mul_one]

/-- `Tr((ρ + σ) A²) = 1/13`. -/
lemma q5C : ((rhoC + sig5C) * A5C ^ 2).trace = ((1 / 13 : ℝ) : ℂ) := by
  rw [sq, A5C_idem]
  simp [rhoC, sig5C, A5C, Matrix.trace_fin_two]; norm_num

/-- **G2 (m = 5)**: `δ(ρ,σ) = binEntropy(1/26)`, entropies defined through the CFC. -/
theorem delta5C : ozawaDelta rhoC sig5C = Real.binEntropy (1/26) := by
  unfold ozawaDelta vnEntropy
  rw [W5C_two,
    negTrace_twoProj (a := 1/26) (b := 25/26) A5C_sa A5C_idem A5C_trace (by norm_num) Real.log,
    negTrace_proj rhoC_sa rhoC_idem rhoC_trace Real.log Real.log_one,
    negTrace_proj sig5C_sa sig5C_idem sig5C_trace Real.log Real.log_one,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, show (1 : ℝ) - 1/26 = 25/26 by norm_num]
  simp only [Real.negMulLog]
  ring

/-- **G2 (m = 5, bits)**: `δ₂(ρ,σ) = binEntropy(1/26) / log 2`. -/
theorem delta5C₂ : ozawaDelta₂ rhoC sig5C = Real.binEntropy (1/26) / Real.log 2 := by
  unfold ozawaDelta₂ vnEntropy₂
  rw [W5C_two,
    negTrace_twoProj (a := 1/26) (b := 25/26) A5C_sa A5C_idem A5C_trace (by norm_num)
      (Real.logb 2),
    negTrace_proj rhoC_sa rhoC_idem rhoC_trace (Real.logb 2) Real.logb_one,
    negTrace_proj sig5C_sa sig5C_idem sig5C_trace (Real.logb 2) Real.logb_one,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, show (1 : ℝ) - 1/26 = 25/26 by norm_num]
  simp only [Real.negMulLog, Real.logb]
  ring

/-- **OZ-1, m = 5, natural log.**  `ρ`, `σ` are density matrices, `A ≥ 0`, and
`(8 δ(ρ,σ) Tr((ρ+σ)A²))^{1/2} < Tr(|ρ-σ| A)`. -/
theorem ozawa_literal_fails_m5 :
    rhoC.PosSemidef ∧ rhoC.trace = 1 ∧ sig5C.PosSemidef ∧ sig5C.trace = 1 ∧ A5C.PosSemidef ∧
    Real.sqrt (8 * ozawaDelta rhoC sig5C * ((rhoC + sig5C) * A5C ^ 2).trace.re)
      < (CFC.abs (rhoC - sig5C) * A5C).trace.re := by
  refine ⟨psd_of_proj rhoC_sa rhoC_idem, rhoC_trace, psd_of_proj sig5C_sa sig5C_idem,
    sig5C_trace, psd_of_proj A5C_sa A5C_idem, ?_⟩
  rw [delta5C, q5C, lhs5C, Complex.ofReal_re, Complex.ofReal_re,
    Real.sqrt_lt' (by norm_num)]
  exact ozawa_m5_nat

/-- **OZ-1, m = 5, entropy in bits.** -/
theorem ozawa_literal_fails_m5_bits :
    rhoC.PosSemidef ∧ rhoC.trace = 1 ∧ sig5C.PosSemidef ∧ sig5C.trace = 1 ∧ A5C.PosSemidef ∧
    Real.sqrt (8 * ozawaDelta₂ rhoC sig5C * ((rhoC + sig5C) * A5C ^ 2).trace.re)
      < (CFC.abs (rhoC - sig5C) * A5C).trace.re := by
  refine ⟨psd_of_proj rhoC_sa rhoC_idem, rhoC_trace, psd_of_proj sig5C_sa sig5C_idem,
    sig5C_trace, psd_of_proj A5C_sa A5C_idem, ?_⟩
  rw [delta5C₂, q5C, lhs5C, Complex.ofReal_re, Complex.ofReal_re,
    Real.sqrt_lt' (by norm_num)]
  exact ozawa_m5_base2

end m5

section m7

/-- `σ = v vᵀ`, `v = (24/25, 7/25)`. -/
noncomputable def sig7C : Matrix (Fin 2) (Fin 2) ℂ := !![576/625, 168/625; 168/625, 49/625]
/-- `A = (1/50) u uᵀ`, `u = (1, -7)`. -/
noncomputable def A7C : Matrix (Fin 2) (Fin 2) ℂ := !![1/50, -7/50; -7/50, 49/50]

lemma sig7C_sa : IsSelfAdjoint sig7C := by
  rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sig7C, Matrix.conjTranspose_apply]

lemma A7C_sa : IsSelfAdjoint A7C := by
  rw [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [A7C, Matrix.conjTranspose_apply]

lemma sig7C_idem : sig7C * sig7C = sig7C := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sig7C, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

lemma A7C_idem : A7C * A7C = A7C := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A7C, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

lemma sig7C_trace : sig7C.trace = 1 := by
  simp [sig7C, Matrix.trace_fin_two]; norm_num

lemma A7C_trace : A7C.trace = 1 := by
  simp [A7C, Matrix.trace_fin_two]; norm_num

/-- `(ρ+σ)/2 = (1/50) A + (49/50) (1 - A)`. -/
lemma W7C_two : (1/2 : ℝ) • (rhoC + sig7C) = (1/50 : ℝ) • A7C + (49/50 : ℝ) • (1 - A7C) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rhoC, sig7C, A7C, Complex.real_smul] <;> norm_num

/-- `(ρ - σ)² = (7/25)² • 1`. -/
lemma D7C_sq : (rhoC - sig7C) * (rhoC - sig7C) = ((7 : ℝ) / 25) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rhoC, sig7C, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul] <;>
    norm_num

/-- **G1 (m = 7)**: `|ρ - σ| = (7/25) • 1`, with Mathlib's `CFC.abs`. -/
theorem abs7C : CFC.abs (rhoC - sig7C) = ((7 : ℝ) / 25) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hD : IsSelfAdjoint (rhoC - sig7C) := rhoC_sa.sub sig7C_sa
  rw [CFC.abs_eq_cfc_norm _ hD, cfc_norm_of_mul_self hD (by norm_num) D7C_sq]

lemma lhs7C : (CFC.abs (rhoC - sig7C) * A7C).trace = ((7 / 25 : ℝ) : ℂ) := by
  rw [abs7C, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, A7C_trace, Complex.real_smul,
    mul_one]

lemma q7C : ((rhoC + sig7C) * A7C ^ 2).trace = ((1 / 25 : ℝ) : ℂ) := by
  rw [sq, A7C_idem]
  simp [rhoC, sig7C, A7C, Matrix.trace_fin_two]; norm_num

/-- **G2 (m = 7)**: `δ(ρ,σ) = binEntropy(1/50)`. -/
theorem delta7C : ozawaDelta rhoC sig7C = Real.binEntropy (1/50) := by
  unfold ozawaDelta vnEntropy
  rw [W7C_two,
    negTrace_twoProj (a := 1/50) (b := 49/50) A7C_sa A7C_idem A7C_trace (by norm_num) Real.log,
    negTrace_proj rhoC_sa rhoC_idem rhoC_trace Real.log Real.log_one,
    negTrace_proj sig7C_sa sig7C_idem sig7C_trace Real.log Real.log_one,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, show (1 : ℝ) - 1/50 = 49/50 by norm_num]
  simp only [Real.negMulLog]
  ring

/-- **G2 (m = 7, bits)**: `δ₂(ρ,σ) = binEntropy(1/50) / log 2`. -/
theorem delta7C₂ : ozawaDelta₂ rhoC sig7C = Real.binEntropy (1/50) / Real.log 2 := by
  unfold ozawaDelta₂ vnEntropy₂
  rw [W7C_two,
    negTrace_twoProj (a := 1/50) (b := 49/50) A7C_sa A7C_idem A7C_trace (by norm_num)
      (Real.logb 2),
    negTrace_proj rhoC_sa rhoC_idem rhoC_trace (Real.logb 2) Real.logb_one,
    negTrace_proj sig7C_sa sig7C_idem sig7C_trace (Real.logb 2) Real.logb_one,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, show (1 : ℝ) - 1/50 = 49/50 by norm_num]
  simp only [Real.negMulLog, Real.logb]
  ring

/-- **OZ-1, m = 7, natural log.** -/
theorem ozawa_literal_fails_m7 :
    rhoC.PosSemidef ∧ rhoC.trace = 1 ∧ sig7C.PosSemidef ∧ sig7C.trace = 1 ∧ A7C.PosSemidef ∧
    Real.sqrt (8 * ozawaDelta rhoC sig7C * ((rhoC + sig7C) * A7C ^ 2).trace.re)
      < (CFC.abs (rhoC - sig7C) * A7C).trace.re := by
  refine ⟨psd_of_proj rhoC_sa rhoC_idem, rhoC_trace, psd_of_proj sig7C_sa sig7C_idem,
    sig7C_trace, psd_of_proj A7C_sa A7C_idem, ?_⟩
  rw [delta7C, q7C, lhs7C, Complex.ofReal_re, Complex.ofReal_re,
    Real.sqrt_lt' (by norm_num)]
  exact ozawa_m7_nat

/-- **OZ-1, m = 7, entropy in bits.** -/
theorem ozawa_literal_fails_m7_bits :
    rhoC.PosSemidef ∧ rhoC.trace = 1 ∧ sig7C.PosSemidef ∧ sig7C.trace = 1 ∧ A7C.PosSemidef ∧
    Real.sqrt (8 * ozawaDelta₂ rhoC sig7C * ((rhoC + sig7C) * A7C ^ 2).trace.re)
      < (CFC.abs (rhoC - sig7C) * A7C).trace.re := by
  refine ⟨psd_of_proj rhoC_sa rhoC_idem, rhoC_trace, psd_of_proj sig7C_sa sig7C_idem,
    sig7C_trace, psd_of_proj A7C_sa A7C_idem, ?_⟩
  rw [delta7C₂, q7C, lhs7C, Complex.ofReal_re, Complex.ofReal_re,
    Real.sqrt_lt' (by norm_num)]
  exact ozawa_m7_base2

end m7

/-! ## The literal question, as a universally quantified statement -/

/-- The literal reading of Ozawa's question (5)(i), for `2 × 2` density matrices and natural log,
is false. -/
theorem ozawa_question_literal_false :
    ¬ ∀ ρ σ A : Matrix (Fin 2) (Fin 2) ℂ, ρ.PosSemidef → ρ.trace = 1 → σ.PosSemidef →
      σ.trace = 1 → A.PosSemidef →
      (CFC.abs (ρ - σ) * A).trace.re ≤
        Real.sqrt (8 * ozawaDelta ρ σ * ((ρ + σ) * A ^ 2).trace.re) := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ozawa_literal_fails_m5
  exact absurd (h _ _ _ h1 h2 h3 h4 h5) (not_le.mpr h6)

/-- The same, with the entropy in bits. -/
theorem ozawa_question_literal_false_bits :
    ¬ ∀ ρ σ A : Matrix (Fin 2) (Fin 2) ℂ, ρ.PosSemidef → ρ.trace = 1 → σ.PosSemidef →
      σ.trace = 1 → A.PosSemidef →
      (CFC.abs (ρ - σ) * A).trace.re ≤
        Real.sqrt (8 * ozawaDelta₂ ρ σ * ((ρ + σ) * A ^ 2).trace.re) := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ozawa_literal_fails_m5_bits
  exact absurd (h _ _ _ h1 h2 h3 h4 h5) (not_le.mpr h6)

/-- The same, with the power `(·)^{1/2}` written as `Real.rpow` instead of `Real.sqrt`. -/
theorem ozawa_question_literal_false_rpow :
    ¬ ∀ ρ σ A : Matrix (Fin 2) (Fin 2) ℂ, ρ.PosSemidef → ρ.trace = 1 → σ.PosSemidef →
      σ.trace = 1 → A.PosSemidef →
      (CFC.abs (ρ - σ) * A).trace.re ≤
        (8 * ozawaDelta ρ σ * ((ρ + σ) * A ^ 2).trace.re) ^ (1 / (2 : ℝ)) := by
  simp_rw [← Real.sqrt_eq_rpow]
  exact ozawa_question_literal_false

end Pipeline.Ozawa
