import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# OZ-1, spectral layer: two lemmas about Mathlib's continuous functional calculus

Everything here is about the generic `cfc` of Mathlib (real functional calculus for self-adjoint
elements, `ContinuousFunctionalCalculus ℝ A IsSelfAdjoint`).  For matrices over `ℂ` this is the
instance `Matrix.IsHermitian.instContinuousFunctionalCalculus`.

* `spectrum_twoProj_subset`, `cfc_twoProj` (two-projection lemma): if `P` is a self-adjoint
  idempotent and `a ≠ b`, then `spectrum ℝ (a • P + b • (1 - P)) ⊆ {a, b}` and, for **every**
  `f : ℝ → ℝ`, `cfc f (a • P + b • (1 - P)) = f a • P + f b • (1 - P)`.
* `cfc_norm_of_mul_self` : if `D` is self-adjoint and `D * D = s ^ 2 • 1` with `s ≥ 0`, then
  `cfc (‖·‖) D = s • 1`.
-/

namespace Pipeline.Ozawa

section General

variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A] [StarModule ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

omit [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] in
lemma isSelfAdjoint_twoProj {P : A} (hP : IsSelfAdjoint P) (a b : ℝ) :
    IsSelfAdjoint (a • P + b • (1 - P)) :=
  (IsSelfAdjoint.smul (IsSelfAdjoint.all a) hP).add
    (IsSelfAdjoint.smul (IsSelfAdjoint.all b) ((IsSelfAdjoint.one (R := A)).sub hP))

/-- The spectrum of `a • P + b • (1 - P)` lies in `{a, b}` when `P` is a self-adjoint idempotent. -/
lemma spectrum_twoProj_subset {P : A} (hP : IsSelfAdjoint P) (hPP : P * P = P) (a b : ℝ) :
    spectrum ℝ (a • P + b • (1 - P)) ⊆ {a, b} := by
  have hM : IsSelfAdjoint (a • P + b • (1 - P)) := isSelfAdjoint_twoProj hP a b
  have h1 : cfc (fun t : ℝ => (t - a) * (t - b)) (a • P + b • (1 - P))
      = cfc (fun _ : ℝ => (0 : ℝ)) (a • P + b • (1 - P)) := by
    rw [cfc_mul (fun t : ℝ => t - a) (fun t : ℝ => t - b) _,
      cfc_sub (fun t : ℝ => t) (fun _ : ℝ => a) _, cfc_sub (fun t : ℝ => t) (fun _ : ℝ => b) _,
      cfc_id' ℝ _ hM, cfc_const a _ hM, cfc_const b _ hM, cfc_const_zero]
    simp only [Algebra.algebraMap_eq_smul_one]
    have e1 : a • P + b • (1 - P) - a • (1 : A) = (b - a) • (1 - P) := by module
    have e2 : a • P + b • (1 - P) - b • (1 : A) = (a - b) • P := by module
    have e3 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hPP, sub_self]
    rw [e1, e2, smul_mul_smul_comm, e3, smul_zero]
  intro t ht
  have h2 : (t - a) * (t - b) = 0 := (eqOn_of_cfc_eq_cfc h1 (ha := hM)) ht
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by simp only [Set.mem_singleton_iff]; linarith)

/-- **Two-projection lemma.**  If `P` is a self-adjoint idempotent and `a ≠ b`, then for every
`f : ℝ → ℝ`, `cfc f (a • P + b • (1 - P)) = f a • P + f b • (1 - P)`. -/
theorem cfc_twoProj {P : A} (hP : IsSelfAdjoint P) (hPP : P * P = P) {a b : ℝ} (hab : a ≠ b)
    (f : ℝ → ℝ) : cfc f (a • P + b • (1 - P)) = f a • P + f b • (1 - P) := by
  have hM : IsSelfAdjoint (a • P + b • (1 - P)) := isSelfAdjoint_twoProj hP a b
  have hspec := spectrum_twoProj_subset hP hPP a b
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  set c : ℝ := (f a - f b) / (a - b) with hc
  have hcongr : (spectrum ℝ (a • P + b • (1 - P))).EqOn f (fun t => f b + c * (t - b)) := by
    intro t ht
    rcases Set.mem_insert_iff.mp (hspec ht) with h | h
    · subst h
      simp only [hc]
      field_simp
      ring
    · rw [Set.mem_singleton_iff] at h
      subst h
      simp
  rw [cfc_congr hcongr, cfc_const_add (f b) (fun t => c * (t - b)) _ (by fun_prop) hM,
    cfc_const_mul c (fun t => t - b) _, cfc_sub (fun t : ℝ => t) (fun _ : ℝ => b) _,
    cfc_id' ℝ _ hM, cfc_const b _ hM]
  simp only [Algebra.algebraMap_eq_smul_one]
  have e2 : a • P + b • (1 - P) - b • (1 : A) = (a - b) • P := by module
  rw [e2, smul_smul, show c * (a - b) = f a - f b from div_mul_cancel₀ _ hab']
  module

omit [StarModule ℝ A] in
/-- If `D` is self-adjoint and `D * D = s ^ 2 • 1` with `s ≥ 0`, then `cfc (‖·‖) D = s • 1`. -/
theorem cfc_norm_of_mul_self {D : A} (hD : IsSelfAdjoint D) {s : ℝ} (hs : 0 ≤ s)
    (hDD : D * D = (s ^ 2) • (1 : A)) : cfc (fun t : ℝ => ‖t‖) D = s • (1 : A) := by
  have h1 : cfc (fun t : ℝ => t * t) D = cfc (fun _ : ℝ => s ^ 2) D := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) D, cfc_id' ℝ D hD, cfc_const _ D hD,
      Algebra.algebraMap_eq_smul_one, hDD]
  have hcongr : (spectrum ℝ D).EqOn (fun t : ℝ => ‖t‖) (fun _ => s) := by
    intro t ht
    have h2 : t * t = s ^ 2 := (eqOn_of_cfc_eq_cfc h1 (ha := hD)) ht
    simp only [Real.norm_eq_abs]
    have h3 : |t| ^ 2 = s ^ 2 := by rw [sq_abs, sq]; exact h2
    exact (pow_left_inj₀ (abs_nonneg t) hs two_ne_zero).mp h3
  rw [cfc_congr hcongr, cfc_const s D hD, Algebra.algebraMap_eq_smul_one]

end General

end Pipeline.Ozawa
