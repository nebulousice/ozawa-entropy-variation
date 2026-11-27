import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# OZ-1, rational layer (moved unchanged from the first version of `Main.lean`, 2026-11-27)

Exact identities over `ℚ` for the m = 5 and m = 7 witnesses.  The complex versions used by the
final theorems are re-proved in `Witness.lean`; this file is kept because CERT.md cites these names.
-/

namespace Pipeline.Ozawa

open Matrix

/-! ## Part 1: exact matrix identities over ℚ -/

section m5

def rho : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 0]
def sig5 : Matrix (Fin 2) (Fin 2) ℚ := !![144/169, 60/169; 60/169, 25/169]
def A5 : Matrix (Fin 2) (Fin 2) ℚ := !![1/26, -5/26; -5/26, 25/26]
def u5 : Fin 2 → ℚ := ![1, -5]

theorem rho_idem : rho * rho = rho := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rho, Matrix.mul_apply, Fin.sum_univ_two]

theorem rho_trace : trace rho = 1 := by simp [rho, Matrix.trace_fin_two]

theorem sig5_idem : sig5 * sig5 = sig5 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sig5, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem sig5_trace : trace sig5 = 1 := by simp [sig5, Matrix.trace_fin_two]; norm_num

theorem sig5_eq_outer : sig5 = vecMulVec ![12/13, 5/13] ![12/13, 5/13] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sig5, vecMulVec] <;> norm_num

theorem A5_eq_outer : A5 = (1/26 : ℚ) • vecMulVec u5 u5 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A5, u5, vecMulVec] <;> norm_num

theorem A5_idem : A5 * A5 = A5 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A5, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem A5_trace : trace A5 = 1 := by simp [A5, Matrix.trace_fin_two]; norm_num

theorem D5_sq : (rho - sig5) * (rho - sig5) = ((5:ℚ)/13)^2 • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rho, sig5, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num

theorem D5_trace : trace (rho - sig5) = 0 := by simp [rho, sig5, Matrix.trace_fin_two]; norm_num

theorem W5_spectral :
    (1/2 : ℚ) • (rho + sig5) = (25/26 : ℚ) • (1 - A5) + (1/26 : ℚ) • A5 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rho, sig5, A5, Matrix.one_apply] <;> norm_num

theorem W5_proj_orth : (1 - A5) * A5 = 0 := by
  rw [sub_mul, one_mul, A5_idem, sub_self]

theorem q5 : trace ((rho + sig5) * A5 * A5) = 1/13 := by
  rw [Matrix.mul_assoc, A5_idem]
  simp [rho, sig5, A5, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; norm_num

theorem lhs5 : trace ((((5:ℚ)/13) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) * A5) = 5/13 := by
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, A5_trace]; norm_num

end m5

section m7

def sig7 : Matrix (Fin 2) (Fin 2) ℚ := !![576/625, 168/625; 168/625, 49/625]
def A7 : Matrix (Fin 2) (Fin 2) ℚ := !![1/50, -7/50; -7/50, 49/50]
def u7 : Fin 2 → ℚ := ![1, -7]

theorem sig7_idem : sig7 * sig7 = sig7 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sig7, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem sig7_trace : trace sig7 = 1 := by simp [sig7, Matrix.trace_fin_two]; norm_num

theorem sig7_eq_outer : sig7 = vecMulVec ![24/25, 7/25] ![24/25, 7/25] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sig7, vecMulVec] <;> norm_num

theorem A7_eq_outer : A7 = (1/50 : ℚ) • vecMulVec u7 u7 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A7, u7, vecMulVec] <;> norm_num

theorem A7_idem : A7 * A7 = A7 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [A7, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem A7_trace : trace A7 = 1 := by simp [A7, Matrix.trace_fin_two]; norm_num

theorem D7_sq : (rho - sig7) * (rho - sig7) = ((7:ℚ)/25)^2 • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rho, sig7, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num

theorem D7_trace : trace (rho - sig7) = 0 := by simp [rho, sig7, Matrix.trace_fin_two]; norm_num

theorem W7_spectral :
    (1/2 : ℚ) • (rho + sig7) = (49/50 : ℚ) • (1 - A7) + (1/50 : ℚ) • A7 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rho, sig7, A7, Matrix.one_apply] <;> norm_num

theorem W7_proj_orth : (1 - A7) * A7 = 0 := by
  rw [sub_mul, one_mul, A7_idem, sub_self]

theorem q7 : trace ((rho + sig7) * A7 * A7) = 1/25 := by
  rw [Matrix.mul_assoc, A7_idem]
  simp [rho, sig7, A7, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; norm_num

theorem lhs7 : trace ((((7:ℚ)/25) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) * A7) = 7/25 := by
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, A7_trace]; norm_num

end m7

end Pipeline.Ozawa
