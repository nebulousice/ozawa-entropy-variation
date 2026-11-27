import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# OZ-1, scalar layer (moved unchanged from the first version of `Main.lean`, 2026-11-27)

Strict inequalities with Mathlib's `Real.log` and `Real.binEntropy`.
-/

namespace Pipeline.Ozawa

/-! ## Part 2: the scalar inequalities over ℝ -/

open Real

/-- `binEntropy (1/n) = (1/n) log n + ((n-1)/n) log (n/(n-1))`. -/
theorem binEntropy_inv (n : ℝ) (hn : 1 < n) :
    binEntropy (1/n) = (1/n) * log n + (1 - 1/n) * log (n / (n - 1)) := by
  have hn0 : n ≠ 0 := by positivity
  have hn1 : n - 1 ≠ 0 := by linarith
  have h0 : (1:ℝ) - n⁻¹ = (n - 1) / n := by field_simp
  have h1 : (1 - n⁻¹)⁻¹ = n / (n - 1) := by rw [h0, inv_div]
  simp only [binEntropy, one_div, inv_inv, h1]

/-- `log (n/(n-1)) ≤ 1/(n-1)`. -/
theorem log_ratio_le (n : ℝ) (hn : 1 < n) : log (n / (n - 1)) ≤ 1 / (n - 1) := by
  have hpos : 0 < n / (n - 1) := by apply div_pos <;> linarith
  have h := Real.log_le_sub_one_of_pos hpos
  have : n / (n - 1) - 1 = 1 / (n - 1) := by
    have hn1 : n - 1 ≠ 0 := by linarith
    rw [div_sub_one hn1]
    congr 1
    ring
  linarith

/-- The by-hand inequality behind the m = 5 witness. -/
theorem log_26_lt : log 26 < 21/4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 : (37:ℝ)/16 ≤ exp (21/16) := by linarith [Real.add_one_le_exp ((21:ℝ)/16)]
  have h2 : exp ((21:ℝ)/4) = exp (21/16) ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  calc (26:ℝ) < (37/16)^4 := by norm_num
    _ ≤ exp (21/16) ^ 4 := by gcongr

/-- `log 26 = 5 log 2 + log (13/16) ≤ 5 log 2 - 3/16`. -/
theorem log_26_le_log2 : log 26 ≤ 5 * log 2 - 3/16 := by
  have h : (26:ℝ) = 2^5 * (13/16) := by norm_num
  rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 13/16 by norm_num)
  push_cast; linarith

/-- `log 50 = 6 log 2 + log (25/32) ≤ 6 log 2 - 7/32`. -/
theorem log_50_le_log2 : log 50 ≤ 6 * log 2 - 7/32 := by
  have h : (50:ℝ) = 2^6 * (25/32) := by norm_num
  rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 25/32 by norm_num)
  push_cast; linarith

theorem h26_le : binEntropy (1/26) ≤ (1/26) * log 26 + 1/26 := by
  rw [binEntropy_inv 26 (by norm_num)]
  have := log_ratio_le 26 (by norm_num)
  norm_num at this ⊢
  linarith

theorem h50_le : binEntropy (1/50) ≤ (1/50) * log 50 + 1/50 := by
  rw [binEntropy_inv 50 (by norm_num)]
  have := log_ratio_le 50 (by norm_num)
  norm_num at this ⊢
  linarith

/-- m = 5, natural logarithm: `RHS² = 8 δ Tr((ρ+σ)A²) < LHS²`. -/
theorem ozawa_m5_nat : 8 * binEntropy (1/26) * (1/13) < ((5:ℝ)/13)^2 := by
  have := h26_le
  have := log_26_lt
  nlinarith

/-- m = 5, entropy in base 2 (`δ₂ = δ / log 2`). -/
theorem ozawa_m5_base2 : 8 * (binEntropy (1/26) / log 2) * (1/13) < ((5:ℝ)/13)^2 := by
  have hl := Real.log_two_gt_d9
  have hpos : 0 < log 2 := by linarith
  have h1 := h26_le
  have h2 := log_26_le_log2
  have key : binEntropy (1/26) < 25/104 * log 2 := by linarith
  rw [show 8 * (binEntropy (1/26) / log 2) * (1/13) = (8/13 * binEntropy (1/26)) / log 2 by ring,
    div_lt_iff₀ hpos, show ((5:ℝ)/13)^2 = 25/169 by norm_num]
  linarith

/-- m = 7, natural logarithm. -/
theorem ozawa_m7_nat : 8 * binEntropy (1/50) * (1/25) < ((7:ℝ)/25)^2 := by
  have h1 := h50_le
  have h2 := log_50_le_log2
  have h3 := Real.log_two_lt_d9
  nlinarith

/-- m = 7, entropy in base 2. -/
theorem ozawa_m7_base2 : 8 * (binEntropy (1/50) / log 2) * (1/25) < ((7:ℝ)/25)^2 := by
  have hl := Real.log_two_gt_d9
  have hpos : 0 < log 2 := by linarith
  have h1 := h50_le
  have h2 := log_50_le_log2
  have key : binEntropy (1/50) < 49/200 * log 2 := by linarith
  rw [show 8 * (binEntropy (1/50) / log 2) * (1/25) = (8/25 * binEntropy (1/50)) / log 2 by ring,
    div_lt_iff₀ hpos, show ((7:ℝ)/25)^2 = 49/625 by norm_num]
  linarith

end Pipeline.Ozawa
