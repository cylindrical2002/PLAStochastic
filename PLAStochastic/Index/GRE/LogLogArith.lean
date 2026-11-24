import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# `log log n` bookkeeping for the rank-equispaced height

Real-number lemmas turning the pathwise bounds of `PLAStochastic.Index.Algorithm.RankHeightRecursion` into
`O(log log n)` and `Ω(log log n)` statements.
-/

namespace PGM

open Real Filter

/-- `logb 2 (K · x) = logb 2 K + logb 2 x`. -/
theorem logb_two_mul_le {K x : ℝ} (hK : 0 < K) (hx : 0 < x) :
    Real.logb 2 (K * x) = Real.logb 2 K + Real.logb 2 x :=
  Real.logb_mul hK.ne' hx.ne'

/-- Upper form: `logb 2 L + logb 2 (K L) + C ≤ C' log L` once `log L ≥ 1`. -/
theorem logb_sum_le_mul_log {K C L : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) (hLpos : 0 < L)
    (hL : 1 ≤ Real.log L) :
    Real.logb 2 L + Real.logb 2 (K * L) + C ≤
      ((2 + Real.log K) / Real.log 2 + C) * Real.log L := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : 0 < K := by linarith
  rw [logb_two_mul_le hKpos hLpos]
  simp only [Real.logb]
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have e : ((2 + Real.log K) / Real.log 2 + C) * Real.log L =
      (2 * Real.log L + Real.log K * Real.log L) / Real.log 2 + C * Real.log L := by
    field_simp
  rw [e]
  have h1 : Real.log K ≤ Real.log K * Real.log L := le_mul_of_one_le_right hlogK hL
  have h2 : C ≤ C * Real.log L := le_mul_of_one_le_right hC hL
  have h3 : (Real.log L + (Real.log K + Real.log L)) / Real.log 2 ≤
      (2 * Real.log L + Real.log K * Real.log L) / Real.log 2 := by
    apply div_le_div_of_nonneg_right _ hlog2.le
    linarith
  calc Real.log L / Real.log 2 + (Real.log K / Real.log 2 + Real.log L / Real.log 2) + C
      = (Real.log L + (Real.log K + Real.log L)) / Real.log 2 + C := by ring
    _ ≤ _ := by linarith

/-- Lower form: if `log D' ≤ D · (log n)^(1-η)`, then
    `logb 2 (log n / (2 D')) ≥ (η/log 2) log log n - log (2D)/log 2`. -/
theorem logb_ratio_ge {η D D' Ln : ℝ} (hD : 0 < D) (hD' : 0 < D')
    (hLn : 1 < Ln) (hbound : D' ≤ D * Ln ^ (1 - η)) :
    η / Real.log 2 * Real.log Ln - Real.log (2 * D) / Real.log 2 ≤
      Real.logb 2 (Ln / (2 * D')) := by
  have hLnpos : 0 < Ln := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : 0 < Ln ^ (1 - η) := Real.rpow_pos_of_pos hLnpos _
  -- Ln / (2 D') ≥ Ln^η / (2 D)
  have hge : Ln ^ η / (2 * D) ≤ Ln / (2 * D') := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsplit : Ln = Ln ^ η * Ln ^ (1 - η) := by
      rw [← Real.rpow_add hLnpos]; simp
    calc Ln ^ η * (2 * D') ≤ Ln ^ η * (2 * (D * Ln ^ (1 - η))) := by gcongr
      _ = Ln ^ η * Ln ^ (1 - η) * (2 * D) := by ring
      _ = Ln * (2 * D) := by rw [← hsplit]
  have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hge
  have hval : Real.logb 2 (Ln ^ η / (2 * D)) =
      η / Real.log 2 * Real.log Ln - Real.log (2 * D) / Real.log 2 := by
    rw [Real.logb, Real.log_div (by positivity) (by positivity), Real.log_rpow hLnpos]
    ring
  linarith

end PGM
