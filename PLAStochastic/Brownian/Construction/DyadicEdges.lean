import PLAStochastic.Brownian.Construction.KolmogorovCondition
import Mathlib.Analysis.SpecificLimits.Basic

/-! Summable bad dyadic-edge probabilities and actual Borel--Cantelli path bounds. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def dyadicTime (n k : ℕ) : ℝ≥0 := k / (2 : ℝ≥0) ^ n

theorem dyadicTime_step (n k : ℕ) :
    (dyadicTime n (k + 1) : ℝ) - dyadicTime n k = 1 / (2 : ℝ) ^ n := by
  simp only [dyadicTime, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat,
    Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The probability of one bad dyadic edge has a geometric fourth-moment bound. -/
theorem preBrownian_dyadic_edge_measure_le (hB : IsPreBrownianReal B μ) (n k : ℕ) :
    μ {ω | (7 / 8 : ℝ) ^ n ≤ |B (dyadicTime n (k + 1)) ω - B (dyadicTime n k) ω|} ≤
      ENNReal.ofReal (3 * (1024 / 2401 : ℝ) ^ n) := by
  have h := preBrownian_measure_increment_ge hB (dyadicTime n (k + 1)) (dyadicTime n k)
    (pow_pos (by norm_num : (0 : ℝ) < 7 / 8) n)
  rw [dyadicTime_step] at h
  convert h using 1
  congr 1
  have he : (1 / (2 : ℝ) ^ n) ^ 2 / ((7 / 8 : ℝ) ^ n) ^ 4 =
      ((1 / 2 : ℝ) ^ 2 / (7 / 8 : ℝ) ^ 4) ^ n := by
    conv_rhs => rw [div_pow]
    rw [← one_div_pow]
    simp only [← pow_mul, Nat.mul_comm]
  rw [mul_div_assoc, he]
  norm_num

/-- At level `n`, at least one dyadic edge before `K` exceeds the regularity threshold. -/
def dyadicBadEvent (B : ℝ≥0 → Ω → ℝ) (K n : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range (K * 2 ^ n),
    {ω | (7 / 8 : ℝ) ^ n ≤ |B (dyadicTime n (k + 1)) ω - B (dyadicTime n k) ω|}

theorem preBrownian_dyadicBadEvent_measure_le (hB : IsPreBrownianReal B μ) (K n : ℕ) :
    μ (dyadicBadEvent B K n) ≤ ENNReal.ofReal (3 * K * (2048 / 2401 : ℝ) ^ n) := by
  calc
    _ ≤ ∑ k ∈ Finset.range (K * 2 ^ n),
        μ {ω | (7 / 8 : ℝ) ^ n ≤ |B (dyadicTime n (k + 1)) ω - B (dyadicTime n k) ω|} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range (K * 2 ^ n), ENNReal.ofReal (3 * (1024 / 2401 : ℝ) ^ n) :=
      Finset.sum_le_sum fun k _ => preBrownian_dyadic_edge_measure_le hB n k
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      have he : (2048 / 2401 : ℝ) ^ n = 2 ^ n * (1024 / 2401 : ℝ) ^ n := by
        rw [← mul_pow]
        norm_num
      rw [he, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

/-- The bad dyadic levels have summable probabilities on every bounded interval. -/
theorem preBrownian_dyadicBadEvent_tsum_ne_top (hB : IsPreBrownianReal B μ) (K : ℕ) :
    (∑' n, μ (dyadicBadEvent B K n)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum fun n => preBrownian_dyadicBadEvent_measure_le hB K n)
  apply Summable.tsum_ofReal_ne_top
  exact (summable_geometric_of_abs_lt_one (by norm_num : |(2048 / 2401 : ℝ)| < 1)).mul_left (3 * (K : ℝ))

/-- Almost every path has uniformly small dyadic edges at all sufficiently fine levels. -/
theorem preBrownian_dyadic_edges_eventually_ae (hB : IsPreBrownianReal B μ) (K : ℕ) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ k < K * 2 ^ n,
      |B (dyadicTime n (k + 1)) ω - B (dyadicTime n k) ω| < (7 / 8 : ℝ) ^ n := by
  filter_upwards [ae_eventually_notMem (preBrownian_dyadicBadEvent_tsum_ne_top hB K)] with ω hω
  filter_upwards [hω] with n hn k hk
  apply lt_of_not_ge
  intro he
  exact hn (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨Finset.mem_range.mpr hk, he⟩⟩)

/-- The same full-measure event works simultaneously for every integer time horizon. -/
theorem preBrownian_dyadic_edges_all_horizons_ae (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ K : ℕ, ∀ᶠ n in atTop, ∀ k < K * 2 ^ n,
      |B (dyadicTime n (k + 1)) ω - B (dyadicTime n k) ω| < (7 / 8 : ℝ) ^ n :=
  ae_all_iff.mpr (preBrownian_dyadic_edges_eventually_ae hB)

end BrownianAffine
