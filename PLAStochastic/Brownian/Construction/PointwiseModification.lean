import PLAStochastic.Brownian.Construction.DyadicPolygon

/-! Almost-sure convergence of the actual interpolants to every deterministic coordinate. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The lower dyadic vertex of a deterministic time. -/
def dyadicLower (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  dyadicTime n (⌊(2 : ℝ) ^ n * t⌋ : ℤ).toNat

def dyadicUpper (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  dyadicTime n ((⌊(2 : ℝ) ^ n * t⌋ : ℤ).toNat + 1)

theorem dyadic_bracket (n : ℕ) (t : ℝ≥0) :
    dyadicLower n t ≤ t ∧ t ≤ dyadicUpper n t := by
  have hk : 0 ≤ (⌊(2 : ℝ) ^ n * t⌋ : ℤ) := Int.floor_nonneg.mpr (by positivity)
  have hc : (((⌊(2 : ℝ) ^ n * t⌋ : ℤ).toNat : ℕ) : ℝ) = (⌊(2 : ℝ) ^ n * t⌋ : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hk
  constructor
  · change ((⌊(2 : ℝ) ^ n * t⌋ : ℤ).toNat : ℝ≥0) / 2 ^ n ≤ t
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast (hc ▸ (Int.floor_le ((2 : ℝ) ^ n * t))).trans_eq (mul_comm _ _)
  · unfold dyadicUpper dyadicTime
    rw [Nat.cast_add, Nat.cast_one, le_div_iff₀ (by positivity)]
    have hh : (t : ℝ) * 2 ^ n ≤ ((⌊(2 : ℝ) ^ n * t⌋ : ℤ).toNat : ℝ) + 1 := by
      rw [hc, mul_comm]
      exact (Int.lt_floor_add_one _).le
    exact_mod_cast hh

theorem dyadic_vertex_dist_le (n : ℕ) (t : ℝ≥0) :
    |(dyadicLower n t : ℝ) - t| ≤ 1 / (2 : ℝ) ^ n ∧
      |(dyadicUpper n t : ℝ) - t| ≤ 1 / (2 : ℝ) ^ n := by
  have hb := dyadic_bracket n t
  have hd := dyadicTime_step n (⌊(2 : ℝ) ^ n * t⌋ : ℤ).toNat
  change (dyadicUpper n t : ℝ) - dyadicLower n t = 1 / (2 : ℝ) ^ n at hd
  have hlo : (dyadicLower n t : ℝ) ≤ t := by exact_mod_cast hb.1
  have hhi : (t : ℝ) ≤ dyadicUpper n t := by exact_mod_cast hb.2
  rw [abs_of_nonpos (sub_nonpos.mpr hlo), abs_of_nonneg (sub_nonneg.mpr hhi)]
  constructor <;> linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem preBrownian_small_increment_measure_le (hB : IsPreBrownianReal B μ) (n : ℕ)
    (s t : ℝ≥0) (hd : |(s : ℝ) - t| ≤ 1 / (2 : ℝ) ^ n) :
    μ {ω | (7 / 8 : ℝ) ^ n ≤ |B s ω - B t ω|} ≤
      ENNReal.ofReal (3 * (1024 / 2401 : ℝ) ^ n) := by
  apply (preBrownian_measure_increment_ge hB s t (by positivity)).trans
  apply ENNReal.ofReal_le_ofReal
  have hp : ((s : ℝ) - t) ^ 2 ≤ (1 / (2 : ℝ) ^ n) ^ 2 := by
    rw [← sq_abs ((s : ℝ) - t)]
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  calc
    _ ≤ 3 * (1 / (2 : ℝ) ^ n) ^ 2 / ((7 / 8 : ℝ) ^ n) ^ 4 := by gcongr
    _ = _ := by
      have he : (1 / (2 : ℝ) ^ n) ^ 2 / ((7 / 8 : ℝ) ^ n) ^ 4 =
          ((1 / 2 : ℝ) ^ 2 / (7 / 8 : ℝ) ^ 4) ^ n := by
        conv_rhs => rw [div_pow]
        rw [← one_div_pow]
        simp only [← pow_mul, Nat.mul_comm]
      rw [mul_div_assoc, he]
      norm_num

/-- Dyadic approximation of each deterministic coordinate, proved by Borel--Cantelli. -/
theorem preBrownian_vertex_error_eventually_ae (hB : IsPreBrownianReal B μ)
    (s : ℕ → ℝ≥0) (t : ℝ≥0) (hd : ∀ n, |(s n : ℝ) - t| ≤ 1 / (2 : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, |B (s n) ω - B t ω| < (7 / 8 : ℝ) ^ n := by
  have hsum : (∑' n, μ {ω | (7 / 8 : ℝ) ^ n ≤ |B (s n) ω - B t ω|}) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum fun n =>
      preBrownian_small_increment_measure_le hB n (s n) t (hd n))
    exact ((summable_geometric_of_abs_lt_one (by norm_num : |(1024 / 2401 : ℝ)| < 1)).mul_left (3 : ℝ)).tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  exact lt_of_not_ge hn

omit [MeasurableSpace Ω] in
theorem dyadicPolygon_dist_vertex_le (n : ℕ) (t : ℝ≥0) (ω : Ω) (y a : ℝ)
    (hlo : |B (dyadicLower n t) ω - y| ≤ a)
    (hup : |B (dyadicUpper n t) ω - y| ≤ a) :
    |dyadicPolygon B n t ω - y| ≤ a := by
  have hk : 0 ≤ (⌊(2 : ℝ) ^ n * t⌋ : ℤ) := Int.floor_nonneg.mpr (by positivity)
  have hnat : (⌊(2 : ℝ) ^ n * t⌋ + 1 : ℤ).toNat = (⌊(2 : ℝ) ^ n * t⌋ : ℤ).toNat + 1 := by omega
  unfold dyadicPolygon
  apply realPolygon_dist_le
  · exact hlo
  · simpa only [hnat, dyadicUpper] using hup

/-- At every fixed time the interpolants converge almost surely to the original coordinate. -/
theorem preBrownian_polygon_tendsto_coordinate_ae (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => dyadicPolygon B n t ω) atTop (𝓝 (B t ω)) := by
  filter_upwards [preBrownian_vertex_error_eventually_ae hB (fun n => dyadicLower n t) t
      (fun n => (dyadic_vertex_dist_le n t).1),
    preBrownian_vertex_error_eventually_ae hB (fun n => dyadicUpper n t) t
      (fun n => (dyadic_vertex_dist_le n t).2)] with ω hlo hup
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(7 / 8 : ℝ)| < 1))
  filter_upwards [hlo, hup] with n hnlo hnup
  rw [Real.norm_eq_abs]
  exact dyadicPolygon_dist_vertex_le n t ω (B t ω) ((7 / 8 : ℝ) ^ n) hnlo.le hnup.le

end BrownianAffine
