import PLAStochastic.Swing.FrozenCarry.Interior.Coefficient

/-! Compact-uniform exact interior tail coefficient for the actual maximal frozen Gaussian prefix. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem frozenScaledTail_interior_uniform
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ : ℝ} (hδ : 0 < δ) {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ici 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ E : ℝ in atTop, ∀ n : ℕ, frozenInteriorWindow δ E n → ∀ w ∈ K,
      |frozenScaledTail X μ w E n-4*gaussianRenewalPotential X μ w| < ε := by
  obtain ⟨W0, hW0⟩ := hK.bddAbove_image (f := fun w : ℝ => |w|) continuous_abs.continuousOn
  let W := max W0 0
  have hW : 0 ≤ W := le_max_right _ _
  have hwbound : ∀ w ∈ K, |w| ≤ W := fun w hw => (hW0 ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  obtain ⟨M0, hM0⟩ := hK.bddAbove_image
    ((gaussianRenewalPotential_continuousOn hX hi hG).mono hK0).abs
  let M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hVbound : ∀ w ∈ K, |gaussianRenewalPotential X μ w| ≤ M :=
    fun w hw => (hM0 ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  let r := min (1/2 : ℝ) (ε/(16*(M+1)))
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hr1 : r ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hrM : 2*r*M ≤ ε/8 := by
    have hrr : r ≤ ε/(16*(M+1)) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0 < 16*(M+1) by positivity)).mp hrr
    nlinarith
  have hsmall := (Metric.tendstoUniformlyOn_iff.mp
    (gaussianInfiniteSurvival_small_drift_uniform hX hi hG hK hK0)) (ε/32) (by positivity)
  obtain ⟨a0, ha0, ha⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  have hdrift : ∀ᶠ E : ℝ in atTop, 3*E^(-δ) < min a0 1 := by
    have ht := (tendsto_rpow_neg_atTop hδ).const_mul (3 : ℝ)
    have hm : 0 < min a0 1 := lt_min ha0 zero_lt_one
    simp only [mul_zero] at ht
    exact ht.eventually (Iio_mem_nhds hm)
  have hbad : ∀ᶠ E : ℝ in atTop, 2*E^3*Real.exp (-(r^2/8)*E^δ) < ε/4 := by
    have ht := (frozen_polynomial_exp_rpow_tendsto_zero 3 (by positivity : 0 < r^2/8) hδ).const_mul 2
    simp only [mul_zero] at ht
    simpa only [mul_assoc] using ht.eventually (Iio_mem_nhds (show 0 < ε/4 by positivity))
  have hrem : ∀ᶠ E : ℝ in atTop,
      gaussianBallotConstant*(W+2)*E*Real.exp (-E^δ) < ε/4 := by
    have ht := (frozen_polynomial_exp_rpow_tendsto_zero 1 (by norm_num : (0 : ℝ) < 1) hδ).const_mul
      (gaussianBallotConstant*(W+2))
    simp only [mul_zero] at ht
    simpa only [pow_one, neg_one_mul, mul_assoc] using
      ht.eventually (Iio_mem_nhds (show 0 < ε/4 by positivity))
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (2*W/r), hdrift, hbad, hrem]
    with E hE hEW hEd hEb hEr
  intro n hn w hw
  have hEp : 0 < E := by linarith
  have hnp : (0 : ℝ) < n := lt_of_lt_of_le hEp
    (frozenInteriorWindow_ge_budget (by linarith : 1 ≤ E) hδ.le hn)
  have hwb : 2*|w| ≤ r*E := by
    have hh := (div_le_iff₀ hr).mp hEW
    nlinarith [hwbound w hw]
  have hap : 0 < (2+r)*E/(n : ℝ) := by positivity
  have ham : 0 < (2-r)*E/(n : ℝ) := by
    have : 0 < 2-r := by linarith
    positivity
  have hapb : (2+r)*E/(n : ℝ) < min a0 1 := by
    calc
      _ ≤ 3*E^(-δ) := (frozenInteriorWindow_drift_le (by linarith : 1 ≤ E) hδ.le
        (by positivity : 0 ≤ 2+r) hn).trans (by gcongr; linarith)
      _ < _ := hEd
  have hamb : (2-r)*E/(n : ℝ) < a0 := by
    have hh : (2-r)*E/(n : ℝ) ≤ (2+r)*E/(n : ℝ) := by gcongr; linarith
    exact hh.trans_lt (hapb.trans_le (min_le_left _ _))
  have hpm := ha ⟨ham, hamb⟩ w hw
  have hpp := ha ⟨hap, hapb.trans_le (min_le_left _ _)⟩ w hw
  simp only [Real.dist_eq] at hpm hpp
  rw [abs_sub_comm] at hpm hpp
  have hmain := frozenInterior_scaled_error_bound hX hi hG hE hr hr1 hδ.le hn (hK0 hw) hwb
    (by positivity : 0 ≤ ε/32) hpm.le hpp.le
  have hVr : 2*r*|gaussianRenewalPotential X μ w| ≤ 2*r*M :=
    mul_le_mul_of_nonneg_left (hVbound w hw) (by positivity)
  have hη : (4+2*r)*(ε/32) ≤ 6*(ε/32) := by gcongr; linarith
  have hactualrem : gaussianBallotConstant*(w+(2+r)*E/n+1)*E*Real.exp (-((2+r)^2/4)*E^δ) ≤
      gaussianBallotConstant*(W+2)*E*Real.exp (-E^δ) := by
    have hwW : w ≤ W := (le_abs_self w).trans (hwbound w hw)
    have haa : (2+r)*E/(n : ℝ) ≤ 1 := (hapb.trans_le (min_le_right _ _)).le
    have hexp : -((2+r)^2/4)*E^δ ≤ -E^δ := by
      have hh := Real.rpow_nonneg hEp.le δ
      have hc : 1 ≤ (2+r)^2/4 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hc hh]
    have hC := gaussianBallotConstant_pos
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_right _ hEp.le
      exact mul_le_mul_of_nonneg_left (by linarith : w+(2+r)*E/n+1 ≤ W+2) hC.le
    · exact Real.exp_le_exp.mpr hexp
    · positivity
    · positivity
  linarith

end SwingRepair
