import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.LimitRewardBounds

/-! # `γ_Swing`: the explicit form, finiteness and strict positivity

`stationaryLeadingCoefficient` is defined as an integral of
`marginLeadingReward`, which is `4 V` on the positive half-line and `0`
elsewhere.  The paper's coefficient is

`γ_Swing = 4 ∫_{(0,∞)} V(r) ν_∞(dr) ∈ (0,∞)`.

This file proves that the library object is exactly that integral, that the
integrand is genuinely integrable (so the value is not Lean's default for a
non-integrable function), that it is bounded above by an explicit finite
constant, and that it is strictly positive.

Positivity is *not* deduced from nonnegativity.  It uses the pointwise lower
bound `V(r) ≥ r` on a fixed interval `(1,2)` of positive limit mass; the mass is
positive because Lebesgue measure is absolutely continuous with respect to the
limit law, which is the second conclusion of Theorem 4.3.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
namespace LeadingCoefficient

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The renewal potential dominates its argument -/

/-- `V(w) = w + E O_w ≥ w`: the overshoot term is a nonnegative expectation.
This is the pointwise input for strict positivity of `γ`. -/
theorem le_gaussianRenewalPotential
    (hi : iIndepFun X μ) (w : ℝ) :
    w ≤ gaussianRenewalPotential X μ w := by
  let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hnon : 0 ≤ ∫ ω, gaussianHalfLineOvershoot X w 0 ω ∂μ :=
    integral_nonneg (μ := μ) (f := fun ω => gaussianHalfLineOvershoot X w 0 ω)
      (fun ω => gaussianHalfLineOvershoot_nonneg X w 0 ω)
  unfold gaussianRenewalPotential
  linarith

/-! ### The explicit integral representation -/

theorem marginLeadingReward_eq_indicator (X : ℕ → Ω → ℝ) (μ : Measure Ω) :
    marginLeadingReward X μ =
      Set.indicator (Ioi (0 : ℝ))
        (fun r => 4 * gaussianRenewalPotential X μ r) := by
  funext r
  by_cases hr : (0 : ℝ) < r
  · rw [marginLeadingReward, if_pos hr,
      Set.indicator_of_mem (by exact hr : r ∈ Ioi (0 : ℝ))]
  · rw [marginLeadingReward, if_neg hr,
      Set.indicator_of_notMem (by simpa using hr)]

/-- `γ = 4 ∫_{(0,∞)} V dν`, exactly the paper's `eq:leadingcoefficient`. -/
theorem stationaryLeadingCoefficient_eq (X : ℕ → Ω → ℝ) (μ : Measure Ω)
    (ν : Measure ℝ) :
    stationaryLeadingCoefficient X μ ν =
      4 * ∫ r in Ioi (0 : ℝ), gaussianRenewalPotential X μ r ∂ν := by
  rw [stationaryLeadingCoefficient, marginLeadingReward_eq_indicator,
    integral_indicator measurableSet_Ioi, integral_const_mul]

/-! ### Integrability, finiteness and positivity -/

/-- `V` itself is integrable on the positive half-line against the limit law.
Without this the previous identity could be an equality of two default values. -/
theorem gaussianRenewalPotential_integrableOn_Ioi
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hνabs : Integrable (fun r : ℝ => |r|) ν) :
    IntegrableOn (gaussianRenewalPotential X μ) (Ioi (0 : ℝ)) ν := by
  have hint : Integrable (marginLeadingReward X μ) ν :=
    marginLeadingReward_integrable_of_abs_integrable hX hi hG hνabs
  rw [marginLeadingReward_eq_indicator] at hint
  have h4 := (integrable_indicator_iff (μ := ν) measurableSet_Ioi).mp hint
  have hscaled := h4.const_mul (4 : ℝ)⁻¹
  refine hscaled.congr ?_
  filter_upwards [] with r
  field_simp

/-- An explicit finite upper bound: `γ ≤ 4 (C + ∫|r| dν)`.  Together with the
integrability above this is the `γ < ∞` half of `eq:leadingcoefficient`. -/
theorem stationaryLeadingCoefficient_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hνabs : Integrable (fun r : ℝ => |r|) ν) :
    stationaryLeadingCoefficient X μ ν ≤
      4 * (gaussianExcessExpMomentBound 2 + ∫ r, |r| ∂ν) := by
  have hint : Integrable (marginLeadingReward X μ) ν :=
    marginLeadingReward_integrable_of_abs_integrable hX hi hG hνabs
  have hdom : Integrable
      (fun r : ℝ => 4 * (gaussianExcessExpMomentBound 2 + |r|)) ν := by
    have hsum := (integrable_const
      ((4 : ℝ) * gaussianExcessExpMomentBound 2)).add (hνabs.const_mul 4)
    refine hsum.congr ?_
    filter_upwards [] with r
    simp only [Pi.add_apply]
    ring
  have hpt : ∀ r : ℝ, marginLeadingReward X μ r ≤
      4 * (gaussianExcessExpMomentBound 2 + |r|) := by
    intro r
    have hm := marginLeadingReward_le_linear hX hi hG (r := r)
    have hmax : max r 0 ≤ |r| := max_le (le_abs_self r) (abs_nonneg r)
    calc
      marginLeadingReward X μ r ≤
          4 * (max r 0 + gaussianExcessExpMomentBound 2) := hm
      _ ≤ 4 * (gaussianExcessExpMomentBound 2 + |r|) := by linarith
  calc
    stationaryLeadingCoefficient X μ ν
        = ∫ r, marginLeadingReward X μ r ∂ν := rfl
    _ ≤ ∫ r, 4 * (gaussianExcessExpMomentBound 2 + |r|) ∂ν :=
      integral_mono hint hdom hpt
    _ = 4 * (gaussianExcessExpMomentBound 2 + ∫ r, |r| ∂ν) := by
      rw [integral_const_mul, integral_add (integrable_const _) hνabs,
        integral_const]
      simp

/-- `γ > 0`.  The witness is the fixed interval `(1,2)`, on which
`4 V(r) ≥ 4 r > 4`; its limit mass is positive because Lebesgue measure is
absolutely continuous with respect to the limit law. -/
theorem stationaryLeadingCoefficient_pos
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hνabs : Integrable (fun r : ℝ => |r|) ν)
    (hca : (volume : Measure ℝ) ≪ ν) :
    0 < stationaryLeadingCoefficient X μ ν := by
  have hint : Integrable (marginLeadingReward X μ) ν :=
    marginLeadingReward_integrable_of_abs_integrable hX hi hG hνabs
  have hmass : 0 < ν.real (Ioo (1 : ℝ) 2) := by
    have hne : ν (Ioo (1 : ℝ) 2) ≠ 0 := by
      intro h0
      have hvol : (volume : Measure ℝ) (Ioo (1 : ℝ) 2) = 0 := hca h0
      rw [Real.volume_Ioo] at hvol
      norm_num at hvol
    exact ENNReal.toReal_pos hne (measure_ne_top ν _)
  have hg : Integrable
      (Set.indicator (Ioo (1 : ℝ) 2) (fun _ : ℝ => (4 : ℝ))) ν :=
    (integrable_const (4 : ℝ)).indicator measurableSet_Ioo
  have hpt : ∀ r : ℝ,
      Set.indicator (Ioo (1 : ℝ) 2) (fun _ : ℝ => (4 : ℝ)) r ≤
        marginLeadingReward X μ r := by
    intro r
    by_cases hr : r ∈ Ioo (1 : ℝ) 2
    · rw [Set.indicator_of_mem hr]
      have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr.1
      rw [marginLeadingReward, if_pos hr0]
      have hV : r ≤ gaussianRenewalPotential X μ r := le_gaussianRenewalPotential hi r
      nlinarith [hr.1]
    · rw [Set.indicator_of_notMem hr]
      exact marginLeadingReward_nonneg hX hi hG
  have hlow : (4 : ℝ) * ν.real (Ioo (1 : ℝ) 2) ≤
      stationaryLeadingCoefficient X μ ν := by
    have hmono := integral_mono hg hint hpt
    rw [integral_indicator_const _ measurableSet_Ioo] at hmono
    rw [stationaryLeadingCoefficient]
    simpa [smul_eq_mul, mul_comm] using hmono
  have : (0 : ℝ) < 4 * ν.real (Ioo (1 : ℝ) 2) := by positivity
  linarith

end LeadingCoefficient
end SwingRepair
