import PLAStochastic.Index.CEPS.Scaled.EndpointZeroMark

/-! # An order-independent physical endpoint disc with square-root frequency scaling -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueEndpointScaleBase {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  min (dom.trueDenominatorScaleBase M) (Real.sqrt (cepsMarkedUnitRadius D θ))

def CepsCanonDomain.trueEndpointScaleRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) (z : ℂ) : ℝ :=
  dom.trueEndpointScaleBase M / (2 + Real.sqrt ‖z‖)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueEndpointScaleRadius_pos {M : ℝ} (hM : 0 ≤ M) (z : ℂ) :
    0 < dom.trueEndpointScaleRadius M z := by
  have := trueDenominatorScaleBase_pos dom hW hθ hD hM
  have := cepsMarkedUnitRadius_pos hD hθ
  unfold CepsCanonDomain.trueEndpointScaleRadius CepsCanonDomain.trueEndpointScaleBase
  positivity

theorem trueEndpointScaleRadius_le (M : ℝ) (z : ℂ) :
    dom.trueEndpointScaleRadius M z ≤ dom.trueDenominatorScaleRadius M 1 z := by
  simpa only [CepsCanonDomain.trueEndpointScaleRadius, CepsCanonDomain.trueEndpointScaleBase,
    CepsCanonDomain.trueDenominatorScaleRadius,
    abs_one, one_add_one_eq_two] using
      div_le_div_of_nonneg_right (min_le_left (dom.trueDenominatorScaleBase M)
        (Real.sqrt (cepsMarkedUnitRadius D θ))) (by positivity : 0 ≤ 2 + Real.sqrt ‖z‖)

include hθ hD in
theorem cepsScaledTrueEndpoint_mark_mem (M : ℝ) {z b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.trueEndpointScaleRadius M z)) :
    b ^ 2 * z ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ) := by
  have hp : 0 < 2 + Real.sqrt ‖z‖ := by positivity
  have ht := (lt_div_iff₀ hp).mp (mem_ball_zero_iff.mp hb)
  have hbase : dom.trueEndpointScaleBase M ≤ Real.sqrt (cepsMarkedUnitRadius D θ) := min_le_right _ _
  have hsmall : ‖b‖ * Real.sqrt ‖z‖ < Real.sqrt (cepsMarkedUnitRadius D θ) := by
    nlinarith [norm_nonneg b]
  have hR := cepsMarkedUnitRadius_pos hD hθ
  have hs := Real.sq_sqrt (norm_nonneg z)
  have hsR := Real.sq_sqrt hR.le
  have hs0 := Real.sqrt_nonneg ‖z‖
  have hsR0 := Real.sqrt_nonneg (cepsMarkedUnitRadius D θ)
  rw [mem_ball_zero_iff, norm_mul, norm_pow]
  nlinarith [mul_nonneg (norm_nonneg b) hs0]

include hW hθ hD in
theorem cepsScaledTrueEndpoint_curve_bounds (M : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueEndpointScaleRadius M z)) :
    |b| ≤ dom.μ₀ ∧ ‖cepsComplexScaledDiscount 1 z b‖ < dom.q₀ ∧
      (b : ℂ) ^ 2 * z ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ) := by
  have hbD := ball_subset_ball (trueEndpointScaleRadius_le dom M z) hb
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M 1 z) hbD
  have hbC := ball_subset_ball ((min_le_right _ _).trans
    (div_le_self (canonScaleRadius_pos dom hW hθ hD 1 z).le (by norm_num))) hbE
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD 1 hz (sign := 1) (by norm_num) hbC
  simp only [ofReal_one, mul_one, norm_real, Real.norm_eq_abs] at hμ
  exact ⟨by linarith [dom.μ₀_pos], hq.trans (half_lt_self dom.q₀_pos),
    cepsScaledTrueEndpoint_mark_mem dom hθ hD M hb⟩

include hW hθ hD in
theorem cepsScaledTrueEndpoint_eq_physical_on_disc (M : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : 0 < b) (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueEndpointScaleRadius M z)) :
    cepsScaledTrueRegularEndpoint dom ρW z b = cepsScaledMarkedEndpoint dom ρW b z := by
  obtain ⟨hμ, hq, ht⟩ := cepsScaledTrueEndpoint_curve_bounds dom hW hθ hD M hz hbs
  exact cepsScaledTrueRegularEndpoint_eq_filled_all_marks dom hW hθ hD hb hμ hq.le ht

end PGM
