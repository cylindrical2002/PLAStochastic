import PLAStochastic.Index.CEPS.Scaled.EndpointScaleLimit
import PLAStochastic.Index.CEPS.Normal.ZeroDiscountRoots

/-! # Zero mark in the actual regular endpoint -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueRegularEndpoint_zero_mark {b : ℝ} (hb : 0 < b)
    (hμ : |b| ≤ dom.μ₀) : cepsScaledTrueRegularEndpoint dom ρW 0 b = 1 := by
  have hb0 : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have hμc : ‖((b * 1 : ℝ) : ℂ)‖ < cepsChartMu D θ := by
    simpa only [mul_one] using dom.μ_lt_chart (by simpa only [norm_real, Real.norm_eq_abs] using hμ)
  obtain ⟨hp0, hm0⟩ := cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hb
  have hp : cepsScaledSignedRoot D θ ρW 1 0 1 b = 0 := by
    rw [cepsScaledSignedRoot_plus_actual hW hθ hD hb hμc]
    simp only [cepsScaledDiscount, mul_zero, zero_mul, mul_one, hp0, zero_div]
  have hm : cepsScaledSignedRoot D θ ρW 1 0 (-1) b ≠ 0 := by
    rw [cepsScaledSignedRoot_minus_actual hW hθ hD hb hμc]
    simp only [cepsScaledDiscount, mul_zero, zero_mul, mul_one]
    exact div_ne_zero (by intro he; rw [he, zero_re] at hm0; exact (lt_irrefl _ hm0)) hb0
  let L := dom.canonL ρW b 0 0
  have hQ := CepsC6.cepsQ_ne_zero dom hW hθ hD hμ (q := 0) (z := 0)
    (by simpa using dom.q₀_pos.le) (by simp only [zero_re, abs_zero]; linarith [dom.c₀_pos])
  have hexp : exp (2 * L) * exp (-(2 * L)) = 1 := by rw [← exp_add]; simp
  rw [cepsScaledTrueRegularEndpoint_eq_factors]
  unfold cepsScaledTrueDoubleMarkPrefactor cepsScaledTrueG cepsCanonTrueWeight cepsScaledEndpointCarrier
  simp only [hp, neg_zero, mul_zero, zero_mul, cepsComplexScaledDiscount, exp_zero, one_mul, mul_one,
    ofReal_one, zero_sub, div_self (neg_ne_zero.mpr hm)]
  change exp (2 * L) / cepsQ D θ ρW b 0 0 * (cepsQ D θ ρW b 0 0 * exp (-2 * L)) = 1
  simp only [neg_mul]
  field_simp [hQ]
  exact hexp

include hW hθ hD in
theorem cepsScaledTrueRegularEndpoint_eq_filled_all_marks {b : ℝ} (hb : 0 < b)
    (hμ : |b| ≤ dom.μ₀) {z : ℂ}
    (hq : ‖cepsComplexScaledDiscount 1 z b‖ ≤ dom.q₀)
    (ht : (b : ℂ) ^ 2 * z ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ)) :
    cepsScaledTrueRegularEndpoint dom ρW z b = cepsScaledMarkedEndpoint dom ρW b z := by
  by_cases hz : z = 0
  · subst z
    rw [cepsScaledTrueRegularEndpoint_zero_mark dom hW hθ hD hb hμ,
      cepsScaledMarkedEndpoint_zero]
  · exact cepsScaledTrueRegularEndpoint_eq_filled dom hW hθ hD hb hμ hz hq ht

end PGM
