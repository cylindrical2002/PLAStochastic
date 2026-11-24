import PLAStochastic.Affine.Extrema.Contact.Rescaling
import PLAStochastic.ForMathlib.MeasureTheory.Integral.RectangleAverage

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Positive first-contact time forces the initial point to lie inside the old interval. -/
theorem orderedContactLayer_initial_mem {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h0 : B 0 ω=0) {x r e d : ℝ} {T : ℝ≥0} {S D₁ D₂ : Set ℝ}
    (hE : orderedContactLayerEvent B x r e d T S D₁ D₂ ω) : x ∈ Ioo 0 r := by
  by_contra hx
  have ht : intervalTouchTime B x r ω=0 := by
    apply le_antisymm _ bot_le
    apply intervalTouchTime_le_of_outside (t := 0)
    simpa only [h0,add_zero] using hx
  have hs : intervalTouchClock B x r ω=0 := by
    rw [intervalTouchClock,ht]
    rfl
  have hp := hE.1.2.1
  rw [hs,NNReal.coe_zero] at hp
  exact (lt_irrefl (0 : ℝ)) hp

/-- Exact level support of the true layer, before discarding null rectangle edges. -/
theorem orderedContactLayer_level_support {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (h0 : B 0 ω=0) {l h e d : ℝ} (he : 0 < e) (hd : 0 < d)
    {S D₁ D₂ : Set ℝ} (hE : orderedContactLayerEvent B (-l) (h-l) e d 1 S D₁ D₂ ω) :
    slopeLower (unitPath (processPath B ω) 1) 0 ≤ l ∧
      l < slopeLower (unitPath (processPath B ω) 1) 0+e ∧
      slopeUpper (unitPath (processPath B ω) 1) 0-d < h ∧
      h ≤ slopeUpper (unitPath (processPath B ω) 1) 0 := by
  have hx := orderedContactLayer_initial_mem h0 hE
  have hr : 0 < h-l := hx.1.trans hx.2
  have hrct := orderedContactLayer_extrema_rectangle hc hr he hd hE
  exact ⟨by linarith [hrct.2.1],by linarith [hrct.1],
    by linarith [hrct.2.2.2],by linarith [hrct.2.2.1]⟩

/-- Outside the extremal rectangle, except for its two null edges, every true layer test is zero. -/
theorem orderedContactTest_eq_zero_outside_rectangle {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω)) (h0 : B 0 ω=0)
    {l h e d : ℝ} (he : 0 < e) (hd : 0 < d)
    (hl : l ≠ slopeLower (unitPath (processPath B ω) 1) 0)
    (hh : h ≠ slopeUpper (unitPath (processPath B ω) 1) 0)
    (hout : l ∉ Ioo (slopeLower (unitPath (processPath B ω) 1) 0)
        (slopeLower (unitPath (processPath B ω) 1) 0+e) ∨
      h ∉ Ioo (slopeUpper (unitPath (processPath B ω) 1) 0-d)
        (slopeUpper (unitPath (processPath B ω) 1) 0))
    (φ : ExtremaVector → ℝ) : orderedContactTest φ B (-l) (h-l) e d ω=0 := by
  apply if_neg
  intro hE
  have hs := orderedContactLayer_level_support hc h0 he hd hE
  rcases hout with hlout | hhout
  · exact hlout ⟨lt_of_le_of_ne hs.1 hl.symm,hs.2.1⟩
  · exact hhout ⟨hs.2.2.1,lt_of_le_of_ne hs.2.2.2 hh⟩

/-- The full nonnegative level integral equals its restriction to the small
extremal rectangle; the removed boundary levels are Lebesgue null. -/
theorem lintegral_orderedContactTest_eq_rectangle {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω)) (h0 : B 0 ω=0)
    {e d : ℝ} (he : 0 < e) (hd : 0 < d) (φ : ExtremaVector → ℝ) :
    (∫⁻ l : ℝ, ∫⁻ h : ℝ, ENNReal.ofReal (orderedContactTest φ B (-l) (h-l) e d ω)) =
      ∫⁻ l in Ioo (slopeLower (unitPath (processPath B ω) 1) 0)
        (slopeLower (unitPath (processPath B ω) 1) 0+e),
      ∫⁻ h in Ioo (slopeUpper (unitPath (processPath B ω) 1) 0-d)
        (slopeUpper (unitPath (processPath B ω) 1) 0),
        ENNReal.ofReal (orderedContactTest φ B (-l) (h-l) e d ω) := by
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr_ae
  filter_upwards [volume.ae_ne (slopeLower (unitPath (processPath B ω) 1) 0)] with l hl
  by_cases hlI : l ∈ Ioo (slopeLower (unitPath (processPath B ω) 1) 0)
      (slopeLower (unitPath (processPath B ω) 1) 0+e)
  · rw [indicator_of_mem hlI,←lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr_ae
    filter_upwards [volume.ae_ne (slopeUpper (unitPath (processPath B ω) 1) 0)] with h hh
    by_cases hhI : h ∈ Ioo (slopeUpper (unitPath (processPath B ω) 1) 0-d)
        (slopeUpper (unitPath (processPath B ω) 1) 0)
    · rw [indicator_of_mem hhI]
    · rw [indicator_of_notMem hhI,
        orderedContactTest_eq_zero_outside_rectangle hc h0 he hd hl hh (Or.inr hhI) φ,
        ENNReal.ofReal_zero]
  · rw [indicator_of_notMem hlI]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [volume.ae_ne (slopeUpper (unitPath (processPath B ω) 1) 0)] with h hh
    rw [orderedContactTest_eq_zero_outside_rectangle hc h0 he hd hl hh (Or.inl hlI) φ,
      ENNReal.ofReal_zero]
    rfl

/-- The normalized actual level integral is exactly its rescaled unit-square
average, pathwise. This is an equality before taking any small-layer limit. -/
theorem lintegral_orderedContactTest_normalized_eq_rescaled {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω)) (h0 : B 0 ω=0)
    {e d : ℝ} (he : 0 < e) (hd : 0 < d) (φ : ExtremaVector → ℝ) :
    (∫⁻ l : ℝ, ∫⁻ h : ℝ, ENNReal.ofReal (orderedContactTest φ B (-l) (h-l) e d ω)) /
        (ENNReal.ofReal e*ENNReal.ofReal d) =
      ∫⁻ a in Ioo (0 : ℝ) 1, ∫⁻ b in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (rescaledOrderedContactTest φ B e d a b ω) := by
  rw [lintegral_orderedContactTest_eq_rectangle hc h0 he hd φ]
  exact setLIntegral_rectangle_average _ _ _ he hd

end BrownianAffine
