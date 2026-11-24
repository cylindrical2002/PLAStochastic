import PLAStochastic.Affine.Extrema.Contact.LayerEvent

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Translation of a Borel endpoint set under Lebesgue integration. -/
theorem setLIntegral_translate_sub {S : Set ℝ} (hS : MeasurableSet S)
    (f : ℝ → ℝ≥0∞) (e : ℝ) :
    (∫⁻ z in (fun z => z-e) ⁻¹' S, f z) = ∫⁻ z in S, f (z+e) := by
  rw [← lintegral_indicator (hS.preimage (by fun_prop)),
    ← lintegral_add_right_eq_self _ e,← lintegral_indicator hS]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ S <;> simp [indicator,hz]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem killedBrownianMeasure_shifted_heatIntegral (hB : IsBrownianReal B μ)
    {a R e : ℝ} (hR : 0 < R) (ha : a ∈ Icc 0 R) {U : ℝ≥0} (hU : 0 < U)
    {S : Set ℝ} (hS : MeasurableSet S) (hSR : S ⊆ Icc (-e) (R-e)) :
    killedBrownianMeasure B μ a R U ((fun z => z-e) ⁻¹' S) =
      ∫⁻ z in S, ENNReal.ofReal (dirichletHeatKernel R U a (z+e)) := by
  have hshift : MeasurableSet ((fun z => z-e) ⁻¹' S) := hS.preimage (by fun_prop)
  have hsub : ((fun z => z-e) ⁻¹' S) ⊆ Icc 0 R := by
    intro z hz
    have hb := hSR hz
    constructor <;> linarith [hb.1,hb.2]
  rw [killedBrownianMeasure_apply_eq_heatIntegral hB hR ha hU hshift,
    Measure.restrict_restrict hshift,inter_eq_left.mpr hsub]
  exact setLIntegral_translate_sub hS _ e

/-- The true two-contact probability has the exact A0-Ar-K triple kernel on every
Borel pair of time windows and every Borel interior endpoint set. -/
theorem measure_orderedContactLayer_eq_heat_integral (hB : IsBrownianReal B μ)
    {x r e d : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (he : 0 < e) (hd : 0 < d)
    {T : ℝ≥0} (hT : 0 < T) {S D₁ D₂ : Set ℝ}
    (hS : MeasurableSet S) (hSr : S ⊆ Icc 0 r)
    (hD₁ : MeasurableSet D₁) (hD₂ : MeasurableSet D₂) :
    μ {ω | orderedContactLayerEvent B x r e d T S D₁ D₂ ω} =
      ∫⁻ s in D₁ ∩ Ioo (0 : ℝ) (T : ℝ), ENNReal.ofReal (heatBoundaryLeft r s x/2)*
        ∫⁻ v in D₂ ∩ Ioo (0 : ℝ) ((T : ℝ)-s), ENNReal.ofReal (heatBoundaryRight (r+e) v e/2)*
          ∫⁻ z in S, ENNReal.ofReal (dirichletHeatKernel (r+e+d) ((T : ℝ)-s-v) (r+e) (z+e)) := by
  rw [measure_orderedContactLayer_eq_double_convolution hB hr hx he hd hT hS hD₁ hD₂]
  apply setLIntegral_congr_fun (hD₁.inter measurableSet_Ioo)
  intro s hs
  dsimp only
  congr 1
  have hsN : Real.toNNReal s < T := by
    exact_mod_cast (show (Real.toNNReal s : ℝ) < (T : ℝ) by
      rw [Real.coe_toNNReal _ hs.2.1.le]
      exact hs.2.2)
  have hU : ((T-Real.toNNReal s : ℝ≥0) : ℝ)=(T : ℝ)-s := by
    rw [NNReal.coe_sub hsN.le,Real.coe_toNNReal _ hs.2.1.le]
  rw [hU]
  apply setLIntegral_congr_fun (hD₂.inter measurableSet_Ioo)
  intro v hv
  dsimp only
  congr 1
  have hvN : Real.toNNReal v < T-Real.toNNReal s := by
    exact_mod_cast (show (Real.toNNReal v : ℝ) < ((T-Real.toNNReal s : ℝ≥0) : ℝ) by
      rw [Real.coe_toNNReal _ hv.2.1.le,hU]
      exact hv.2.2)
  rw [killedBrownianMeasure_shifted_heatIntegral hB (by linarith)
    (show r+e ∈ Icc 0 (r+e+d) from ⟨by linarith,by linarith⟩)
    (tsub_pos_iff_lt.mpr hvN) hS (by
      intro z hz
      have hb := hSr hz
      constructor <;> linarith [hb.1,hb.2]),
    NNReal.coe_sub hvN.le,hU,Real.coe_toNNReal _ hv.2.1.le]

end BrownianAffine
