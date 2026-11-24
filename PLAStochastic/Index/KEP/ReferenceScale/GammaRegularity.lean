import PLAStochastic.Index.KEP.ReferenceScale.GammaDensity
import PLAStochastic.Index.KEP.ReferenceScale.LawOrbit
import PLAStochastic.Index.KEP.ReferenceScale.MeanSpan
import PLAStochastic.ForMathlib.Probability.Distributions.GammaMixtureScale

/-!
# Finite classical second derivatives on the actual reference-law orbit

The density is identified with the existing actual normalised `lawPhi` orbit.
All positive layers have two continuous classical derivatives and finite L1
norms. The initial unweighted second-derivative budget is polynomial in epsilon;
the later bounds still depend on the layer mean scale.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepReferenceWeights (eps : ℝ) (j : ℕ) : ℕ → ℝ :=
  gammaCountWeights expSeqMeasure (epLayerSeq eps expCoord j)

theorem kepReferenceWeights_nonneg (eps : ℝ) (j n : ℕ) : 0 ≤ kepReferenceWeights eps j n :=
  gammaCountWeights_nonneg n

theorem kepReferenceWeights_summable {eps : ℝ} (heps : 2 ≤ eps) {j : ℕ} (hj : 1 ≤ j) :
    Summable (kepReferenceWeights eps j) :=
  summable_gammaCountWeights
    ((gammaClosure_epLayerSeq iidSeq_expCoord (hasLaw_expCoord 0) (by linarith : 0 ≤ eps) j).1.measurable 0)
    (ae_reference_count_ge_four heps hj)

theorem kepReferenceWeights_sum {eps : ℝ} (heps : 2 ≤ eps) {j : ℕ} (hj : 1 ≤ j) :
    (∑' n, kepReferenceWeights eps j n) = 1 :=
  tsum_gammaCountWeights
    ((gammaClosure_epLayerSeq iidSeq_expCoord (hasLaw_expCoord 0) (by linarith : 0 ≤ eps) j).1.measurable 0)
    (ae_reference_count_ge_four heps hj)

def kepReferenceClassicalThreshold : ℝ :=
  max 2 (epsZero (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))))

theorem kepReferenceSpan_pos {eps : ℝ} (heps : kepReferenceClassicalThreshold ≤ eps) (j : ℕ) :
    0 < kepReferenceSpan eps j := by
  have he : epsZero (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))) ≤ eps :=
    (le_max_right _ _).trans heps
  have h := layerOK_all (layerOK_input gapLaw_expCoord) (bAbs_le_bIn 1 1)
    (βAbs_le_βIn _ _) (vIn_pos one_pos one_pos) (vIn_le 1 1) KcAbs_le_KcIn he j
  exact h.1.cnt_pos

def kepReferenceDensity {eps : ℝ} (heps : kepReferenceClassicalThreshold ≤ eps)
    {j : ℕ} (hj : 1 ≤ j) : HellingerDensity (volume : Measure ℝ) :=
  gammaScaledHellinger (kepReferenceWeights_nonneg eps j)
    (kepReferenceWeights_summable ((le_max_left _ _).trans heps) hj)
    (kepReferenceWeights_sum ((le_max_left _ _).trans heps) hj)
    (kepReferenceSpan_pos heps j)

theorem kepReferenceDensity_density {eps : ℝ} (heps : kepReferenceClassicalThreshold ≤ eps)
    {j : ℕ} (hj : 1 ≤ j) :
    (kepReferenceDensity heps hj).density =
      gammaScaledMixture (kepReferenceWeights eps j) (kepReferenceSpan eps j) :=
  gammaScaledHellinger_density _ _ _ _

theorem kepReferenceDensity_toMeasure {eps : ℝ} (heps : kepReferenceClassicalThreshold ≤ eps)
    {j : ℕ} (hj : 1 ≤ j) :
    (kepReferenceDensity heps hj).toMeasure = (kepReferenceLaw eps j : Measure ℝ) := by
  have heps2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have heps0 : 0 ≤ eps := by linarith
  have he : epsZero (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))) ≤ eps :=
    (le_max_right _ _).trans heps
  have hraw : (gammaMixtureHellinger (kepReferenceWeights_nonneg eps j)
      (kepReferenceWeights_summable heps2 hj) (kepReferenceWeights_sum heps2 hj)).toMeasure =
      expSeqMeasure.map (fun ω => (epLayerSeq eps expCoord j 0 ω).1) :=
    kepReferenceRawDensity_toMeasure heps2 hj
  rw [kepReferenceDensity, gammaScaledHellinger_toMeasure, hraw,
    Measure.map_map (show Measurable (fun x : ℝ => x / kepReferenceSpan eps j) from
      measurable_id.div_const _) (measurable_epLayerSeq_entry
      (fun i => measurable_expCoord i) eps j 0).fst]
  have horbit := (layer_law_orbit gapLaw_expCoord he expPM (by
    change expMeasure 1 = expSeqMeasure.map (fun ω => expCoord 0 ω / 1)
    simpa only [div_one] using (hasLaw_expCoord 0).map_eq.symm) j).1
  rw [kepReferenceSpan_eq_mean_gap heps0 j]
  exact horbit.symm

theorem kepReferenceDensity_classical {eps : ℝ} (heps : kepReferenceClassicalThreshold ≤ eps)
    {j : ℕ} (hj : 1 ≤ j) :
    let p := kepReferenceDensity heps hj
    let p' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    let p'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    (∀ x, x ≤ 0 → p.density x = 0) ∧
      (∀ x, HasDerivAt p.density (p' x) x) ∧ (∀ x, HasDerivAt p' (p'' x) x) ∧
      Continuous p'' ∧ Integrable p' volume ∧ Integrable p'' volume ∧
      (∫ x, |p' x|) ≤ 2 * kepReferenceSpan eps j ∧
      (∫ x, |p'' x|) ≤ 4 * (kepReferenceSpan eps j) ^ 2 := by
  have heps2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hp := kepReferenceWeights_summable heps2 hj
  have hp0 := kepReferenceWeights_nonneg eps j
  have hp1 := kepReferenceWeights_sum heps2 hj
  have hm := kepReferenceSpan_pos heps j
  dsimp only
  rw [kepReferenceDensity_density heps hj]
  refine ⟨?_, hasDerivAt_gammaScaledMixture hp0 hp _ , hasDerivAt_gammaScaledFirst hp0 hp _,
    continuous_gammaScaledSecond hp0 hp _, integrable_gammaScaledFirst hp0 hp hm,
    integrable_gammaScaledSecond hp0 hp hm, integral_abs_gammaScaledFirst_le hp0 hp hp1 hm,
    integral_abs_gammaScaledSecond_le hp0 hp hp1 hm⟩
  intro x hx
  unfold gammaScaledMixture
  rw [gammaMixtureDensity_succ_of_nonpos _ 2 (mul_nonpos_of_nonneg_of_nonpos hm.le hx), mul_zero]

theorem kepReferenceSpan_one_le {eps : ℝ} (heps : kepReferenceClassicalThreshold ≤ eps) :
    kepReferenceSpan eps 1 ≤ cBr (bIn 1 1) (vIn 1 1) * eps ^ 2 := by
  have he : epsZero (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))) ≤ eps :=
    (le_max_right _ _).trans heps
  have h := layerOK_all (layerOK_input gapLaw_expCoord) (bAbs_le_bIn 1 1)
    (βAbs_le_βIn _ _) (vIn_pos one_pos one_pos) (vIn_le 1 1) KcAbs_le_KcIn he 0
  have hm : kepReferenceSpan eps 1 = segMean expSeqMeasure eps (epLayerSeq eps expCoord 0) := by
    change lcount expSeqMeasure (epLayerSeq eps expCoord (0 + 1)) = _
    rw [h.2.2.1]
    have hzero : lcount expSeqMeasure (epLayerSeq eps expCoord 0) = 1 :=
      meanSpan_zero expSeqMeasure eps expCoord
    rw [hzero, one_mul]
  rw [hm]
  exact (segMean_bracket gapLaw_expCoord he 0).2

theorem kepReferenceDensity_one_second_polynomial {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) :
    (∫ x, |gammaScaledSecond (kepReferenceWeights eps 1) (kepReferenceSpan eps 1) x|) ≤
      4 * (cBr (bIn 1 1) (vIn 1 1)) ^ 2 * eps ^ 4 := by
  have h := (kepReferenceDensity_classical heps (j := 1) le_rfl).2.2.2.2.2.2.2
  have hm := kepReferenceSpan_pos heps 1
  have hupper := kepReferenceSpan_one_le heps
  calc
    _ ≤ 4 * (kepReferenceSpan eps 1) ^ 2 := h
    _ ≤ 4 * (cBr (bIn 1 1) (vIn 1 1) * eps ^ 2) ^ 2 := by gcongr
    _ = _ := by ring

end

end PGM
