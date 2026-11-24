import PLAStochastic.Index.KEP.ReferenceScale.GammaRegularity
import PLAStochastic.ForMathlib.Probability.Distributions.GammaMixtureWeightedScale

/-!
# A fixed weighted Gamma entry on the actual reference orbit

The common regular-law class supplies one fixed exponent and moment bound.
Every positive layer has finite weighted classical derivative norms, and the
first second-derivative norm has a polynomial epsilon budget. The later rough
bound still grows with the mean scale, so a uniform recurrence is still needed.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepReferenceSpan_ge_four {eps : ℝ} (heps : kepReferenceClassicalThreshold ≤ eps)
    {j : ℕ} (hj : 1 ≤ j) : 4 ≤ kepReferenceSpan eps j := by
  have he : epsZero (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))) ≤ eps :=
    (le_max_right _ _).trans heps
  have hL := (layerOK_all (layerOK_input gapLaw_expCoord) (bAbs_le_bIn 1 1)
    (βAbs_le_βIn _ _) (vIn_pos one_pos one_pos) (vIn_le 1 1) KcAbs_le_KcIn he j).1
  have hint := hL.cnt2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hmin : ∀ᵐ ω ∂expSeqMeasure, (4 : ℝ) ≤ (epLayerSeq eps expCoord j 0 ω).2 := by
    filter_upwards [ae_reference_count_ge_four ((le_max_left _ _).trans heps) hj] with ω hω
    exact_mod_cast hω
  have h := integral_mono_ae (integrable_const (4 : ℝ)) hint hmin
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul] at h
  convert h using 1 <;> rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem kepReferenceDensity_weighted_of_regular {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {D theta0 vlo vhi theta : ℝ} (htheta0 : 0 < theta0) (hvlo : 0 < vlo)
    (hreg : RegLaw D theta0 vlo vhi (kepReferenceLaw eps j))
    (htheta : 0 ≤ theta) (htheta_le : theta ≤ theta0 / 2) (htheta_small : theta ≤ 1 / 2) :
    Integrable (fun x => Real.exp (theta * x) *
      gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j) x) volume ∧
      Integrable (fun x => Real.exp (theta * x) *
        gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) x) volume ∧
      (∫ x, Real.exp (theta * x) *
        |gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j) x|) ≤
          2 * kepReferenceSpan eps j * (2 * D / theta0) ∧
      (∫ x, Real.exp (theta * x) *
        |gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) x|) ≤
          4 * (kepReferenceSpan eps j) ^ 2 * (2 * D / theta0) := by
  have hm := kepReferenceSpan_pos heps j
  have hmin := kepReferenceSpan_ge_four heps hj
  have hEM := (hreg.expMom htheta0).mono (hreg.momClass htheta0 hvlo).pos
    htheta htheta_le le_rfl
  have hiLaw : Integrable (fun x => Real.exp (theta * x))
      (kepReferenceDensity heps hj).toMeasure := by
    rw [kepReferenceDensity_toMeasure heps hj]
    exact hEM.integrable
  have hi := ((kepReferenceDensity heps hj).integrable_toMeasure_iff
    (fun x => Real.exp (theta * x))).mp hiLaw
  rw [kepReferenceDensity_density heps hj] at hi
  have hi' : Integrable (fun x => Real.exp (theta * x) *
      gammaScaledMixture (kepReferenceWeights eps j) (kepReferenceSpan eps j) x) volume := by
    simpa only [mul_comm] using hi
  have he := (kepReferenceDensity heps hj).integral_toMeasure (fun x => Real.exp (theta * x))
  rw [kepReferenceDensity_toMeasure heps hj, kepReferenceDensity_density heps hj] at he
  have hM : (∫ x, Real.exp (theta * x) *
      gammaScaledMixture (kepReferenceWeights eps j) (kepReferenceSpan eps j) x) ≤ 2 * D / theta0 := by
    have hb := hEM.le
    rw [he] at hb
    simpa only [mul_comm] using hb
  obtain ⟨h1, h2, hF, hS⟩ := gammaScaled_weighted_derivatives
    (kepReferenceWeights_nonneg eps j)
    (kepReferenceWeights_summable ((le_max_left _ _).trans heps) hj)
    hm htheta (by linarith) hi'
  exact ⟨h1, h2, hF.trans (mul_le_mul_of_nonneg_left hM (by positivity)),
    hS.trans (mul_le_mul_of_nonneg_left hM (by positivity))⟩

theorem kepReference_weighted_finite_and_initial :
    ∃ theta M K eps0 : ℝ, 0 < theta ∧ 0 ≤ M ∧ 0 ≤ K ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps →
        (∀ j : ℕ, 1 ≤ j →
          Integrable (fun x => Real.exp (theta * x) *
            gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j) x) volume ∧
          Integrable (fun x => Real.exp (theta * x) *
            gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) x) volume ∧
          (∫ x, Real.exp (theta * x) *
            |gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) x|) ≤
              4 * M * (kepReferenceSpan eps j) ^ 2) ∧
        (∫ x, Real.exp (theta * x) *
          |gammaScaledSecond (kepReferenceWeights eps 1) (kepReferenceSpan eps 1) x|) ≤ K * eps ^ 4 := by
  obtain ⟨D, theta0, vlo, vhi, e0, hD, ht0, hvlo, -, hreg⟩ := kepReferenceLaw_regular
  let theta := min (theta0 / 2) (1 / 2)
  let M := 2 * D / theta0
  let cb := cBr (bIn 1 1) (vIn 1 1)
  have ht : 0 < theta := lt_min (by positivity) (by norm_num)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨theta, M, 4 * M * cb ^ 2, max kepReferenceClassicalThreshold e0,
    ht, hM, by positivity, le_max_left _ _, ?_⟩
  intro eps heps
  have he : kepReferenceClassicalThreshold ≤ eps := (le_max_left _ _).trans heps
  have hr : e0 ≤ eps := (le_max_right _ _).trans heps
  have hb (j : ℕ) (hj : 1 ≤ j) := kepReferenceDensity_weighted_of_regular he hj ht0 hvlo
    (hreg eps hr j) ht.le (min_le_left _ _) (min_le_right _ _)
  constructor
  · intro j hj
    obtain ⟨h1, h2, -, hS⟩ := hb j hj
    refine ⟨h1, h2, hS.trans_eq ?_⟩
    dsimp [M]
    ring
  · have h := (hb 1 le_rfl).2.2.2
    have hm := kepReferenceSpan_pos he 1
    have hup := kepReferenceSpan_one_le he
    have hsq : (kepReferenceSpan eps 1) ^ 2 ≤ (cb * eps ^ 2) ^ 2 := by gcongr
    calc
      _ ≤ 4 * (kepReferenceSpan eps 1) ^ 2 * M := h
      _ ≤ 4 * (cb * eps ^ 2) ^ 2 * M := by gcongr
      _ = _ := by ring

end

end PGM
