import PLAStochastic.Index.CEPS.Scaled.TrueSpatialError
import PLAStochastic.Index.CEPS.Scaled.SlopeSubtraction
import PLAStochastic.Index.CEPS.Scaled.SurrogateSecondSlopeBudget
import PLAStochastic.Index.CEPS.Scaled.SurrogateDividedDenominator

/-! # Actual scaled divided-difference errors, including collisions

The true factor is evaluated only at real scale. Its first and second
divided differences retain the respective endpoint weights and the full
real-drift vanishing order. No inverse denominator is used here.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueSpatialErrorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * (Real.exp 2 * dom.canonWeightErrorBound N M) / (1 / 2 : ℝ) ^ n

def cepsScaledTrueDenominator {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  dslope (cepsScaledTrueG dom ρW lam z b)
    (cepsScaledSignedRoot D θ ρW lam z (-1) b)
    (cepsScaledSignedRoot D θ ρW lam z 1 b)

def cepsScaledTrueEntranceNumerator {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  dslope (dslope (cepsScaledTrueG dom ρW lam z b)
    (cepsScaledSignedRoot D θ ρW lam z (-1) b))
    (cepsScaledSignedRoot D θ ρW lam z 1 b) ((b : ℂ) * z)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueSpatialErrorConstant_nonneg {M : ℝ} (hM : 0 ≤ M) (N n : ℕ) :
    0 ≤ dom.trueSpatialErrorConstant N M n := by
  have := CepsCanonDomain.v_pos hW hθ hD
  have := dom.jetC_nonneg hD N
  have := dom.c₀_pos
  unfold CepsCanonDomain.trueSpatialErrorConstant CepsCanonDomain.canonWeightErrorBound
    CepsCanonDomain.canonDriftCoeffBound
  positivity

include hW hθ hD in
theorem entranceScaleCurve_root_norm_le_half (N : ℕ) (M lam : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) {b sign : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) (hsign : ‖sign‖ ≤ 1) :
    ‖cepsScaledSignedRoot D θ ρW lam z sign b‖ ≤ dom.entranceSpatialScaleRadius lam z / 2 := by
  have hsub : dom.entranceScaleRadius N M lam z ≤ dom.actualRootScaleRadius lam z :=
    (min_le_right _ _).trans ((div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le
      (by norm_num)).trans (min_le_left _ _))
  have hn := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz hsign).2 b
    (ball_subset_ball hsub hb)
  unfold CepsCanonDomain.entranceSpatialScaleRadius
  nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]

include hW hθ hD in
theorem entranceScaleCurve_mark_norm_le_half (N : ℕ) (M lam : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖b * z‖ ≤ dom.entranceSpatialScaleRadius lam z / 2 := by
  have hn := cepsScaledMark_norm_le_frequency dom hW hθ hD N M lam hz hb
  have hC : 0 ≤ dom.actualScaledRootBound lam z := (norm_nonneg _).trans
    ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).2 0
      (mem_ball_self (actualRootScaleRadius_pos dom hW hθ hD lam z)))
  unfold CepsCanonDomain.entranceSpatialScaleRadius
  nlinarith [abs_nonneg lam]

include hW hθ hD in
theorem cepsScaledTrueG_dslope_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) {a t : ℂ}
    (ha : ‖a‖ ≤ dom.entranceSpatialScaleRadius lam z / 2)
    (ht : ‖t‖ ≤ dom.entranceSpatialScaleRadius lam z / 2) :
    ‖dslope (cepsScaledTrueG dom ρW lam z b) a t -
      dslope (cepsScaledSurrogateG dom ρW N lam z b) a t‖ ≤
      dom.trueSpatialErrorConstant N M 1 * |b * lam| ^ (N + 1) *
        (Real.exp (-(a * (1 + (b : ℂ) * lam)).re) +
          Real.exp (-(t * (1 + (b : ℂ) * lam)).re)) := by
  have hR := (entranceScale_constants dom hW hθ hD N M lam z).2
  have hA := cepsScaledTrueG_spatial_differentiableOn dom hW hθ hD N M lam hz hb
  have hdJ := cepsScaledSurrogateG_differentiableOn_joint dom hW hθ hD
    (M := M) hf hη N (by omega) lam hz
  have hB : DifferentiableOn ℂ (cepsScaledSurrogateG dom ρW N lam z b)
      (ball 0 (dom.entranceSpatialScaleRadius lam z)) :=
    fun ξ hξ => (differentiableAt_slice_snd (isOpen_ball.prod isOpen_ball) hdJ ⟨hb, hξ⟩).differentiableWithinAt
  apply cepsNormal_norm_dslope_sub_le_weighted hR
    (mul_nonneg (trueSpatialErrorConstant_nonneg dom hW hθ hD
      ((cepsSobolev_nonneg m η fW).trans hM) N 1) (pow_nonneg (abs_nonneg _) _)) hA hB _ ha ht
  intro ξ hξ
  have he := cepsScaledTrueG_spatial_error_budget dom hW hθ hD hf hη hM N hN lam hz hb 1 hξ
  simpa only [iteratedDeriv_one, CepsCanonDomain.trueSpatialErrorConstant, mul_assoc,
    mul_comm (Real.exp _) (|b * lam| ^ (N + 1))] using! he

include hW hθ hD in
theorem cepsScaledTrueG_second_dslope_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) {a p t : ℂ}
    (ha : ‖a‖ ≤ dom.entranceSpatialScaleRadius lam z / 2)
    (hp : ‖p‖ ≤ dom.entranceSpatialScaleRadius lam z / 2)
    (ht : ‖t‖ ≤ dom.entranceSpatialScaleRadius lam z / 2) :
    ‖dslope (dslope (cepsScaledTrueG dom ρW lam z b) a) p t -
      dslope (dslope (cepsScaledSurrogateG dom ρW N lam z b) a) p t‖ ≤
      dom.trueSpatialErrorConstant N M 2 * |b * lam| ^ (N + 1) *
        (Real.exp (-(a * (1 + (b : ℂ) * lam)).re) +
          Real.exp (-(p * (1 + (b : ℂ) * lam)).re) +
            Real.exp (-(t * (1 + (b : ℂ) * lam)).re)) := by
  have hR := (entranceScale_constants dom hW hθ hD N M lam z).2
  have hA := cepsScaledTrueG_spatial_differentiableOn dom hW hθ hD N M lam hz hb
  have hdJ := cepsScaledSurrogateG_differentiableOn_joint dom hW hθ hD
    (M := M) hf hη N (by omega) lam hz
  have hB : DifferentiableOn ℂ (cepsScaledSurrogateG dom ρW N lam z b)
      (ball 0 (dom.entranceSpatialScaleRadius lam z)) :=
    fun ξ hξ => (differentiableAt_slice_snd (isOpen_ball.prod isOpen_ball) hdJ ⟨hb, hξ⟩).differentiableWithinAt
  apply cepsNormal_norm_second_dslope_sub_le_weighted hR
    (mul_nonneg (trueSpatialErrorConstant_nonneg dom hW hθ hD
      ((cepsSobolev_nonneg m η fW).trans hM) N 2) (pow_nonneg (abs_nonneg _) _)) hA hB _ ha hp ht
  intro ξ hξ
  have he := cepsScaledTrueG_spatial_error_budget dom hW hθ hD hf hη hM N hN lam hz hb 2 hξ
  simpa only [CepsCanonDomain.trueSpatialErrorConstant, mul_assoc,
    mul_comm (Real.exp _) (|b * lam| ^ (N + 1))] using! he

include hW hθ hD in
theorem cepsScaledTrueDenominator_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueDenominator dom ρW lam z b - cepsScaledSurrogateDenominator dom ρW N lam z b‖ ≤
      dom.trueSpatialErrorConstant N M 1 * |b * lam| ^ (N + 1) *
        (Real.exp (-(cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re) +
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re)) :=
  cepsScaledTrueG_dslope_error_budget dom hW hθ hD hf hη hM N hN lam hz hb
    (entranceScaleCurve_root_norm_le_half dom hW hθ hD N M lam hz hb (by norm_num))
    (entranceScaleCurve_root_norm_le_half dom hW hθ hD N M lam hz hb (by norm_num))

include hW hθ hD in
theorem cepsScaledTrueEntranceNumerator_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueEntranceNumerator dom ρW lam z b -
      dslope (dslope (cepsScaledSurrogateG dom ρW N lam z b)
        (cepsScaledSignedRoot D θ ρW lam z (-1) b))
        (cepsScaledSignedRoot D θ ρW lam z 1 b) ((b : ℂ) * z)‖ ≤
      dom.trueSpatialErrorConstant N M 2 * |b * lam| ^ (N + 1) *
        (Real.exp (-(cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re) +
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) +
            Real.exp (-(((b : ℂ) * z) * (1 + (b : ℂ) * lam)).re)) :=
  cepsScaledTrueG_second_dslope_error_budget dom hW hθ hD hf hη hM N hN lam hz hb
    (entranceScaleCurve_root_norm_le_half dom hW hθ hD N M lam hz hb (by norm_num))
    (entranceScaleCurve_root_norm_le_half dom hW hθ hD N M lam hz hb (by norm_num))
    (entranceScaleCurve_mark_norm_le_half dom hW hθ hD N M lam hz hb)

end PGM
