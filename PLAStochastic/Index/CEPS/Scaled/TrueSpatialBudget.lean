import PLAStochastic.Index.CEPS.Scaled.TrueDenominatorStable

/-! # Fixed-disc weighted spatial budgets of the actual factor -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueSpatialBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (M : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * (Real.exp 2 *
    (v * Real.exp (2 * dom.canonDriftTaylorBound 0 M (dom.μ₀ / 8)))) / (1 / 2 : ℝ) ^ n +
      dom.trueSpatialErrorConstant 0 M n

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueSpatialBound_nonneg {M : ℝ} (hM : 0 ≤ M) (n : ℕ) :
    0 ≤ dom.trueSpatialBound M n := by
  have := trueSpatialErrorConstant_nonneg dom hW hθ hD hM 0 n
  have := CepsCanonDomain.v_pos hW hθ hD
  unfold CepsCanonDomain.trueSpatialBound
  positivity

include hW hθ hD in
theorem cepsScaledTrueScale_drift_le_one (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) : |b * lam| ≤ 1 := by
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hb
  have ht := entranceScaleCurve_product_bound dom hD 0 M lam hbE
  rw [norm_real, Real.norm_eq_abs] at ht
  have hC : 0 ≤ dom.actualScaledRootBound lam z := (norm_nonneg _).trans
    ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).2 0
      (mem_ball_self (actualRootScaleRadius_pos dom hW hθ hD lam z)))
  have hbase : dom.canonScaleBase ≤ 1 := min_le_left _ _
  rw [abs_mul]
  nlinarith [abs_nonneg b, abs_nonneg lam, Real.sqrt_nonneg ‖z‖]

include hW hθ hD in
theorem cepsScaledTrueG_spatial_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) (n : ℕ) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ dom.entranceSpatialScaleRadius lam z / 2) :
    ‖iteratedDeriv n (cepsScaledTrueG dom ρW lam z b) ξ‖ ≤
      dom.trueSpatialBound M n * Real.exp (-(ξ * (1 + (b : ℂ) * lam)).re) := by
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hb
  have hA := cepsScaledTrueG_spatial_error_budget dom hW hθ hD hf hη hM 0 hm lam hz hbE n hξ
  have hB := cepsScaledSurrogateG_spatial_deriv_budget dom hW hθ hD hf hη hM 0 (by omega) lam hz hbE n hξ
  have hC := trueSpatialErrorConstant_nonneg dom hW hθ hD
    ((cepsSobolev_nonneg m η fW).trans hM) 0 n
  have hμ := cepsScaledTrueScale_drift_le_one dom hW hθ hD M lam hz hb
  have hE : 0 ≤ Real.exp (-(ξ * (1 + (b : ℂ) * lam)).re) := (Real.exp_pos _).le
  simp only [zero_add, pow_one] at hA
  have hAE := hA.trans (mul_le_mul_of_nonneg_left hμ (mul_nonneg hC hE))
  have ht := norm_add_le
    (iteratedDeriv n (cepsScaledTrueG dom ρW lam z b) ξ -
      iteratedDeriv n (cepsScaledSurrogateG dom ρW 0 lam z b) ξ)
    (iteratedDeriv n (cepsScaledSurrogateG dom ρW 0 lam z b) ξ)
  rw [sub_add_cancel] at ht
  exact ht.trans ((add_le_add hAE hB).trans_eq (by
    unfold CepsCanonDomain.trueSpatialBound CepsCanonDomain.trueSpatialErrorConstant
    ring))

include hW hθ hD in
theorem cepsScaledTrueEntranceNumerator_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    ‖cepsScaledTrueEntranceNumerator dom ρW lam z b‖ ≤ dom.trueSpatialBound M 2 *
      (Real.exp (-(cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re) +
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) +
          Real.exp (-(((b : ℂ) * z) * (1 + (b : ℂ) * lam)).re)) := by
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hb
  have hR := (entranceScale_constants dom hW hθ hD 0 M lam z).2
  have hC := trueSpatialBound_nonneg dom hW hθ hD ((cepsSobolev_nonneg m η fW).trans hM) 2
  have hG := cepsScaledTrueG_spatial_differentiableOn dom hW hθ hD 0 M lam hz hbE
  apply cepsNormal_norm_second_dslope_le_weighted hR hC hG _
    (entranceScaleCurve_root_norm_le_half dom hW hθ hD 0 M lam hz hbE (by norm_num))
    (entranceScaleCurve_root_norm_le_half dom hW hθ hD 0 M lam hz hbE (by norm_num))
    (entranceScaleCurve_mark_norm_le_half dom hW hθ hD 0 M lam hz hbE)
  intro ξ hξ
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using!
    cepsScaledTrueG_spatial_budget dom hW hθ hD hf hη hM hm lam hz hb 2 hξ

end PGM
