import PLAStochastic.Index.CEPS.Scaled.CentralEntranceBudget
import PLAStochastic.Index.CEPS.Scaled.TruePairScaling

/-! # A class-uniform central complete-pair scale budget -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsScaledSurrogateBridge cepsScaledSurrogateEntrance

def CepsCanonDomain.centralPairBound {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  Real.exp 1 * dom.centralEntranceBound N M ^ 2 *
    (4 * (dom.centralBridgeBound N M / (dom.centralCoordinateRadius N M ^ 2 / 4)) +
      dom.centralBridgeBound N M / 2)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledCentral_width_bounds (N : ℕ) (M : ℝ) (lam : ℝ)
    (hlam : |lam| ≤ dom.centralFrequencyDriftRadius N M) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M)) :
    ‖b‖ ≤ 1 / 2 ∧ ‖1 + b * lam‖ ≤ 2 ∧ 1 + b * (lam : ℂ) ≠ 0 ∧ ‖(1 + b * (lam : ℂ))⁻¹‖ ≤ 2 := by
  have hL : ‖(lam : ℂ)‖ ≤ dom.centralDriftRadius N M := by
    simpa only [norm_real, Real.norm_eq_abs] using hlam.trans (min_le_left _ _)
  have hR := centralCoordinateRadius_pos dom hW hθ hD N M
  obtain ⟨_, hbhalf, _, _, hw⟩ := cepsScaledCentral_scale_bounds dom hW hθ hD N M hL
    (show ‖(0 : ℂ)‖ ≤ dom.centralCoordinateRadius N M by simpa using hR.le) hb
  have hw2 : ‖1 + b * lam‖ ≤ 2 := by
    have ht := norm_add_le ((1 + b * lam) - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at ht
    linarith
  have hwlo : 1 / 2 ≤ ‖1 + b * (lam : ℂ)‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (1 + b * lam)
    rw [norm_one, norm_sub_rev] at ht
    linarith
  have hwpos : 0 < ‖1 + b * (lam : ℂ)‖ := lt_of_lt_of_le (by norm_num) hwlo
  refine ⟨hbhalf, hw2, norm_pos_iff.mp hwpos, ?_⟩
  rw [norm_inv]
  exact ((inv_le_inv₀ hwpos (by norm_num : (0 : ℝ) < 1 / 2)).mpr hwlo).trans_eq (by norm_num)

include hW hθ hD in
theorem cepsScaledSurrogatePair_central_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ)
    (hlam : |lam| ≤ dom.centralFrequencyDriftRadius N M) {z : ℂ} (hz : 0 ≤ z.re)
    (hznorm : ‖z‖ < dom.centralFrequencyRadius N M) :
    DifferentiableOn ℂ (cepsScaledSurrogatePair dom ρW N lam z) (ball 0 (dom.centralPairScaleRadius N M)) := by
  let U : Set ℂ := ball 0 (dom.centralPairScaleRadius N M)
  have hsub : U ⊆ ball (0 : ℂ) (dom.centralScaleRadius N M) := ball_subset_ball (min_le_left _ _)
  have hsubE : U ⊆ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z) :=
    fun _ hb => (cepsScaledCentral_pairScale_mem dom hW hθ hD N M hlam hznorm.le hb).2
  obtain ⟨hB, hDB, _⟩ := cepsScaledSurrogateBridge_central_scale_budget dom hW hθ hD hf hη hM N hN lam hlam hz hznorm
  have hH := (cepsScaledSurrogateEntrance_differentiableOn dom hW hθ hD hf hη hM N hN lam hz).mono hsubE
  have hw : DifferentiableOn ℂ (fun b : ℂ => 1 + b * (lam : ℂ)) U := by fun_prop
  have hwne : ∀ b ∈ U, 1 + b * (lam : ℂ) ≠ 0 :=
    fun b hb => (cepsScaledCentral_width_bounds dom hW hθ hD N M lam hlam (hsub hb)).2.2.1
  have hO := (((hw.inv hwne).neg.mul (hDB.mono hsub)).sub
    (differentiableOn_id.mul (hB.mono hsub)))
  have hE : DifferentiableOn ℂ (fun b : ℂ => exp ((b * z) * (1 + b * lam))) U := by fun_prop
  unfold cepsScaledSurrogatePair
  simpa only [one_div, Pi.mul_def, Pi.sub_def, Pi.neg_def, Pi.pow_apply, Pi.inv_apply, id_eq] using (hE.mul (hH.pow 2)).mul hO

include hW hθ hD in
theorem cepsScaledSurrogatePair_central_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ)
    (hlam : |lam| ≤ dom.centralFrequencyDriftRadius N M) {z b : ℂ} (hz : 0 ≤ z.re)
    (hznorm : ‖z‖ < dom.centralFrequencyRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralPairScaleRadius N M)) :
    ‖cepsScaledSurrogatePair dom ρW N lam z b‖ ≤ dom.centralPairBound N M := by
  have hbC := (cepsScaledCentral_pairScale_mem dom hW hθ hD N M hlam hznorm.le hb).1
  obtain ⟨hbhalf, hw2, _, hwInv⟩ := cepsScaledCentral_width_bounds dom hW hθ hD N M lam hlam hbC
  have hz1 := (cepsScaledCentral_frequency_envelope dom hW hθ hD N M hlam hznorm.le).2.1
  have hE : ‖exp ((b * z) * (1 + b * lam))‖ ≤ Real.exp 1 := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    apply (re_le_norm _).trans
    rw [norm_mul, norm_mul]
    have h := mul_le_mul (mul_le_mul hbhalf hz1 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2))
      hw2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ (1 / 2) * 1)
    norm_num only [mul_one, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)] at h
    exact h
  have hH := cepsScaledSurrogateEntrance_central_bound dom hW hθ hD hf hη hM N hN lam hlam hz hznorm.le hb
  obtain ⟨hB, hDB⟩ := (cepsScaledSurrogateBridge_central_scale_budget dom hW hθ hD hf hη hM N hN lam hlam hz hznorm).2.2 b hbC
  have hC : 0 ≤ dom.centralBridgeBound N M := by
    unfold CepsCanonDomain.centralBridgeBound
    have := boundedSpatialWeightLower_pos dom hD N M
    positivity
  have hDC : 0 ≤ dom.centralBridgeBound N M / (dom.centralCoordinateRadius N M ^ 2 / 4) := by positivity
  have hO : ‖-(1 / (1 + b * lam)) * deriv (fun z => cepsScaledSurrogateBridge dom ρW N lam z b) z -
      b * cepsScaledSurrogateBridge dom ρW N lam z b‖ ≤
      4 * (dom.centralBridgeBound N M / (dom.centralCoordinateRadius N M ^ 2 / 4)) + dom.centralBridgeBound N M / 2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul, norm_mul, norm_neg, one_div]
    have h1 := mul_le_mul hwInv hDB (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have h2 := mul_le_mul hbhalf hB (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith
  have hHC : 0 ≤ dom.centralEntranceBound N M := by
    unfold CepsCanonDomain.centralEntranceBound
    have := surrogateEntrancePolynomialConstant_pos dom hW hθ hD N M
    positivity
  rw [cepsScaledSurrogatePair, norm_mul, norm_mul, norm_pow]
  exact mul_le_mul (mul_le_mul hE (pow_le_pow_left₀ (norm_nonneg _) hH 2) (sq_nonneg _) (Real.exp_pos _).le)
    hO (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

end PGM
