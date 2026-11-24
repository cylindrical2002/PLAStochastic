import PLAStochastic.Index.CEPS.Scaled.TrueEntranceCorrection

/-! # Actual entrance correction decay on the imaginary frequency axis -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRootMinus_positive_exp_polynomial (N : ℕ) (M lam : ℝ) (hlam : 0 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.complexDirectionScaleRadius N M lam z)) :
    Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) ≤
      Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hdir := (cepsScaledRoot_complex_width_directions dom hW hθ hD N M lam hz hb).2 hlam
  rw [neg_mul, neg_re] at hdir
  have hbS := ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hb)
  have hcoord := cepsScaledRootCoordinate_lower dom hW hθ hD N M lam hz hbS
  have hv : 0 < 8 * Real.sqrt v := by have := CepsCanonDomain.v_pos hW hθ hD; positivity
  have hlo := (div_le_div_of_nonneg_right
    ((scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z).trans hcoord) hv.le).trans hdir
  have hr : ((|lam| + Real.sqrt ‖z‖) / Real.sqrt (8 * v + 8)) / (8 * Real.sqrt v) =
      dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) := by
    unfold CepsCanonDomain.negativeBridgeDecayRate
    ring
  rw [hr] at hlo
  exact Real.exp_le_exp.mpr (by linarith)

include hW hθ hD in
theorem cepsScaledTrueEntranceCorrection_positive_imaginary_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    ‖cepsScaledTrueEntranceCorrection dom ρW lam z b‖ ≤
      (2 * dom.trueEntranceCorrectionConstant M) * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hz0 : 0 ≤ z.re := hz.symm.le
  have hbd := ball_subset_ball ((trueFrequencyScaleRadius_le dom M lam z).trans
    (truePairScaleRadius_le dom M lam z)) hbs
  have hbP : (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase 0 M /
      (1 + |lam| + Real.sqrt ‖z‖)) :=
    ball_subset_ball (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) hbd
  have hbD := ball_subset_ball (min_le_left _ _)
    (ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD 0 M lam z).1 hbP)
  have hn := cepsScaledTrueEntranceCorrection_positive_weighted_budget dom hW hθ hD
    hf hη hM hm lam hlam hz0 hbd
  have he := cepsScaledRootMinus_positive_exp_polynomial dom hW hθ hD 0 M lam (by linarith) hz0 hbD
  obtain ⟨hp, _⟩ := cepsScaledTrueFrequency_root_re_signs dom hW hθ hD M lam hz0 hb hbs
  obtain ⟨_, _, _, _, hwlo, _, _⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz0 hb hbs
  have hw : 0 ≤ 1 + b * lam := by linarith
  have hwre : (1 + (b : ℂ) * (lam : ℂ)).re = 1 + b * lam := by simp
  have hwim : (1 + (b : ℂ) * (lam : ℂ)).im = 0 := by simp
  have hpw : 0 ≤ (cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re := by
    rw [mul_re, hwre, hwim, mul_zero, sub_zero]
    exact mul_nonneg hp hw
  have htw : (((b : ℂ) * z) * (1 + (b : ℂ) * lam)).re = 0 := by
    simp [mul_re, mul_im, hz]
  have he₁ : Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
      cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) ≤
        Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
    apply (Real.exp_le_exp.mpr _).trans he
    rw [sub_mul, sub_re]
    linarith
  have he₂ : Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - (b : ℂ) * z) *
      (1 + (b : ℂ) * lam)).re) ≤
        Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
    simpa only [sub_mul, sub_re, htw, sub_zero] using he
  have hK := trueEntranceCorrectionConstant_nonneg dom hW hθ hD ((cepsSobolev_nonneg m η fW).trans hM)
  apply hn.trans
  exact (mul_le_mul_of_nonneg_left (add_le_add he₁ he₂) (by positivity)).trans_eq (by ring)

end PGM
