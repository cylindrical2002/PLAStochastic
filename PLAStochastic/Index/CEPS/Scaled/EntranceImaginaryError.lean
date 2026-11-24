import PLAStochastic.Index.CEPS.Scaled.TimeOperatorError

/-! # Uniform actual and surrogate entrance comparison on imaginary frequencies -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.entranceComparisonConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  3 * (|dom.trueEntranceWeightedConstant M| + |dom.trueEntranceErrorConstant N M|)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledEntrance_imaginary_weights_le (M lam : ℝ) {z : ℂ} (hz : z.re = 0)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    1 + Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
      cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) +
        Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - (b : ℂ) * z) *
          (1 + (b : ℂ) * lam)).re) ≤ 3 := by
  obtain ⟨hp, ha⟩ := cepsScaledTrueFrequency_root_re_signs dom hW hθ hD M lam hz.symm.le hb hbs
  obtain ⟨_, _, _, _, hwlo, _, _⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz.symm.le hb hbs
  have hw : 0 ≤ 1 + b * lam := by linarith
  have ht : ((b : ℂ) * z).re = 0 := by simp [mul_re, hz]
  have hwre : (1 + (b : ℂ) * (lam : ℂ)).re = 1 + b * lam := by simp
  have hwim : (1 + (b : ℂ) * (lam : ℂ)).im = 0 := by simp
  have he₁ : Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
      cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    simp only [mul_re, sub_re, hwre, hwim, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (ha.trans hp)) hw
  have he₂ : Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - (b : ℂ) * z) *
      (1 + (b : ℂ) * lam)).re) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    simp only [mul_re, sub_re, hwre, hwim, ht, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg ha hw
  linarith

include hW hθ hD in
theorem cepsScaledTrueEntrance_imaginary_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueEntrance dom ρW lam z b - cepsScaledSurrogateEntrance dom ρW N lam z b‖ ≤
      (3 * |dom.trueEntranceErrorConstant N M|) * (1 + |lam| + Real.sqrt ‖z‖) *
        |b * lam| ^ (N + 1) := by
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have h := cepsScaledTrueEntrance_error_budget dom hW hθ hD hf hη hM N hN lam hz.symm.le hbD hbN
  have hw := cepsScaledEntrance_imaginary_weights_le dom hW hθ hD M lam hz hb hbs
  apply h.trans
  calc
    _ ≤ (|dom.trueEntranceErrorConstant N M| * (1 + |lam| + Real.sqrt ‖z‖)) * 3 *
        |b * lam| ^ (N + 1) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg _) _)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      · exact hw
      · positivity
      · positivity
    _ = _ := by ring

include hW hθ hD in
theorem cepsScaledEntrance_imaginary_comparison_profile {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueEntrance dom ρW lam z b‖ ≤ dom.entranceComparisonConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ∧
    ‖cepsScaledSurrogateEntrance dom ρW N lam z b‖ ≤ dom.entranceComparisonConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ∧
    ‖cepsScaledTrueEntrance dom ρW lam z b - cepsScaledSurrogateEntrance dom ρW N lam z b‖ ≤
      dom.entranceComparisonConstant N M * (1 + |lam| + Real.sqrt ‖z‖) * |b * lam| ^ (N + 1) := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have ht := cepsScaledTrueEntrance_imaginary_budget dom hW hθ hD hf hη hM (by omega) lam hz hb hbs
  have hT : ‖cepsScaledTrueEntrance dom ρW lam z b‖ ≤ 3 * |dom.trueEntranceWeightedConstant M| * X :=
    ht.trans (by dsimp only [X]; gcongr; exact le_abs_self _)
  have he := cepsScaledTrueEntrance_imaginary_error_budget dom hW hθ hD hf hη hM N hN lam hz hb hbs hbN
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have hμ := cepsScaledTrueScale_drift_le_one dom hW hθ hD M lam hz.symm.le hbD
  have he1 : |b * lam| ^ (N + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hμ
  have hEn : ‖cepsScaledTrueEntrance dom ρW lam z b - cepsScaledSurrogateEntrance dom ρW N lam z b‖ ≤
      3 * |dom.trueEntranceErrorConstant N M| * X :=
    he.trans ((mul_le_mul_of_nonneg_left he1 (by positivity)).trans_eq (mul_one _))
  refine ⟨hT.trans ?_, ?_, he.trans ?_⟩
  · unfold CepsCanonDomain.entranceComparisonConstant
    nlinarith [abs_nonneg (dom.trueEntranceErrorConstant N M)]
  · have hn := norm_sub_le (cepsScaledTrueEntrance dom ρW lam z b)
      (cepsScaledTrueEntrance dom ρW lam z b - cepsScaledSurrogateEntrance dom ρW N lam z b)
    rw [sub_sub_cancel] at hn
    exact hn.trans ((add_le_add hT hEn).trans_eq (by unfold CepsCanonDomain.entranceComparisonConstant; ring))
  · unfold CepsCanonDomain.entranceComparisonConstant
    gcongr
    linarith [abs_nonneg (dom.trueEntranceWeightedConstant M)]

end PGM
