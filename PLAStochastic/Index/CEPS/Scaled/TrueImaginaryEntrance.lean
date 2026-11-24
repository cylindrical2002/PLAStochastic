import PLAStochastic.Index.CEPS.Scaled.TrueNegativeDerivative
import PLAStochastic.Index.CEPS.Scaled.LadderSigns

/-! # Actual entrance bounds on the imaginary frequency axis -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueFrequency_root_re_signs (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    0 ≤ (cepsScaledSignedRoot D θ ρW lam z 1 b).re ∧
      (cepsScaledSignedRoot D θ ρW lam z (-1) b).re ≤ 0 := by
  obtain ⟨hμ, hq, hre, _, _, _, _⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hqeq : cepsComplexScaledDiscount lam z b = cepsScaledDiscount b lam z := by
    simp only [cepsComplexScaledDiscount, cepsScaledDiscount, ofReal_mul]
  rw [hqeq] at hq hre
  have hq' := hq.trans (half_le_self dom.q₀_pos.le)
  have hs := cepsRoots_re_signs dom hW hθ hD hμ hre hq'
  have hμnorm : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  rw [cepsScaledSignedRoot_plus_actual hW hθ hD hb (dom.μ_lt_chart hμnorm),
    cepsScaledSignedRoot_minus_actual hW hθ hD hb (dom.μ_lt_chart hμnorm),
    div_ofReal_re, div_ofReal_re]
  exact ⟨div_nonneg hs.1 hb.le, div_nonpos_of_nonpos_of_nonneg hs.2 hb.le⟩

include hW hθ hD in
theorem cepsScaledTrueFrequency_scale_width_budget (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    ‖(b : ℂ)‖ ≤ 1 ∧ ‖(1 / (1 + (b : ℂ) * lam) : ℂ)‖ ≤ 2 := by
  obtain ⟨_, _, _, _, hwlo, _, _⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hw : 0 < 1 + b * lam := by linarith
  have hT := (cepsNormal_width_properties dom hW hθ hD
    (l := dom.normalWidthThreshold) le_rfl).1
  have hn := mem_ball_zero_iff.mp hbs
  have hX : 1 ≤ 1 + |lam| + Real.sqrt ‖z‖ := by
    linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hbase : dom.trueFrequencyScaleBase M ≤ 1 / (4 * (1 + dom.normalWidthThreshold)) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 1 + |lam| + Real.sqrt ‖z‖)).mp hn
  have hbound : 1 / (4 * (1 + dom.normalWidthThreshold)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * (1 + dom.normalWidthThreshold))).mpr
    linarith
  constructor
  · nlinarith [norm_nonneg (b : ℂ)]
  · have he : 1 + (b : ℂ) * (lam : ℂ) = ((1 + b * lam : ℝ) : ℂ) := by push_cast; rfl
    rw [he, norm_div, norm_one, norm_real, Real.norm_eq_abs, abs_of_pos hw]
    exact (div_le_iff₀ hw).mpr (by linarith)

include hW hθ hD in
theorem cepsScaledTrueEntrance_imaginary_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ)
    {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    ‖cepsScaledTrueEntrance dom ρW lam z b‖ ≤
      (3 * dom.trueEntranceWeightedConstant M) * (1 + |lam| + Real.sqrt ‖z‖) := by
  have hz0 : 0 ≤ z.re := hz.symm.le
  have hbd := ball_subset_ball ((trueFrequencyScaleRadius_le dom M lam z).trans
    (truePairScaleRadius_le dom M lam z)) hbs
  have hn := cepsScaledTrueEntrance_weighted_budget dom hW hθ hD hf hη hM hm lam hz0 hbd
  obtain ⟨hp, ha⟩ := cepsScaledTrueFrequency_root_re_signs dom hW hθ hD M lam hz0 hb hbs
  obtain ⟨_, _, _, _, hwlo, _, _⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz0 hb hbs
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
  have hK : 0 ≤ dom.trueEntranceWeightedConstant M := by
    have := trueSpatialBound_nonneg dom hW hθ hD ((cepsSobolev_nonneg m η fW).trans hM) 2
    have := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M
    have := cepsVarLo_pos hD
    unfold CepsCanonDomain.trueEntranceWeightedConstant
    positivity
  exact hn.trans ((mul_le_mul_of_nonneg_left (by linarith :
    1 + Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
      cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) +
        Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - (b : ℂ) * z) *
          (1 + (b : ℂ) * lam)).re) ≤ 3) (by positivity)).trans_eq (by ring))

theorem cepsScaledMarker_exp_norm_imaginary (lam b : ℝ) {z : ℂ} (hz : z.re = 0) :
    ‖exp (((b : ℂ) * z) * (1 + (b : ℂ) * lam))‖ = 1 := by
  rw [norm_exp]
  simp [mul_re, mul_im, hz]

end PGM
