import PLAStochastic.Affine.Moments.Optimal.Laplace.ConvolutionLaplace

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Real Q remains jointly Borel even before proving its finiteness. -/
theorem measurable_optimalMomentConvolution :
    Measurable (fun p : ℝ × ℝ × ℝ => optimalMomentConvolution p.1 p.2.1 p.2.2) := by
  let F : ((ℝ × ℝ × ℝ) × ℝ) × ℝ → ℝ := fun p =>
    (Ioo 0 (p.1.1.2.2-p.1.2)).indicator
      (fun w => optimalMomentConvolutionIntegrand p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 w) p.2
  have hm : Measurable F := by
    have hk := measurable_optimalMomentConvolutionIntegrand.comp (f := fun p : ((ℝ × ℝ × ℝ) × ℝ) × ℝ =>
      (p.1.1.1,p.1.1.2.1,p.1.1.2.2,p.1.2,p.2)) (by fun_prop)
    have hs : MeasurableSet {p : ((ℝ × ℝ × ℝ) × ℝ) × ℝ | p.2 ∈ Ioo 0 (p.1.1.2.2-p.1.2)} := by
      simp only [mem_Ioo]
      measurability
    exact hk.indicator hs
  have hi : StronglyMeasurable (fun p : (ℝ × ℝ × ℝ) × ℝ => ∫ w, F (p,w)) :=
    hm.stronglyMeasurable.integral_prod_right'
  have ho : Measurable (fun p : ℝ × ℝ × ℝ => ∫ v in Ioi (0:ℝ), ∫ w, F ((p,v),w)) :=
    hi.integral_prod_right'.measurable
  convert! ho using 1
  funext p
  unfold optimalMomentConvolution
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  exact (integral_indicator measurableSet_Ioo).symm

theorem optimalMomentConvolution_nonneg {a b : ℝ} (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (T : ℝ) :
    0≤optimalMomentConvolution a b T := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro v hv
  apply setIntegral_nonneg measurableSet_Ioo
  intro w hw
  exact (optimalMomentConvolutionIntegrand_pos ha hb hv hw).le

/-- Finiteness of the nonnegative convolution gives actual Fubini integrability,
so its Bochner definition agrees with the nonnegative one. -/
theorem ofReal_optimalMomentConvolution_eq_of_finite {a b T : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hfin : optimalMomentConvolutionENN a b T≠∞) :
    ENNReal.ofReal (optimalMomentConvolution a b T)=optimalMomentConvolutionENN a b T := by
  let F : ℝ×ℝ→ℝ := fun p =>
    (Ioo 0 (T-p.1)).indicator (fun w => optimalMomentConvolutionIntegrand a b T p.1 w) p.2
  let P : Measure (ℝ×ℝ) := (volume.restrict (Ioi (0:ℝ))).prod volume
  have hm : Measurable F := by
    have hs : MeasurableSet {p : ℝ×ℝ | p.2∈Ioo 0 (T-p.1)} := by simp only [mem_Ioo]; measurability
    exact (measurable_optimalMomentConvolutionIntegrand.comp (f := fun p : ℝ×ℝ =>
      (a,b,T,p.1,p.2)) (by fun_prop)).indicator hs
  have hn : 0≤ᵐ[P] F := by
    change ∀ᵐ p ∂P, (0:ℝ)≤F p
    apply (ae_prod_iff_ae_ae (measurableSet_le measurable_const hm)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    filter_upwards [] with w
    by_cases hw : w∈Ioo 0 (T-v)
    · simpa only [F,indicator_of_mem hw] using (optimalMomentConvolutionIntegrand_pos ha hb hv hw).le
    · simp only [F,indicator_of_notMem hw,le_refl]
  have hQ : (∫⁻ p, ENNReal.ofReal (F p) ∂P)=optimalMomentConvolutionENN a b T := by
    rw [lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    have he : (fun w => ENNReal.ofReal (F (v,w)))=
        (Ioo 0 (T-v)).indicator (fun w => ENNReal.ofReal (optimalMomentConvolutionIntegrand a b T v w)) := by
      funext w
      by_cases hw : w∈Ioo 0 (T-v) <;> simp [F,hw]
    rw [he,lintegral_indicator measurableSet_Ioo]
  have hi : Integrable F P := (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hn).mp
    (hQ.symm ▸ hfin)
  have hreal : (∫ p, F p ∂P)=optimalMomentConvolution a b T := by
    rw [integral_prod _ hi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    change (∫ w, (Ioo 0 (T-v)).indicator (fun w => optimalMomentConvolutionIntegrand a b T v w) w)=_
    exact integral_indicator measurableSet_Ioo
  rw [←hreal,ofReal_integral_eq_lintegral_ofReal hi hn,hQ]

/-- Positive exponential weighting makes Q finite at almost every positive time. -/
theorem optimalMomentConvolutionENN_ae_finite {a b : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) :
    ∀ᵐ T ∂volume.restrict (Ioi (0:ℝ)), optimalMomentConvolutionENN a b T≠∞ := by
  have hm : Measurable (fun T => ENNReal.ofReal (Real.exp (-(1^2/2)*T))*optimalMomentConvolutionENN a b T) :=
    (by fun_prop : Measurable (fun T : ℝ => ENNReal.ofReal (Real.exp (-(1^2/2)*T)))).mul
      (measurable_optimalMomentConvolutionENN.comp (f := fun T : ℝ => (a,b,T)) (by fun_prop))
  have hi : (∫⁻ T in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(1^2/2)*T))*optimalMomentConvolutionENN a b T)≠∞ := by
    rw [lintegral_laplace_optimalMomentConvolutionENN ha hb (by norm_num : (0:ℝ)<1)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top hm hi] with T hT
  exact (ENNReal.lt_top_of_mul_ne_top_right hT.ne
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne').ne

theorem ofReal_optimalMomentConvolution_eq_ae {a b : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) :
    (fun T => ENNReal.ofReal (optimalMomentConvolution a b T)) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      optimalMomentConvolutionENN a b :=
  (optimalMomentConvolutionENN_ae_finite ha hb).mono fun _ hfin =>
    ofReal_optimalMomentConvolution_eq_of_finite ha hb hfin

end BrownianAffine
