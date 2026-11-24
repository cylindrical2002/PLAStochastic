import PLAStochastic.Affine.Moments.Optimal.Survival.Kernel.ConvolutionRepresentation
import PLAStochastic.Affine.Moments.Optimal.Width.UnitWidth

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalSurvivalSpatialMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))

instance : IsFiniteMeasure optimalSurvivalSpatialMeasure := by
  unfold optimalSurvivalSpatialMeasure
  infer_instance

theorem ae_mem_optimalSurvivalSpatialMeasure : ∀ᵐ p ∂optimalSurvivalSpatialMeasure,
    p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioo (0 : ℝ) 1 := by
  apply (ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with b hb
  exact ⟨ha,hb⟩

def optimalSurvivalSpatialIntegrand (T : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp ((p.2-p.1)^2/(2*T))*optimalMomentConvolution p.1 p.2 T

def optimalSurvivalSpatialIntegral (T : ℝ) : ℝ :=
  ∫ p, optimalSurvivalSpatialIntegrand T p ∂optimalSurvivalSpatialMeasure

theorem measurable_optimalSurvivalSpatialIntegrand (T : ℝ) :
    Measurable (optimalSurvivalSpatialIntegrand T) := by
  exact (by fun_prop : Measurable (fun p : ℝ × ℝ => Real.exp ((p.2-p.1)^2/(2*T)))).mul
    (measurable_optimalMomentConvolution.comp (f := fun p : ℝ × ℝ => (p.1,p.2,T)) (by fun_prop))

theorem exists_bound_optimalSurvivalSpatialIntegrand {δ : ℝ} (hδ : 0 < δ) (U : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T ∈ Icc δ U, ∀ p : ℝ × ℝ,
      p.1 ∈ Ioo (0 : ℝ) 1 → p.2 ∈ Ioo (0 : ℝ) 1 →
      ‖optimalSurvivalSpatialIntegrand T p‖ ≤ M := by
  obtain ⟨M,hM0,hM⟩ := exists_bound_optimalMomentConvolution_time U
  refine ⟨Real.exp (1/(2*δ))*M,by positivity,?_⟩
  intro T hT p ha hb
  have hp1 : 0 ≤ 1-(p.2-p.1) := by linarith [ha.1,ha.2,hb.1,hb.2]
  have hp2 : 0 ≤ 1+(p.2-p.1) := by linarith [ha.1,ha.2,hb.1,hb.2]
  have he : (p.2-p.1)^2 ≤ 1 := by nlinarith [mul_nonneg hp1 hp2]
  have hd : (p.2-p.1)^2/(2*T) ≤ 1/(2*δ) :=
    (div_le_div_of_nonneg_right he (by linarith [hT.1] : 0 ≤ 2*T)).trans
      (one_div_le_one_div_of_le (by positivity) (by linarith [hT.1]))
  unfold optimalSurvivalSpatialIntegrand
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (Real.exp_le_exp.mpr hd) (hM p.1 ha p.2 hb T hT.2)
    (norm_nonneg _) (Real.exp_nonneg _)

theorem integrable_optimalSurvivalSpatialIntegrand {T : ℝ} (hT : 0 < T) :
    Integrable (optimalSurvivalSpatialIntegrand T) optimalSurvivalSpatialMeasure := by
  obtain ⟨M,hM0,hM⟩ := exists_bound_optimalSurvivalSpatialIntegrand hT T
  exact (integrable_const M).mono' (measurable_optimalSurvivalSpatialIntegrand T).aestronglyMeasurable
    (ae_mem_optimalSurvivalSpatialMeasure.mono fun p hp => hM T ⟨le_rfl,le_rfl⟩ p hp.1 hp.2)

theorem continuousAt_optimalSurvivalSpatialIntegral {T : ℝ} (hT : 0 < T) :
    ContinuousAt optimalSurvivalSpatialIntegral T := by
  obtain ⟨M,hM0,hM⟩ := exists_bound_optimalSurvivalSpatialIntegrand (half_pos hT) (T+1)
  apply continuousAt_of_dominated (bound := fun _ => M)
  · exact Eventually.of_forall fun t => (measurable_optimalSurvivalSpatialIntegrand t).aestronglyMeasurable
  · filter_upwards [Icc_mem_nhds (by linarith : T/2 < T) (by linarith : T < T+1)] with t ht
    exact ae_mem_optimalSurvivalSpatialMeasure.mono fun p hp => hM t ht p hp.1 hp.2
  · exact integrable_const M
  · filter_upwards [ae_mem_optimalSurvivalSpatialMeasure] with p hp
    have hne : 2*T ≠ 0 := by positivity
    exact (by fun_prop : ContinuousAt (fun t : ℝ => Real.exp ((p.2-p.1)^2/(2*t))) T).mul
      (continuous_optimalMomentConvolution_time hp.1 hp.2).continuousAt

theorem optimalSurvivalSpatialIntegral_nonneg (T : ℝ) :
    0 ≤ optimalSurvivalSpatialIntegral T := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_mem_optimalSurvivalSpatialMeasure] with p hp
  exact mul_nonneg (Real.exp_nonneg _) (optimalMomentConvolution_nonneg hp.1 hp.2 T)

theorem ofReal_optimalSurvivalSpatialIntegral {T : ℝ} (hT : 0 < T) :
    ENNReal.ofReal (optimalSurvivalSpatialIntegral T)=optimalMomentSpatialConvolutionENN T := by
  unfold optimalSurvivalSpatialIntegral
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_optimalSurvivalSpatialIntegrand hT)
    (ae_mem_optimalSurvivalSpatialMeasure.mono fun p hp =>
      mul_nonneg (Real.exp_nonneg _) (optimalMomentConvolution_nonneg hp.1 hp.2 T))]
  rw [optimalSurvivalSpatialMeasure,lintegral_prod _
    (measurable_optimalSurvivalSpatialIntegrand T).ennreal_ofReal.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro a ha
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro b hb
  dsimp only [optimalSurvivalSpatialIntegrand]
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _),ofReal_optimalMomentConvolution_eq ha hb]

theorem optimalMomentSpatialConvolutionENN_ne_top {T : ℝ} (hT : 0 < T) :
    optimalMomentSpatialConvolutionENN T ≠ ∞ := by
  rw [←ofReal_optimalSurvivalSpatialIntegral hT]
  exact ENNReal.ofReal_ne_top

theorem optimalSurvivalSpatialIntegral_eq_iterated {T : ℝ} (hT : 0 < T) :
    optimalSurvivalSpatialIntegral T = ∫ a in Ioo (0 : ℝ) 1, ∫ b in Ioo (0 : ℝ) 1,
      Real.exp ((b-a)^2/(2*T))*optimalMomentConvolution a b T :=
  integral_prod _ (integrable_optimalSurvivalSpatialIntegrand hT)

theorem optimalSurvivalWidthKernelENN_eq_spatial {r : ℝ} (hr : 0 < r) :
    optimalSurvivalWidthKernelENN r = ENNReal.ofReal
      (Real.sqrt (2*Real.pi)*r/4*optimalSurvivalSpatialIntegral (1/r^2)) := by
  rw [optimalSurvivalWidthKernelENN_eq_convolution hr,ENNReal.ofReal_mul (by positivity),
    ofReal_optimalSurvivalSpatialIntegral (by positivity)]
  rfl

theorem continuousOn_optimalSurvivalWidthKernelENN :
    ContinuousOn optimalSurvivalWidthKernelENN (Ioi (0 : ℝ)) := by
  intro r hr
  change 0 < r at hr
  have hrne : r^2 ≠ 0 := pow_ne_zero 2 hr.ne'
  have hc : ContinuousAt (fun r : ℝ => ENNReal.ofReal
      (Real.sqrt (2*Real.pi)*r/4*optimalSurvivalSpatialIntegral (1/r^2))) r := by
    apply ENNReal.continuous_ofReal.continuousAt.comp
    apply ContinuousAt.mul (by fun_prop)
    exact (continuousAt_optimalSurvivalSpatialIntegral (by positivity)).comp
      (by fun_prop : ContinuousAt (fun r : ℝ => 1/r^2) r)
  apply hc.continuousWithinAt.congr
  · intro s hs
    exact optimalSurvivalWidthKernelENN_eq_spatial hs
  · exact optimalSurvivalWidthKernelENN_eq_spatial hr

end BrownianAffine
