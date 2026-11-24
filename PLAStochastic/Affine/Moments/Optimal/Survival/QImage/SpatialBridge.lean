import PLAStochastic.Affine.Moments.Optimal.Survival.QImage.Convergence
import PLAStochastic.Affine.Moments.Optimal.Survival.QImage.SeriesLaplace
import PLAStochastic.Affine.Moments.Optimal.Survival.Kernel.ExactKernel
import PLAStochastic.Affine.Moments.Optimal.Survival.Spatial.SignedIntegral

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem optimalQImageSeries_eq_convolution {x y T : ℝ}
    (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) (hT : 0 < T) :
    optimalQImageSeries x y T = optimalMomentConvolution (1-x) y T := by
  have ha : 1-x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hxa : |x| ≤ 1 := by rw [abs_of_pos hx.1]; exact hx.2.le
  have hya : |y| ≤ 1 := by rw [abs_of_pos hy.1]; exact hy.2.le
  exact eqOn_open_of_ae_eq (optimalQImageSeries_eq_convolution_ae hx hy) isOpen_Ioi
    (fun t ht => (continuousAt_optimalQImageSeries_time hxa hya ht).continuousWithinAt)
    (continuous_optimalMomentConvolution_time ha hy).continuousOn hT

def optimalQImageWeightedMode (n : ℕ) (T : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp ((p.1+p.2-1)^2/(2*T))*optimalQImageMode n p.1 p.2 T

theorem measurable_optimalQImageWeightedMode (n : ℕ) (T : ℝ) :
    Measurable (optimalQImageWeightedMode n T) :=
  (by fun_prop : Measurable (fun p : ℝ × ℝ => Real.exp ((p.1+p.2-1)^2/(2*T)))).mul
    ((measurable_optimalQImageMode n).comp (f := fun p : ℝ × ℝ => (p.1,p.2,T)) (by fun_prop))

theorem norm_optimalQImageWeightedMode_bound (n : ℕ) {T : ℝ} (hT : 0 < T)
    {p : ℝ × ℝ} (hx : p.1 ∈ Ioo 0 1) (hy : p.2 ∈ Ioo 0 1) :
    ‖optimalQImageWeightedMode n T p‖ ≤ Real.exp (1/(2*T))*optimalQImageGaussianBound T T n := by
  have hxa : |p.1| ≤ 1 := by rw [abs_of_pos hx.1]; exact hx.2.le
  have hya : |p.2| ≤ 1 := by rw [abs_of_pos hy.1]; exact hy.2.le
  have hp : (p.1+p.2-1)^2 ≤ 1 := by
    have h₁ : 0 ≤ 1-(p.1+p.2-1) := by linarith [hx.2,hy.2]
    have h₂ : 0 ≤ 1+(p.1+p.2-1) := by linarith [hx.1,hy.1]
    nlinarith [mul_nonneg h₁ h₂]
  unfold optimalQImageWeightedMode
  rw [norm_mul,Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_mul (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hp (by positivity)))
    (norm_optimalQImageMode_bound n hT hxa hya ⟨le_rfl,le_rfl⟩) (norm_nonneg _) (Real.exp_nonneg _)

theorem integrable_optimalQImageWeightedMode (n : ℕ) {T : ℝ} (hT : 0 < T) :
    Integrable (optimalQImageWeightedMode n T) optimalSurvivalSpatialMeasure :=
  (integrable_const (Real.exp (1/(2*T))*optimalQImageGaussianBound T T n)).mono'
    (measurable_optimalQImageWeightedMode n T).aestronglyMeasurable
    (ae_mem_optimalSurvivalSpatialMeasure.mono fun _ hp => norm_optimalQImageWeightedMode_bound n hT hp.1 hp.2)

/-- Finite-measure dominated convergence justifies the genuine spatial series exchange. -/
theorem hasSum_integral_optimalQImageWeightedMode {T : ℝ} (hT : 0 < T) :
    HasSum (fun n => ∫ p,optimalQImageWeightedMode n T p ∂optimalSurvivalSpatialMeasure)
      (∫ p : ℝ × ℝ,Real.exp ((p.1+p.2-1)^2/(2*T))*optimalQImageSeries p.1 p.2 T
        ∂optimalSurvivalSpatialMeasure) := by
  apply hasSum_integral_of_dominated_convergence
    (fun n _ => Real.exp (1/(2*T))*optimalQImageGaussianBound T T n)
  · intro n
    exact (measurable_optimalQImageWeightedMode n T).aestronglyMeasurable
  · intro n
    exact ae_mem_optimalSurvivalSpatialMeasure.mono fun _ hp => norm_optimalQImageWeightedMode_bound n hT hp.1 hp.2
  · exact Eventually.of_forall fun _ => (summable_optimalQImageGaussianBound hT hT).mul_left _
  · exact integrable_const _
  · filter_upwards [ae_mem_optimalSurvivalSpatialMeasure] with p hp
    have hx : |p.1| ≤ 1 := by rw [abs_of_pos hp.1.1]; exact hp.1.2.le
    have hy : |p.2| ≤ 1 := by rw [abs_of_pos hp.2.1]; exact hp.2.2.le
    exact (summable_optimalQImageMode hx hy hT).hasSum.mul_left _

theorem optimalSurvivalSpatialMeasure_eq_square :
    optimalSurvivalSpatialMeasure = volume.restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  unfold optimalSurvivalSpatialMeasure
  simp only [restrict_Ioo_eq_restrict_Icc,Measure.prod_restrict,Measure.volume_eq_prod]

theorem optimalQImage_weighted_base_factor (C B L d : ℝ) {T : ℝ} (hT : 0 < T) :
    (Real.sqrt (2*Real.pi)/(4*Real.sqrt T))*16*Real.exp (d^2/(2*T))*
      ((C*L/T-B)*optimalQImageGaussian L T) =
      4/T^2*((C*L-B*T)*Real.exp (-(L^2-d^2)/(2*T))) := by
  have hπ : 0 < 2*Real.pi := by positivity
  have hsq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  have he : Real.exp (-(L^2-d^2)/(2*T))=Real.exp (d^2/(2*T))*Real.exp (-L^2/(2*T)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  unfold optimalQImageGaussian
  rw [he,Real.sqrt_mul hπ.le]
  field_simp
  rw [hsq]
  ring

theorem optimalQImageWeightedMode_factor (n : ℕ) {T : ℝ} (hT : 0 < T) (p : ℝ × ℝ) :
    Real.sqrt (2*Real.pi)/(4*Real.sqrt T)*optimalQImageWeightedMode n T p =
      4/T^2*optimalImageSpatialTerm n T p := by
  have hp := optimalQImage_weighted_base_factor (optimalQImageCoefficientC n)
    (optimalQImageCoefficientB n) (optimalQImageLength n p.1 p.2) (p.1+p.2-1) hT
  have hm := optimalQImage_weighted_base_factor (optimalQImageCoefficientC n)
    (optimalQImageCoefficientB n) (optimalQImageLength n (-p.1) (-p.2)) (p.1+p.2-1) hT
  have hpm := optimalQImage_weighted_base_factor (optimalQImageCoefficientC n)
    (optimalQImageCoefficientB n) (optimalQImageLength n p.1 (-p.2)) (p.1+p.2-1) hT
  have hmp := optimalQImage_weighted_base_factor (optimalQImageCoefficientC n)
    (optimalQImageCoefficientB n) (optimalQImageLength n (-p.1) p.2) (p.1+p.2-1) hT
  dsimp only [optimalQImageWeightedMode,optimalQImageMode,optimalQImageBase,
    optimalImageSpatialTerm,Pi.add_apply,Pi.sub_apply,optimalImageSpatialSigned,one_mul,neg_one_mul]
  simp only [one_mul,neg_one_mul]
  linear_combination hp + hm - hpm - hmp

theorem integral_optimalQImageWeightedMode_factor (n : ℕ) {T : ℝ} (hT : 0 < T) :
    Real.sqrt (2*Real.pi)/(4*Real.sqrt T)*
      (∫ p,optimalQImageWeightedMode n T p ∂optimalSurvivalSpatialMeasure)=optimalImageSpatialMode n T := by
  unfold optimalImageSpatialMode imageUnitSquareIntegral
  rw [optimalSurvivalSpatialMeasure_eq_square,←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (optimalQImageWeightedMode_factor n hT)

def optimalImageSpatialReflection : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.subLeft (1 : ℝ)).prodCongr (MeasurableEquiv.refl ℝ)

theorem measurePreserving_optimalImageSpatialReflection :
    MeasurePreserving optimalImageSpatialReflection optimalSurvivalSpatialMeasure optimalSurvivalSpatialMeasure := by
  have h₁ := (volume.measurePreserving_sub_left (1 : ℝ)).restrict_preimage
    (s := Ioo 0 1) measurableSet_Ioo
  have he : (fun t : ℝ => 1-t) ⁻¹' Ioo 0 1=Ioo 0 1 := by
    ext t
    simp only [mem_preimage,mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [he] at h₁
  exact h₁.prod (MeasurePreserving.id (volume.restrict (Ioo (0 : ℝ) 1)))

theorem integral_optimalQImageSeries_spatial {T : ℝ} (hT : 0 < T) :
    (∫ p : ℝ × ℝ,Real.exp ((p.1+p.2-1)^2/(2*T))*optimalQImageSeries p.1 p.2 T
      ∂optimalSurvivalSpatialMeasure) = optimalSurvivalSpatialIntegral T := by
  calc
    _ = ∫ p,optimalSurvivalSpatialIntegrand T (optimalImageSpatialReflection p)
        ∂optimalSurvivalSpatialMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_mem_optimalSurvivalSpatialMeasure] with p hp
      rw [optimalQImageSeries_eq_convolution hp.1 hp.2 hT]
      change Real.exp ((p.1+p.2-1)^2/(2*T))*optimalMomentConvolution (1-p.1) p.2 T =
        Real.exp ((p.2-(1-p.1))^2/(2*T))*optimalMomentConvolution (1-p.1) p.2 T
      congr 2
      ring
    _ = _ := measurePreserving_optimalImageSpatialReflection.integral_comp' (optimalSurvivalSpatialIntegrand T)

theorem hasSum_optimalImageSpatialMode_survival {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {T : ℝ} (hT : 0 < T) :
    HasSum (fun n => optimalImageSpatialMode n T) (μ.real {ω | 4*T < optimalUnitLifetime B ω}) := by
  have hh := (hasSum_integral_optimalQImageWeightedMode hT).mul_left
    (Real.sqrt (2*Real.pi)/(4*Real.sqrt T))
  simp only [integral_optimalQImageWeightedMode_factor _ hT,integral_optimalQImageSeries_spatial hT] at hh
  have he : μ.real {ω | 4*T < optimalUnitLifetime B ω}=
      Real.sqrt (2*Real.pi)/(4*Real.sqrt T)*optimalSurvivalSpatialIntegral T := by
    rw [measureReal_optimalUnitLifetime_survival_kernel hB hT,
      optimalSurvivalSpatialIntegral_eq_iterated hT]
  rwa [←he] at hh

theorem measureReal_optimalUnitLifetime_eq_spatial_series {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {T : ℝ} (hT : 0 < T) :
    μ.real {ω | 4*T < optimalUnitLifetime B ω}=∑' n,optimalImageSpatialMode n T :=
  (hasSum_optimalImageSpatialMode_survival hB hT).tsum_eq.symm

end BrownianAffine
