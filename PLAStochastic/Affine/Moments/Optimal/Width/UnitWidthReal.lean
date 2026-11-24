import PLAStochastic.Affine.Moments.Optimal.Width.UnitWidth

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalMomentUnitMeasure : Measure (ℝ×ℝ×ℝ) :=
  (volume.restrict (Ioo (0:ℝ) 1)).prod
    ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ))))

def optimalMomentUnitIntegrand (q : ℝ) (p : ℝ×ℝ×ℝ) : ℝ :=
  p.2.2^(q-3/2)*Real.exp ((p.2.1-p.1)^2/(2*p.2.2))*optimalMomentConvolution p.1 p.2.1 p.2.2

def optimalMomentUnitIntegrandENN (q : ℝ) (p : ℝ×ℝ×ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (p.2.2^(q-3/2)) *
    (ENNReal.ofReal (Real.exp ((p.2.1-p.1)^2/(2*p.2.2)))*optimalMomentConvolutionENN p.1 p.2.1 p.2.2)

theorem measurable_optimalMomentUnitIntegrand (q : ℝ) : Measurable (optimalMomentUnitIntegrand q) := by
  exact (by fun_prop : Measurable (fun p : ℝ×ℝ×ℝ => p.2.2^(q-3/2)*Real.exp ((p.2.1-p.1)^2/(2*p.2.2)))).mul
    measurable_optimalMomentConvolution

theorem measurable_optimalMomentUnitIntegrandENN (q : ℝ) : Measurable (optimalMomentUnitIntegrandENN q) := by
  exact (by fun_prop : Measurable (fun p : ℝ×ℝ×ℝ => ENNReal.ofReal (p.2.2^(q-3/2)))).mul
    ((by fun_prop : Measurable (fun p : ℝ×ℝ×ℝ => ENNReal.ofReal (Real.exp ((p.2.1-p.1)^2/(2*p.2.2))))).mul
      measurable_optimalMomentConvolutionENN)

theorem optimalMomentUnitIntegrand_nonneg_ae (q : ℝ) :
    0≤ᵐ[optimalMomentUnitMeasure] optimalMomentUnitIntegrand q := by
  change ∀ᵐ p ∂optimalMomentUnitMeasure, (0:ℝ)≤optimalMomentUnitIntegrand q p
  apply (ae_prod_iff_ae_ae (measurableSet_le measurable_const (measurable_optimalMomentUnitIntegrand q))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
  apply (ae_prod_iff_ae_ae (measurableSet_le measurable_const
    ((measurable_optimalMomentUnitIntegrand q).comp measurable_prodMk_left))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with b hb
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hT.le _) (Real.exp_nonneg _))
    (optimalMomentConvolution_nonneg ha hb T)

theorem optimalMomentUnitIntegrand_ofReal_ae (q : ℝ) :
    (fun p => ENNReal.ofReal (optimalMomentUnitIntegrand q p)) =ᵐ[optimalMomentUnitMeasure]
      optimalMomentUnitIntegrandENN q := by
  apply (ae_prod_iff_ae_ae (measurableSet_eq_fun (measurable_optimalMomentUnitIntegrand q).ennreal_ofReal
    (measurable_optimalMomentUnitIntegrandENN q))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
  apply (ae_prod_iff_ae_ae (measurableSet_eq_fun
    (((measurable_optimalMomentUnitIntegrand q).ennreal_ofReal).comp measurable_prodMk_left)
    ((measurable_optimalMomentUnitIntegrandENN q).comp measurable_prodMk_left))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with b hb
  filter_upwards [ae_restrict_mem measurableSet_Ioi,ofReal_optimalMomentConvolution_eq_ae ha hb] with T hT hQ
  change ENNReal.ofReal (T^(q-3/2)*Real.exp ((b-a)^2/(2*T))*optimalMomentConvolution a b T)=_
  rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hT.le _) (Real.exp_nonneg _)),
    ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _),hQ,mul_assoc]
  rfl

/-- Tonelli moves the unit-width spatial integrals outside the time integral. -/
theorem lintegral_optimalMomentUnitIntegrandENN (q : ℝ) :
    (∫⁻ T in Ioi (0:ℝ), ENNReal.ofReal (T^(q-3/2))*optimalMomentSpatialConvolutionENN T)=
      ∫⁻ p, optimalMomentUnitIntegrandENN q p ∂optimalMomentUnitMeasure := by
  have hm := measurable_optimalMomentUnitIntegrandENN q
  have hpoint (T : ℝ) : ENNReal.ofReal (T^(q-3/2))*optimalMomentSpatialConvolutionENN T=
      ∫⁻ a in Ioo (0:ℝ) 1, ∫⁻ b in Ioo (0:ℝ) 1, optimalMomentUnitIntegrandENN q (a,b,T) := by
    unfold optimalMomentSpatialConvolutionENN
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro a ha
    dsimp only
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  simp only [hpoint]
  have hM : Measurable (fun p : (ℝ×ℝ)×ℝ => optimalMomentUnitIntegrandENN q (p.1.2,p.2,p.1.1)) :=
    hm.comp (by fun_prop)
  have hMa : Measurable (fun p : ℝ×ℝ => ∫⁻ b in Ioo (0:ℝ) 1,
      optimalMomentUnitIntegrandENN q (p.2,b,p.1)) := hM.lintegral_prod_right'
  rw [lintegral_lintegral_swap hMa.aemeasurable]
  change _=∫⁻ p, optimalMomentUnitIntegrandENN q p ∂(volume.restrict (Ioo (0:ℝ) 1)).prod
    ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ))))
  rw [lintegral_prod _ hm.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro a ha
  dsimp only
  have hMb : Measurable (fun p : ℝ×ℝ => optimalMomentUnitIntegrandENN q (a,p.2,p.1)) := hm.comp (by fun_prop)
  rw [lintegral_lintegral_swap hMb.aemeasurable]
  exact (lintegral_prod _ (hm.comp measurable_prodMk_left).aemeasurable).symm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0→Ω→ℝ}

theorem optimalUnitLifetime_moment_unitIntegralENN (hB : IsBrownianReal B μ) {q : ℝ} (hq : 0<q) :
    (∫⁻ ω, ENNReal.ofReal (optimalUnitLifetime B ω^q) ∂μ)=
      ENNReal.ofReal ((2:ℝ)^(2*q-2)*q*Real.sqrt (2*Real.pi))*
        ∫⁻ p, ENNReal.ofReal (optimalMomentUnitIntegrand q p) ∂optimalMomentUnitMeasure := by
  rw [optimalUnitLifetime_moment_unitWidth_lintegral hB hq,lintegral_optimalMomentUnitIntegrandENN,
    lintegral_congr_ae (optimalMomentUnitIntegrand_ofReal_ae q)]

/-- The actual positive-order moment controls the entire unit-width integrand,
so every required Fubini exchange is absolutely integrable. -/
theorem integrable_optimalMomentUnitIntegrand (hB : IsBrownianReal B μ) {q : ℝ} (hq : 0<q) :
    Integrable (optimalMomentUnitIntegrand q) optimalMomentUnitMeasure := by
  have hi := optimalUnitLifetime_integrable_rpow hB hq.le
  have hn : 0≤ᵐ[μ] (fun ω => optimalUnitLifetime B ω^q) :=
    Eventually.of_forall fun ω => Real.rpow_nonneg (optimalUnitLifetime_nonnegative B ω) q
  have hfin := (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hn).mpr hi
  rw [optimalUnitLifetime_moment_unitIntegralENN hB hq] at hfin
  exact (lintegral_ofReal_ne_top_iff_integrable (measurable_optimalMomentUnitIntegrand q).aestronglyMeasurable
    (optimalMomentUnitIntegrand_nonneg_ae q)).mp
    (ENNReal.lt_top_of_mul_ne_top_right hfin (by positivity)).ne

/-- The paper's real unit-width moment formula, for every positive real q. -/
theorem optimalUnitLifetime_moment_unitWidth (hB : IsBrownianReal B μ) {q : ℝ} (hq : 0<q) :
    (∫ ω, optimalUnitLifetime B ω^q ∂μ)=
      (2:ℝ)^(2*q-2)*q*Real.sqrt (2*Real.pi)*
        ∫ a in Ioo (0:ℝ) 1, ∫ b in Ioo (0:ℝ) 1, ∫ T in Ioi (0:ℝ),
          T^(q-3/2)*Real.exp ((b-a)^2/(2*T))*optimalMomentConvolution a b T := by
  have hi := integrable_optimalMomentUnitIntegrand hB hq
  have hl := optimalUnitLifetime_integrable_rpow hB hq.le
  have he := congrArg ENNReal.toReal (optimalUnitLifetime_moment_unitIntegralENN hB hq)
  rw [←integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun ω => Real.rpow_nonneg (optimalUnitLifetime_nonnegative B ω) q) hl.aestronglyMeasurable,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),
    ←integral_eq_lintegral_of_nonneg_ae (optimalMomentUnitIntegrand_nonneg_ae q) hi.aestronglyMeasurable] at he
  rw [he]
  congr 1
  change (∫ p, optimalMomentUnitIntegrand q p ∂(volume.restrict (Ioo (0:ℝ) 1)).prod
    ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))))=_
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with a hIa
  exact integral_prod _ hIa

end BrownianAffine
