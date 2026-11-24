import PLAStochastic.ForMathlib.MeasureTheory.Measure.PositiveLaplaceUniqueness
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Uniqueness for signed exponentially integrable functions on the positive half-line -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem integrable_laplace_positive_part {H : ℝ→ℝ} (hH : Measurable H)
    {lam : ℝ} (hi : IntegrableOn (fun t => Real.exp (-lam*t)*H t) (Ioi 0)) :
    IntegrableOn (fun t => max (H t) 0*Real.exp (-lam*t)) (Ioi 0) := by
  apply hi.norm.mono' (((hH.max measurable_const).mul (by fun_prop)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro t
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,norm_mul,Real.norm_eq_abs,abs_of_nonneg (Real.exp_nonneg _),
    abs_of_nonneg (mul_nonneg (le_max_right _ _) (Real.exp_nonneg _))]
  rw [Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (Real.exp_nonneg _)).trans_eq (mul_comm _ _)

/-- A genuine Jordan decomposition reduces signed zero-transform uniqueness to
positive-measure uniqueness; no nonnegativity of H is assumed. -/
theorem ae_zero_of_positive_laplace_zero {H : ℝ→ℝ} (hH : Measurable H)
    (hi : ∀lam : ℝ,0<lam → IntegrableOn (fun t => Real.exp (-lam*t)*H t) (Ioi 0))
    (hz : ∀lam : ℝ,0<lam → (∫ t : ℝ in Ioi 0,Real.exp (-lam*t)*H t)=0) :
    H =ᵐ[volume.restrict (Ioi (0:ℝ))] 0 := by
  let μp := (volume.restrict (Ioi (0:ℝ))).withDensity (fun t => ENNReal.ofReal (max (H t) 0))
  let μn := (volume.restrict (Ioi (0:ℝ))).withDensity (fun t => ENNReal.ofReal (max (-H t) 0))
  have hip (lam : ℝ) (hlam : 0<lam) :
      IntegrableOn (fun t => max (H t) 0*Real.exp (-lam*t)) (Ioi 0) :=
    integrable_laplace_positive_part hH (hi lam hlam)
  have hin (lam : ℝ) (hlam : 0<lam) :
      IntegrableOn (fun t => max (-H t) 0*Real.exp (-lam*t)) (Ioi 0) := by
    apply integrable_laplace_positive_part (H := fun t => -H t) hH.neg
    simpa only [mul_neg,Pi.neg_apply] using! (hi lam hlam).neg
  have hμp : ∀ᵐ t ∂μp,0≤t := by
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem measurableSet_Ioi : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),t∈Ioi (0:ℝ))] with t ht
    exact ht.le
  have hμn : ∀ᵐ t ∂μn,0≤t := by
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem measurableSet_Ioi : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),t∈Ioi (0:ℝ))] with t ht
    exact ht.le
  have hip' (lam : ℝ) (hlam : 0<lam) : Integrable (fun t : ℝ => Real.exp (-lam*t)) μp := by
    rw [integrable_withDensity_iff_integrable_smul' (by fun_prop : Measurable (fun t => ENNReal.ofReal (max (H t) 0)))
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (le_max_right _ _),smul_eq_mul] using! hip lam hlam
  have hin' (lam : ℝ) (hlam : 0<lam) : Integrable (fun t : ℝ => Real.exp (-lam*t)) μn := by
    rw [integrable_withDensity_iff_integrable_smul' (by fun_prop : Measurable (fun t => ENNReal.ofReal (max (-H t) 0)))
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (le_max_right _ _),smul_eq_mul] using! hin lam hlam
  have he : μp=μn := by
    apply measure_eq_of_positive_laplace hμp hμn hip' hin'
    intro lam hlam
    dsimp only [μp,μn]
    rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (le_max_right _ _),smul_eq_mul]
    apply sub_eq_zero.mp
    rw [←integral_sub (hip lam hlam) (hin lam hlam)]
    calc
      _ = ∫ t : ℝ in Ioi 0,Real.exp (-lam*t)*H t := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro t
        dsimp only
        rw [←sub_mul,max_zero_sub_max_neg_zero_eq_self,mul_comm]
      _ = 0 := hz lam hlam
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (hH.max measurable_const).ennreal_ofReal.aemeasurable
    (hH.neg.max measurable_const).ennreal_ofReal.aemeasurable).mp he
  filter_upwards [hae] with t ht
  have hreal := congrArg ENNReal.toReal ht
  simp only [ENNReal.toReal_ofReal (le_max_right _ _),Pi.neg_apply] at hreal
  have hzero := max_zero_sub_max_neg_zero_eq_self (H t)
  rw [hreal,sub_self] at hzero
  exact hzero.symm

/-- Equality of transforms above any fixed threshold identifies arbitrary signed
functions that are absolutely integrable with these weights. -/
theorem ae_eq_of_laplace_eq_above {F G : ℝ→ℝ} (hF : Measurable F) (hG : Measurable G) (c : ℝ)
    (hiF : ∀lam : ℝ,c<lam → IntegrableOn (fun t => Real.exp (-lam*t)*F t) (Ioi 0))
    (hiG : ∀lam : ℝ,c<lam → IntegrableOn (fun t => Real.exp (-lam*t)*G t) (Ioi 0))
    (he : ∀lam : ℝ,c<lam → (∫ t : ℝ in Ioi 0,Real.exp (-lam*t)*F t)=
      ∫ t : ℝ in Ioi 0,Real.exp (-lam*t)*G t) :
    F =ᵐ[volume.restrict (Ioi (0:ℝ))] G := by
  let H : ℝ→ℝ := fun t => Real.exp (-c*t)*(F t-G t)
  have hm : Measurable H := (by fun_prop : Measurable (fun t : ℝ => Real.exp (-c*t))).mul (hF.sub hG)
  have hpoint (lam t : ℝ) : Real.exp (-lam*t)*H t=
      Real.exp (-(lam+c)*t)*F t-Real.exp (-(lam+c)*t)*G t := by
    dsimp only [H]
    rw [←mul_assoc,←Real.exp_add,show -lam*t+-c*t=-(lam+c)*t by ring]
    ring
  have hz := ae_zero_of_positive_laplace_zero hm (by
    intro lam hlam
    simp_rw [hpoint]
    exact (hiF (lam+c) (by linarith)).sub (hiG (lam+c) (by linarith))) (by
    intro lam hlam
    simp_rw [hpoint]
    rw [integral_sub (hiF (lam+c) (by linarith)) (hiG (lam+c) (by linarith)),
      he (lam+c) (by linarith),sub_self])
  filter_upwards [hz] with t ht
  dsimp only [H,Pi.zero_apply] at ht
  exact sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_left (Real.exp_ne_zero _))

theorem eqOn_of_laplace_eq_above {F G : ℝ→ℝ} (hF : Measurable F) (hG : Measurable G) (c : ℝ)
    (hiF : ∀lam : ℝ,c<lam → IntegrableOn (fun t => Real.exp (-lam*t)*F t) (Ioi 0))
    (hiG : ∀lam : ℝ,c<lam → IntegrableOn (fun t => Real.exp (-lam*t)*G t) (Ioi 0))
    (he : ∀lam : ℝ,c<lam → (∫ t : ℝ in Ioi 0,Real.exp (-lam*t)*F t)=
      ∫ t : ℝ in Ioi 0,Real.exp (-lam*t)*G t)
    (hcF : ContinuousOn F (Ioi 0)) (hcG : ContinuousOn G (Ioi 0)) : EqOn F G (Ioi 0) :=
  MeasureTheory.Measure.eqOn_open_of_ae_eq (ae_eq_of_laplace_eq_above hF hG c hiF hiG he) isOpen_Ioi hcF hcG

/-- The parameter k=sqrt(2λ) may be restricted to any strictly positive lower bound. -/
theorem ae_eq_of_gaussian_laplace_eq_above {F G : ℝ→ℝ} (hF : Measurable F) (hG : Measurable G)
    {k₀ : ℝ} (hk₀ : 0<k₀)
    (hiF : ∀k : ℝ,k₀≤k → IntegrableOn (fun t => Real.exp (-(k^2/2)*t)*F t) (Ioi 0))
    (hiG : ∀k : ℝ,k₀≤k → IntegrableOn (fun t => Real.exp (-(k^2/2)*t)*G t) (Ioi 0))
    (he : ∀k : ℝ,k₀≤k → (∫ t : ℝ in Ioi 0,Real.exp (-(k^2/2)*t)*F t)=
      ∫ t : ℝ in Ioi 0,Real.exp (-(k^2/2)*t)*G t) :
    F =ᵐ[volume.restrict (Ioi (0:ℝ))] G := by
  have hlam {lam : ℝ} (h : k₀^2/2<lam) : 0<lam := lt_trans (by positivity) h
  have hroot {lam : ℝ} (h : k₀^2/2<lam) : k₀≤Real.sqrt (2*lam) := by
    have hs := Real.sq_sqrt (by have := hlam h; positivity : 0≤2*lam)
    have hn := Real.sqrt_nonneg (2*lam)
    nlinarith
  have hs {lam : ℝ} (h : k₀^2/2<lam) : (Real.sqrt (2*lam))^2/2=lam := by
    rw [Real.sq_sqrt (by have := hlam h; positivity)]
    ring
  apply ae_eq_of_laplace_eq_above hF hG (k₀^2/2)
  · intro lam h
    simpa only [hs h] using hiF (Real.sqrt (2*lam)) (hroot h)
  · intro lam h
    simpa only [hs h] using hiG (Real.sqrt (2*lam)) (hroot h)
  · intro lam h
    simpa only [hs h] using he (Real.sqrt (2*lam)) (hroot h)

/-- On positive time, continuity upgrades the signed uniqueness theorem to every point. -/
theorem eqOn_of_gaussian_laplace_eq_above {F G : ℝ→ℝ} (hF : Measurable F) (hG : Measurable G)
    {k₀ : ℝ} (hk₀ : 0<k₀)
    (hiF : ∀k : ℝ,k₀≤k → IntegrableOn (fun t => Real.exp (-(k^2/2)*t)*F t) (Ioi 0))
    (hiG : ∀k : ℝ,k₀≤k → IntegrableOn (fun t => Real.exp (-(k^2/2)*t)*G t) (Ioi 0))
    (he : ∀k : ℝ,k₀≤k → (∫ t : ℝ in Ioi 0,Real.exp (-(k^2/2)*t)*F t)=
      ∫ t : ℝ in Ioi 0,Real.exp (-(k^2/2)*t)*G t)
    (hcF : ContinuousOn F (Ioi 0)) (hcG : ContinuousOn G (Ioi 0)) : EqOn F G (Ioi 0) :=
  MeasureTheory.Measure.eqOn_open_of_ae_eq
    (ae_eq_of_gaussian_laplace_eq_above hF hG hk₀ hiF hiG he) isOpen_Ioi hcF hcG

end BrownianAffine
