import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.CenteredCoth.Asymptotics
import Mathlib.MeasureTheory.Integral.Asymptotics

/-! # Quantified cotangent tails and an absolute-integrability criterion -/
noncomputable section
open MeasureTheory Filter Set Asymptotics
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The exponentially small correction in the true centered cotangent remains small
when multiplied by the quadratic factor needed by the moment integrands. -/
theorem tendsto_centeredCoth_quadratic_error :
    Tendsto (fun x : ℝ => x^2*(centeredCoth x-1+1/x)) atTop (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-2*x)) atTop (𝓝 0) := by
    convert! Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)) using 1
    simp [Function.comp_def]
  have hx : Tendsto (fun x : ℝ => x^2*Real.exp (-2*x)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    convert! h.div_const 4 using 1
    · funext x
      simp only [Function.comp_def,id]
      ring_nf
    · norm_num
  have hlim : Tendsto (fun x : ℝ => 2*(x^2*Real.exp (-2*x))/(1-Real.exp (-2*x)))
      atTop (𝓝 0) := by
    simpa only [mul_zero,sub_zero,zero_div] using! (hx.const_mul 2).div
      (tendsto_const_nhds.sub he) (by norm_num : (1 : ℝ)-0 ≠ 0)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [centeredCoth_eq_exp hx]
  have hn : 1-Real.exp (-2*x) ≠ 0 := by
    have hh : Real.exp (-2*x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  set y := Real.exp (-2*x) with hy
  change 2*(x^2*y)/(1-y) = x^2*((1+y)/(1-y)-1/x-1+1/x)
  field_simp [hn,hx.ne']
  ring

/-- A continuous function with a finite quadratic tail is absolutely integrable on the positive axis. -/
theorem integrableOn_Ioi_of_quadratic_tail {f : ℝ → ℝ} (hf : Continuous f) {L : ℝ}
    (ht : Tendsto (fun x : ℝ => (1+x^2)*f x) atTop (𝓝 L)) :
    IntegrableOn f (Ioi 0) volume := by
  have ho : f =O[atTop] (fun x : ℝ => 1/(1+x^2)) := by
    apply isBigO_of_div_tendsto_nhds (c := L)
    · apply Eventually.of_forall
      intro x hx
      have hn : (1 : ℝ)/(1+x^2) ≠ 0 := by positivity
      exact (hn hx).elim
    · convert! ht using 1
      funext x
      change f x/(1/(1+x^2)) = (1+x^2)*f x
      rw [div_div_eq_mul_div,div_one,mul_comm]
  have hg : IntegrableAtFilter (fun x : ℝ => 1/(1+x^2)) atTop volume :=
    ⟨univ,Filter.univ_mem,by simpa only [IntegrableOn,Measure.restrict_univ,one_div] using integrable_inv_one_add_sq⟩
  exact ((hf.continuousOn.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop ho hg).mono_set Ioi_subset_Ici_self

end BrownianAffine
