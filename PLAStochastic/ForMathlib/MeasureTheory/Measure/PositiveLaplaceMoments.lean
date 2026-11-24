import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- An explicit factorial majorant for every polynomial times an exponential. -/
theorem pow_mul_exp_neg_le_factorial {c t : ℝ} (hc : 0<c) (ht : 0≤t) (n : ℕ) :
    t^n*Real.exp (-c*t)≤(n.factorial:ℝ)/c^n := by
  have hf : (0:ℝ)<n.factorial := by positivity
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (c*t) (mul_nonneg hc.le ht) n)
  apply (le_div_iff₀ (pow_pos hc n)).mpr
  calc
    _ = (c*t)^n*Real.exp (-c*t) := by rw [mul_pow]; ring
    _ ≤ (Real.exp (c*t)*(n.factorial:ℝ))*Real.exp (-c*t) :=
      mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
    _ = _ := by rw [mul_assoc,mul_comm (n.factorial:ℝ),←mul_assoc,←Real.exp_add]; simp

private theorem pow_exp_parameter_bound {lam a t : ℝ} (hlam : 0<lam)
    (ha : lam/2≤a) (ht : 0≤t) (n : ℕ) :
    t^n*Real.exp (-a*t)≤((n.factorial:ℝ)/(lam/4)^n)*Real.exp (-(lam/4)*t) := by
  have hc : 0<lam/4 := by positivity
  have hb := pow_mul_exp_neg_le_factorial hc ht n
  calc
    _ ≤ t^n*Real.exp (-(lam/4)*t + -(lam/4)*t) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (pow_nonneg ht n)
    _ = (t^n*Real.exp (-(lam/4)*t))*Real.exp (-(lam/4)*t) := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)

def positiveLaplaceMoment (G : ℝ→ℝ) (n : ℕ) (lam : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ), t^n*Real.exp (-lam*t)*G t

variable {G : ℝ→ℝ} (hG : Measurable G) (hGn : ∀t,0<t→0≤G t)
    (hGi : ∀lam,0<lam→IntegrableOn (fun t => Real.exp (-lam*t)*G t) (Ioi 0))

include hG hGn hGi

/-- All polynomially weighted Laplace integrals are finite, from exponential
integrability at smaller positive parameters. -/
theorem integrableOn_positiveLaplaceMoment {lam : ℝ} (hlam : 0<lam) (n : ℕ) :
    IntegrableOn (fun t => t^n*Real.exp (-lam*t)*G t) (Ioi 0) := by
  have hm : Measurable (fun t => t^n*Real.exp (-lam*t)*G t) := (by fun_prop : Measurable (fun t : ℝ => t^n*Real.exp (-lam*t))).mul hG
  apply ((hGi (lam/4) (by positivity)).const_mul ((n.factorial:ℝ)/(lam/4)^n)).mono'
    hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht.le n) (Real.exp_nonneg _)) (hGn t ht))]
  calc
    _ ≤ (((n.factorial:ℝ)/(lam/4)^n)*Real.exp (-(lam/4)*t))*G t :=
      mul_le_mul_of_nonneg_right (pow_exp_parameter_bound hlam (by linarith) ht.le n) (hGn t ht)
    _ = _ := by ring

/-- The nth time moment has a genuine dominated parameter derivative equal to
minus the next time moment. -/
theorem hasDerivAt_positiveLaplaceMoment {lam : ℝ} (hlam : 0<lam) (n : ℕ) :
    HasDerivAt (positiveLaplaceMoment G n) (-positiveLaplaceMoment G (n+1) lam) lam := by
  let F : ℝ→ℝ→ℝ := fun a t => t^n*Real.exp (-a*t)*G t
  let D : ℝ→ℝ→ℝ := fun a t => -(t^(n+1)*Real.exp (-a*t)*G t)
  have hm (a : ℝ) : Measurable (F a) := (by fun_prop : Measurable (fun t : ℝ => t^n*Real.exp (-a*t))).mul hG
  have hdM (a : ℝ) : Measurable (D a) := ((by fun_prop : Measurable (fun t : ℝ => t^(n+1)*Real.exp (-a*t))).mul hG).neg
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), ∀a∈Ioo (lam/2) (2*lam),
      ‖D a t‖≤((n+1).factorial:ℝ)/(lam/4)^(n+1)*(Real.exp (-(lam/4)*t)*G t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht a ha
    change ‖-(t^(n+1)*Real.exp (-a*t)*G t)‖≤_
    rw [norm_neg,Real.norm_of_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht.le _) (Real.exp_nonneg _)) (hGn t ht))]
    calc
      _ ≤ (((n+1).factorial:ℝ)/(lam/4)^(n+1)*Real.exp (-(lam/4)*t))*G t :=
        mul_le_mul_of_nonneg_right (pow_exp_parameter_bound hlam ha.1.le ht.le (n+1)) (hGn t ht)
      _ = _ := by ring
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), ∀a∈Ioo (lam/2) (2*lam),
      HasDerivAt (F · t) (D a t) a := by
    filter_upwards [] with t a ha
    convert! (((((hasDerivAt_id a).neg).mul_const t).exp).const_mul (t^n)).mul_const (G t) using 1
    simp only [D,Pi.neg_apply,id_eq,pow_succ]
    ring
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : lam/2<lam) (by linarith : lam<2*lam))
    (Eventually.of_forall fun a => (hm a).aestronglyMeasurable)
    (integrableOn_positiveLaplaceMoment hG hGn hGi hlam n)
    (hdM lam).aestronglyMeasurable hbound
    ((hGi (lam/4) (by positivity)).const_mul (((n+1).factorial:ℝ)/(lam/4)^(n+1))) hderiv
  change HasDerivAt (fun a => ∫ t in Ioi (0:ℝ), t^n*Real.exp (-a*t)*G t)
    (-(∫ t in Ioi (0:ℝ), t^(n+1)*Real.exp (-lam*t)*G t)) lam
  simpa only [F,D,integral_neg] using hd.2

end BrownianAffine
