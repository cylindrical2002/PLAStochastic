import PLAStochastic.Swing.Gaussian.Tail.ExcessTailShift
import PLAStochastic.ForMathlib.Probability.Moments.SubGaussianExpMoment

/-! # Uniform first, second and exponential moments of actual Gaussian excesses -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The translated exponential is integrable under the original Gaussian law. -/
theorem gaussianExpShift_integrable (r θ : ℝ) :
    Integrable (fun x : ℝ => Real.exp (θ*(x-r))) (gaussianReal 0 1) := by
  have h := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) θ).mul_const (Real.exp (-θ*r))
  simpa only [← Real.exp_add, show ∀ x : ℝ, θ*x+ -θ*r = θ*(x-r) by intro x; ring] using! h

/-- Every fixed conditional excess law has all exponential moments by actual Gaussian integration. -/
theorem gaussianExcessLaw_integrable_exp (r θ : ℝ) :
    Integrable (fun x => Real.exp (θ*x)) (gaussianExcessLaw r) := by
  change Integrable (fun x => Real.exp (θ*x)) (((gaussianReal 0 1)[|Ioi r]).map (fun x => x-r))
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  exact (gaussianExpShift_integrable r θ).integrableOn.smul_measure
    (ENNReal.inv_ne_top.mpr (gaussianReal_Ioi_pos r).ne')

/-- Exact conditional expectation formula under restriction and translation. -/
theorem gaussianExcessLaw_exp_moment_eq (r θ : ℝ) :
    (∫ x, Real.exp (θ*x) ∂gaussianExcessLaw r) =
      ((gaussianReal 0 1).real (Ioi r))⁻¹ * ∫ x in Ioi r, Real.exp (θ*(x-r)) ∂gaussianReal 0 1 := by
  rw [gaussianExcessLaw, integral_map (by fun_prop) (by fun_prop), ProbabilityTheory.cond, integral_smul_measure]
  simp only [ENNReal.toReal_inv, measureReal_def, smul_eq_mul]

/-- The unrestricted shifted exponential has its actual Gaussian MGF value. -/
theorem gaussianExpShift_integral (r θ : ℝ) :
    (∫ x, Real.exp (θ*(x-r)) ∂gaussianReal 0 1) = Real.exp (-θ*r+θ^2/2) := by
  simp_rw [show ∀ x : ℝ, θ*(x-r) = -θ*r+θ*x by intro x; ring, Real.exp_add]
  rw [integral_const_mul]
  have hg : (∫ x, Real.exp (θ*x) ∂gaussianReal 0 1) = Real.exp (θ^2/2) := by
    simpa only [mgf, id_eq, zero_mul, NNReal.coe_one, one_mul, zero_add] using
      congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) θ
  rw [hg, ← Real.exp_add]

/-- Closed integer tails follow from the strict Gaussian bound without an atomlessness assumption. -/
theorem gaussianExcessLaw_closed_nat_tail {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    gaussianExcessLaw r {x | (n : ℝ) ≤ x} ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)^2/8)) := by
  by_cases hn : n = 0
  · subst n
    simpa using (prob_le_one (μ := gaussianExcessLaw r) (s := {x : ℝ | (0 : ℝ) ≤ x}))
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc
    _ ≤ gaussianExcessLaw r (Ioi ((n : ℝ)/2)) := by
      apply measure_mono
      intro x hx
      change (n : ℝ)/2 < x
      change (n : ℝ) ≤ x at hx
      linarith
    _ ≤ ENNReal.ofReal (Real.exp (-((n : ℝ)/2)^2/2)) :=
      gaussianExcessLaw_tail_le hr (by positivity)
    _ = ENNReal.ofReal (Real.exp (-(n : ℝ)^2/8)) := by congr 2; ring

/-- A common exponential-moment bound for all nonnegative thresholds. -/
theorem gaussianExcessLaw_exp_moment_le_of_nonneg {r θ : ℝ} (hr : 0 ≤ r) (hθ : 0 ≤ θ) :
    (∫ x, Real.exp (θ*x) ∂gaussianExcessLaw r) ≤ (subGaussianTailExpBound θ).toReal :=
  integral_exp_le_subGaussianTailExpBound measurable_id
    ((gaussianExcessLaw_positive_ae r).mono fun _ h => h.le) (gaussianExcessLaw_closed_nat_tail hr) hθ

/-- A finite fixed reference tail controls the bounded negative threshold range. -/
theorem gaussianExcessLaw_exp_moment_le_of_nonpos {r θ : ℝ}
    (hr : -(1/2 : ℝ) ≤ r) (hr0 : r ≤ 0) (hθ : 0 ≤ θ) :
    (∫ x, Real.exp (θ*x) ∂gaussianExcessLaw r) ≤
      ((gaussianReal 0 1).real (Ioi 0))⁻¹ * Real.exp (θ/2+θ^2/2) := by
  have hden : 0 < (gaussianReal 0 1).real (Ioi 0) :=
    ENNReal.toReal_pos (gaussianReal_Ioi_pos 0).ne' (measure_ne_top _ _)
  have hmon : (gaussianReal 0 1).real (Ioi 0) ≤ (gaussianReal 0 1).real (Ioi r) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Ioi_subset_Ioi hr0))
  rw [gaussianExcessLaw_exp_moment_eq]
  calc
    _ ≤ ((gaussianReal 0 1).real (Ioi r))⁻¹ *
        ∫ x, Real.exp (θ*(x-r)) ∂gaussianReal 0 1 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
      exact integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun _ => (Real.exp_pos _).le) (gaussianExpShift_integrable r θ)
    _ = ((gaussianReal 0 1).real (Ioi r))⁻¹ * Real.exp (-θ*r+θ^2/2) := by
      rw [gaussianExpShift_integral]
    _ ≤ ((gaussianReal 0 1).real (Ioi 0))⁻¹ * Real.exp (θ/2+θ^2/2) := by
      apply mul_le_mul (inv_anti₀ hden hmon) _ (Real.exp_pos _).le (inv_nonneg.mpr hden.le)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hr hθ]

/-- One explicit common constant for every threshold r≥-1/2. -/
def gaussianExcessExpMomentBound (θ : ℝ) : ℝ :=
  (subGaussianTailExpBound θ).toReal + ((gaussianReal 0 1).real (Ioi 0))⁻¹ * Real.exp (θ/2+θ^2/2)

theorem gaussianExcessExpMomentBound_pos (θ : ℝ) : 0 < gaussianExcessExpMomentBound θ := by
  have hp : 0 < (gaussianReal 0 1).real (Ioi 0) :=
    ENNReal.toReal_pos (gaussianReal_Ioi_pos 0).ne' (measure_ne_top _ _)
  exact add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg (mul_pos (inv_pos.mpr hp) (Real.exp_pos _))

/-- Uniform exponential expectation bound, including the negative thresholds required at strip exit. -/
theorem gaussianExcessLaw_exp_moment_le {r θ : ℝ} (hr : -(1/2 : ℝ) ≤ r) (hθ : 0 ≤ θ) :
    (∫ x, Real.exp (θ*x) ∂gaussianExcessLaw r) ≤ gaussianExcessExpMomentBound θ := by
  by_cases hr0 : 0 ≤ r
  · apply (gaussianExcessLaw_exp_moment_le_of_nonneg hr0 hθ).trans
    exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (Real.exp_pos _).le)
  · apply (gaussianExcessLaw_exp_moment_le_of_nonpos hr (le_of_not_ge hr0) hθ).trans
    exact le_add_of_nonneg_left ENNReal.toReal_nonneg

/-- Uniform expectation control for any measurable function dominated by exp(2x) on positive x. -/
theorem gaussianExcessLaw_integral_le_of_exp_bound {r : ℝ} (hr : -(1/2 : ℝ) ≤ r)
    {f : ℝ → ℝ} (hf : Measurable f) (hbound : ∀ x, 0 ≤ x → |f x| ≤ Real.exp (2*x)) :
    Integrable f (gaussianExcessLaw r) ∧
      (∫ x, f x ∂gaussianExcessLaw r) ≤ gaussianExcessExpMomentBound 2 := by
  have hdom : ∀ᵐ x ∂gaussianExcessLaw r, ‖f x‖ ≤ Real.exp (2*x) := by
    filter_upwards [gaussianExcessLaw_positive_ae r] with x hx
    simpa only [Real.norm_eq_abs] using hbound x hx.le
  have hint := (gaussianExcessLaw_integrable_exp r 2).mono' hf.aestronglyMeasurable hdom
  refine ⟨hint, le_trans (integral_mono_ae hint (gaussianExcessLaw_integrable_exp r 2) ?_)
    (gaussianExcessLaw_exp_moment_le hr (by norm_num))⟩
  exact hdom.mono fun x hx => (le_abs_self (f x)).trans (by simpa only [Real.norm_eq_abs] using hx)

/-- Orders one and two, and E[O exp O], are uniformly bounded over all r≥-1/2. -/
theorem gaussianExcessLaw_uniform_moments {r : ℝ} (hr : -(1/2 : ℝ) ≤ r) :
    (Integrable (fun x : ℝ => x) (gaussianExcessLaw r) ∧
      (∫ x, x ∂gaussianExcessLaw r) ≤ gaussianExcessExpMomentBound 2) ∧
    (Integrable (fun x : ℝ => x^2) (gaussianExcessLaw r) ∧
      (∫ x, x^2 ∂gaussianExcessLaw r) ≤ gaussianExcessExpMomentBound 2) ∧
    (Integrable (fun x : ℝ => x*Real.exp x) (gaussianExcessLaw r) ∧
      (∫ x, x*Real.exp x ∂gaussianExcessLaw r) ≤ gaussianExcessExpMomentBound 2) := by
  have he (x : ℝ) : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  refine ⟨gaussianExcessLaw_integral_le_of_exp_bound hr measurable_id ?_,
    gaussianExcessLaw_integral_le_of_exp_bound hr (by fun_prop) ?_,
    gaussianExcessLaw_integral_le_of_exp_bound hr (by fun_prop) ?_⟩
  · intro x hx
    rw [abs_of_nonneg hx]
    exact (he x).trans (Real.exp_le_exp.mpr (by linarith))
  · intro x hx
    rw [abs_of_nonneg (sq_nonneg x)]
    calc
      x^2 ≤ (Real.exp x)^2 := pow_le_pow_left₀ hx (he x) 2
      _ = Real.exp (2*x) := by rw [← Real.exp_nat_mul]; norm_num
  · intro x hx
    rw [abs_of_nonneg (mul_nonneg hx (Real.exp_pos _).le)]
    calc
      x*Real.exp x ≤ Real.exp x*Real.exp x := mul_le_mul_of_nonneg_right (he x) (Real.exp_pos _).le
      _ = Real.exp (2*x) := by rw [← Real.exp_add]; congr 1; ring

/-- The elementary bound used before integrating a small exponential parameter. -/
theorem exp_le_one_add_mul_exp (x : ℝ) : Real.exp x ≤ 1+x*Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith

/-- The required small-parameter overshoot bound with one constant independent of threshold and drift. -/
theorem gaussianExcessLaw_small_exp_moment_le {r a : ℝ} (hr : -(1/2 : ℝ) ≤ r)
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) :
    (∫ x, Real.exp (2*a*x) ∂gaussianExcessLaw r) ≤ 1+2*gaussianExcessExpMomentBound 2*a := by
  have hm := (gaussianExcessLaw_uniform_moments hr).2.2
  have hbound : ∀ᵐ x ∂gaussianExcessLaw r, Real.exp (2*a*x) ≤ 1+(2*a)*(x*Real.exp x) := by
    filter_upwards [gaussianExcessLaw_positive_ae r] with x hx
    apply (exp_le_one_add_mul_exp (2*a*x)).trans
    have hax : 0 ≤ 2*a*x := by positivity
    have hax' : 2*a*x ≤ x := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hax') hax
    nlinarith
  have hI := integral_mono_ae (gaussianExcessLaw_integrable_exp r (2*a))
    ((integrable_const (1 : ℝ)).add (hm.1.const_mul (2*a))) hbound
  simp only [Pi.add_apply] at hI
  rw [integral_add (integrable_const _) (hm.1.const_mul _), integral_const_mul] at hI
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hI
  have hmul := mul_le_mul_of_nonneg_left hm.2 (show 0 ≤ 2*a by positivity)
  nlinarith

end SwingRepair
