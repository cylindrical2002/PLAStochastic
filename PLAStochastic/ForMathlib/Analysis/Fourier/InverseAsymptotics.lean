import PLAStochastic.ForMathlib.Analysis.Fourier.MomentMajorant
import PLAStochastic.ForMathlib.Analysis.Fourier.CoefficientEnvelope
import Mathlib.Data.Complex.BigOperators

/-! # Uniform finite-jet asymptotics from three-band Fourier estimates -/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace PGM

def angularRealInverse (φ : ℝ → ℂ) : ℝ → ℝ := fun x => (angularInverse φ x).re

theorem angularRealInverse_sub_sum {φ : ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    (hφ : Integrable φ) (s : Finset ℕ) (ha : ∀ k ∈ s, Integrable (a k)) (t : ℕ → ℝ) :
    angularRealInverse (fun u => φ u - ∑ k ∈ s, t k • a k u) =
      fun x => angularRealInverse φ x - ∑ k ∈ s, t k * angularRealInverse (a k) x := by
  funext x
  have he := congrFun (angularInverse_sub_sum hφ s ha t) x
  have h := congrArg Complex.re he
  simpa only [angularRealInverse, Complex.sub_re, Complex.re_sum, Complex.smul_re, smul_eq_mul] using h

theorem iteratedDeriv_inverseRemainder {f : ℝ → ℝ} {a : ℕ → ℝ → ℝ}
    {r : ℕ} (hf : ContDiff ℝ r f) (s : Finset ℕ) (ha : ∀ k ∈ s, ContDiff ℝ r (a k))
    (t : ℕ → ℝ) (x : ℝ) :
    iteratedDeriv r (fun y => f y - ∑ k ∈ s, t k * a k y) x =
      iteratedDeriv r f x - ∑ k ∈ s, t k * iteratedDeriv r (a k) x := by
  have hsum : ContDiff ℝ r (fun y => ∑ k ∈ s, t k * a k y) :=
    ContDiff.sum fun k hk => contDiff_const.mul (ha k hk)
  rw [iteratedDeriv_fun_sub hf.contDiffAt hsum.contDiffAt,
    iteratedDeriv_fun_sum (fun k hk => (contDiff_const.mul (ha k hk)).contDiffAt)]
  congr 1
  exact sum_congr rfl fun k _ => iteratedDeriv_const_mul_field (t k) (a k)

theorem FourierBandEstimates.coefficient_contDiff {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    (h : FourierBandEstimates φ a) (ha : ∀ k, AEStronglyMeasurable (a k)) (m k : ℕ) :
    ContDiff ℝ m (angularRealInverse (a k)) := by
  obtain ⟨B, -, hb⟩ := h.coefficient_moment_bound m k
  exact (contDiff_angularInverse (ha k) (fun r hr =>
    (integrable_fourier_moment_of_bound (ha k) hr hb).1)).continuousLinearMap_comp Complex.reCLM

/-- All prescribed actual inverse derivatives are eventually bounded by one constant. -/
theorem FourierBandEstimates.actual_inverse_bounded {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    (h : FourierBandEstimates φ a) (hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps)) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ eps in atTop,
      ContDiff ℝ m (angularRealInverse (φ eps)) ∧
        ∀ r ≤ m, ∀ x, |iteratedDeriv r (angularRealInverse (φ eps)) x| ≤ B := by
  obtain ⟨C, hC, hc⟩ := h.actual_moment_bound m
  let J := ∫ u : ℝ, fourierMomentWeight (2 * Real.pi * u)
  have hJ : 0 ≤ J := integral_nonneg fun _ => by unfold fourierMomentWeight; positivity
  refine ⟨(2 * Real.pi) ^ m * C * J, by positivity, ?_⟩
  filter_upwards [hc, hφ] with eps he hm
  have hcd := contDiff_angularInverse hm (fun r hr => (integrable_fourier_moment_of_bound hm hr he).1)
  refine ⟨hcd.continuousLinearMap_comp Complex.reCLM, fun r hr x => ?_⟩
  change |iteratedDeriv r (fun y => (angularInverse (φ eps) y).re) x| ≤ _
  rw [iteratedDeriv_re hcd hr]
  refine (Complex.abs_re_le_norm _).trans ((norm_deriv_angularInverse_of_bound hm hC hr he x).trans ?_)
  have hp : (2 * Real.pi) ^ r ≤ (2 * Real.pi) ^ m :=
    pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hr
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hC) hJ

/-- Every real-space derivative has a uniform expansion to every fixed order. -/
theorem FourierBandEstimates.uniform_inverse_expansion {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    (h : FourierBandEstimates φ a) (hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps))
    (ha : ∀ k, AEStronglyMeasurable (a k)) (r : ℕ) :
    UniformInverseExpansion (fun eps => iteratedDeriv r (angularRealInverse (φ eps)))
      (fun k => iteratedDeriv r (angularRealInverse (a k))) := by
  intro P
  obtain ⟨C, hC, hb⟩ := h.remainder_moment_bound r (P + 1)
  obtain ⟨B, hB, hbcoef⟩ := h.coefficient_moment_bound r (P + 1)
  obtain ⟨Q, -, hact⟩ := h.actual_inverse_bounded hφ r
  obtain ⟨A, hA, hamoment⟩ := h.actual_moment_bound r
  let J := ∫ u : ℝ, fourierMomentWeight (2 * Real.pi * u)
  have hJ : 0 ≤ J := integral_nonneg fun _ => by unfold fourierMomentWeight; positivity
  obtain ⟨E, hE⟩ := eventually_atTop.mp (hb.and (hφ.and (hact.and hamoment)))
  refine ⟨(2 * Real.pi) ^ r * (C + B) * J, max 1 E, fun eps heps x => ?_⟩
  have he1 : 1 ≤ eps := (le_max_left _ _).trans heps
  obtain ⟨hbe, hφe, hcd, ham⟩ := hE eps ((le_max_right _ _).trans heps)
  let R : ℝ → ℂ := fun u => φ eps u - ∑ k ∈ range (P + 1 + 1), ((eps⁻¹) ^ k : ℝ) • a k u
  have hRm : AEStronglyMeasurable R :=
    hφe.sub (Finset.aestronglyMeasurable_fun_sum _ fun k _ => (ha k).const_smul ((eps⁻¹) ^ k : ℝ))
  have hRbound : ∀ u, (1 + |u|) ^ (r + 2) * ‖R u‖ ≤ C * (eps⁻¹) ^ (P + 1) := hbe
  have hRcd := contDiff_angularInverse hRm (fun j hj => (integrable_fourier_moment_of_bound hRm hj hRbound).1)
  have hφi : Integrable (φ eps) := by
    apply (integrable_norm_iff hφe).mp
    simpa only [pow_zero, one_mul] using (integrable_fourier_moment_of_bound hφe (Nat.zero_le r) ham).1
  have hai (k : ℕ) : Integrable (a k) := by
    obtain ⟨V, -, hv⟩ := h.coefficient_moment_bound 0 k
    apply (integrable_norm_iff (ha k)).mp
    simpa only [pow_zero, one_mul] using (integrable_fourier_moment_of_bound (ha k) le_rfl hv).1
  have hreq : angularRealInverse R = fun y => angularRealInverse (φ eps) y -
      ∑ k ∈ range (P + 1 + 1), (eps⁻¹) ^ k * angularRealInverse (a k) y :=
    angularRealInverse_sub_sum hφi _ (fun k _ => hai k) _
  have hRderiv (y : ℝ) : iteratedDeriv r (angularRealInverse R) y =
      iteratedDeriv r (angularRealInverse (φ eps)) y -
        ∑ k ∈ range (P + 1 + 1), (eps⁻¹) ^ k * iteratedDeriv r (angularRealInverse (a k)) y := by
    rw [hreq]
    exact iteratedDeriv_inverseRemainder hcd.1 _ (fun k _ => h.coefficient_contDiff ha r k) _ y
  have hs : |iteratedDeriv r (angularRealInverse R) x| ≤
      (2 * Real.pi) ^ r * C * J * (eps⁻¹) ^ (P + 1) := by
    change |iteratedDeriv r (fun y => (angularInverse R y).re) x| ≤ _
    rw [iteratedDeriv_re hRcd le_rfl]
    exact (Complex.abs_re_le_norm _).trans
      ((norm_deriv_angularInverse_of_bound hRm (by positivity) le_rfl hRbound x).trans_eq (by dsimp [J]; ring))
  have hcoef : |iteratedDeriv r (angularRealInverse (a (P + 1))) x| ≤ (2 * Real.pi) ^ r * B * J := by
    have hcc := contDiff_angularInverse (ha (P + 1)) (fun j hj =>
      (integrable_fourier_moment_of_bound (ha (P + 1)) hj hbcoef).1)
    change |iteratedDeriv r (fun y => (angularInverse (a (P + 1)) y).re) x| ≤ _
    rw [iteratedDeriv_re hcc le_rfl]
    exact (Complex.abs_re_le_norm _).trans (norm_deriv_angularInverse_of_bound (ha (P + 1)) hB le_rfl hbcoef x)
  rw [hRderiv] at hs
  have hsplit : iteratedDeriv r (angularRealInverse (φ eps)) x -
      inversePolynomial (fun k => iteratedDeriv r (angularRealInverse (a k)) x) P eps =
      (iteratedDeriv r (angularRealInverse (φ eps)) x -
        ∑ k ∈ range (P + 1 + 1), (eps⁻¹) ^ k * iteratedDeriv r (angularRealInverse (a k)) x) +
          (eps⁻¹) ^ (P + 1) * iteratedDeriv r (angularRealInverse (a (P + 1))) x := by
    unfold inversePolynomial
    rw [sum_range_succ (n := P + 1)]
    have heq : ∑ k ∈ range (P + 1), iteratedDeriv r (angularRealInverse (a k)) x * (eps⁻¹) ^ k =
        ∑ k ∈ range (P + 1), (eps⁻¹) ^ k * iteratedDeriv r (angularRealInverse (a k)) x :=
      sum_congr rfl fun _ _ => mul_comm _ _
    rw [heq]
    ring
  rw [hsplit]
  have hi : 0 ≤ (eps⁻¹) ^ (P + 1) := by positivity
  have ht := mul_le_mul_of_nonneg_left hcoef hi
  rw [← abs_of_nonneg hi, ← abs_mul] at ht
  rw [abs_of_nonneg hi] at ht
  exact (abs_add_le _ _).trans ((add_le_add hs ht).trans_eq (by ring))

end PGM
