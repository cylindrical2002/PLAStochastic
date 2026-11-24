import PLAStochastic.Brownian.Construction.CanonicalPreBrownian
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic

/-! Fourth Gaussian moments and the Kolmogorov increment condition for actual pre-Brownian laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The fourth moment is computed from the actual Gaussian moment generating function. -/
theorem integral_fourth_gaussianReal (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have hder1 : deriv (fun t : ℝ => Real.exp (v * t ^ 2 / 2)) =
      fun t => (v : ℝ) * t * Real.exp (v * t ^ 2 / 2) := by
    ext t
    rw [_root_.deriv_exp (by fun_prop)]
    simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id,
      Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul,
      deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
    ring
  have hder2 : deriv (fun t : ℝ => (v : ℝ) * t * Real.exp (v * t ^ 2 / 2)) =
      fun t => ((v : ℝ) + v ^ 2 * t ^ 2) * Real.exp (v * t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), hder1]
    rw [deriv_const_mul_id]
    ring
  have hder3 : deriv (fun t : ℝ => ((v : ℝ) + v ^ 2 * t ^ 2) * Real.exp (v * t ^ 2 / 2)) =
      fun t => (3 * (v : ℝ) ^ 2 * t + v ^ 3 * t ^ 3) * Real.exp (v * t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), hder1,
      deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop)]
    simp only [deriv_const', zero_mul, zero_add, deriv_pow_field, Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one]
    ring
  calc
    _ = iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 := by
      rw [iteratedDeriv_mgf_zero] <;> simp
    _ = _ := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add]
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
        hder1, hder2, hder3, deriv_fun_mul (by fun_prop) (by fun_prop),
        deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop),
        deriv_fun_mul (by fun_prop) (by fun_prop)]
      simp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem preBrownian_integral_fourth_increment (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) :
    (∫ ω, (B s ω - B t ω) ^ 4 ∂μ) = 3 * ((s : ℝ) - t) ^ 2 := by
  change (∫ ω, ((fun x : ℝ => x ^ 4) ∘ (B s - B t)) ω ∂μ) = _
  rw [(hB.hasLaw_sub s t).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop), integral_fourth_gaussianReal]
  simp only [coe_nndist, Real.dist_eq, sq_abs]
  rfl

theorem preBrownian_integrable_fourth_increment (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) :
    Integrable (fun ω => (B s ω - B t ω) ^ 4) μ := by
  have hm := (hB.hasLaw_sub s t).hasGaussianLaw.memLp (p := (4 : ℝ≥0∞)) (by norm_num)
  simpa only [Real.norm_eq_abs, Pi.sub_apply, (by decide : Even 4).pow_abs] using
    hm.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)

/-- A fourth-moment Markov bound for increments; no path regularity is assumed. -/
theorem preBrownian_measureReal_increment_ge (hB : IsPreBrownianReal B μ)
    (s t : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a ≤ |B s ω - B t ω|} ≤ 3 * ((s : ℝ) - t) ^ 2 / a ^ 4 := by
  have heq : {ω | a ≤ |B s ω - B t ω|} = {ω | a ^ 4 ≤ (B s ω - B t ω) ^ 4} := by
    ext ω
    change (a ≤ |B s ω - B t ω|) ↔ (a ^ 4 ≤ (B s ω - B t ω) ^ 4)
    rw [← (by decide : Even 4).pow_abs (B s ω - B t ω)]
    exact (pow_le_pow_iff_left₀ ha.le (abs_nonneg _) (by norm_num : (4 : ℕ) ≠ 0)).symm
  rw [heq]
  apply (le_div_iff₀ (pow_pos ha 4)).mpr
  rw [mul_comm]
  have hh := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ω => (by positivity : 0 ≤ (B s ω - B t ω) ^ 4)))
    (preBrownian_integrable_fourth_increment hB s t) (a ^ 4)
  rw [preBrownian_integral_fourth_increment hB s t] at hh
  exact hh

/-- The same bound in extended nonnegative measure units. -/
theorem preBrownian_measure_increment_ge (hB : IsPreBrownianReal B μ)
    (s t : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    μ {ω | a ≤ |B s ω - B t ω|} ≤ ENNReal.ofReal (3 * ((s : ℝ) - t) ^ 2 / a ^ 4) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (preBrownian_measureReal_increment_ge hB s t ha)

/-- The exact Kolmogorov fourth-moment identity in extended nonnegative units. -/
theorem preBrownian_lintegral_fourth_increment (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) :
    (∫⁻ ω, edist (B s ω) (B t ω) ^ (4 : ℝ) ∂μ) = 3 * edist s t ^ (2 : ℝ) := by
  calc
    _ = ∫⁻ ω, ENNReal.ofReal ((B s ω - B t ω) ^ 4) ∂μ := by
      apply lintegral_congr
      intro ω
      rw [ENNReal.rpow_ofNat, edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _),
        (by decide : Even 4).pow_abs]
    _ = ENNReal.ofReal (∫ ω, (B s ω - B t ω) ^ 4 ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal (preBrownian_integrable_fourth_increment hB s t)
        (Eventually.of_forall fun ω => by positivity)).symm
    _ = _ := by
      rw [preBrownian_integral_fourth_increment hB s t, ENNReal.ofReal_mul (by norm_num),
        ENNReal.rpow_ofNat, edist_dist]
      norm_num only [ENNReal.ofReal_ofNat]
      congr 1
      rw [← ENNReal.ofReal_pow (dist_nonneg)]
      congr 1
      rw [NNReal.dist_eq, sq_abs]

/-- A measurable pre-Brownian process satisfies the genuine `(4, 2, 3)` condition. -/
theorem preBrownian_isKolmogorovProcess (hB : IsPreBrownianReal B μ)
    (hm : ∀ t, Measurable (B t)) : IsKolmogorovProcess B μ 4 2 3 := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology hm (fun s t => ?_) (by norm_num) (by norm_num)
  exact (preBrownian_lintegral_fourth_increment hB s t).le

theorem canonicalPreBrownian_isKolmogorovProcess :
    IsKolmogorovProcess canonicalPreBrownian canonicalPreBrownianMeasure 4 2 3 :=
  preBrownian_isKolmogorovProcess isPreBrownianReal_canonicalPreBrownian measurable_canonicalPreBrownian

end BrownianAffine
