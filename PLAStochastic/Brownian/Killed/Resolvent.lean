import PLAStochastic.Brownian.Killed.Positivity
import PLAStochastic.ForMathlib.Probability.KingmanSum.ExponentialSeries
import Mathlib.Analysis.PSeries

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

 def heatResolventMode (r lam : ℝ) (n : ℕ) (x z : ℝ) : ℝ :=
  (2/r * (Real.sin (heatFrequency r n*x) * Real.sin (heatFrequency r n*z))) /
    (lam + heatFrequency r n^2/2)

 def heatResolventBound (r : ℝ) (n : ℕ) : ℝ :=
  (4*r/Real.pi^2) * (1/((n : ℝ)+1)^2)

 def heatResolventSeries (r lam x z : ℝ) : ℝ := ∑' n, heatResolventMode r lam n x z

 theorem heatResolventDenom_pos {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam) (n : ℕ) :
    0 < lam + heatFrequency r n^2/2 := by
  have hf := heatFrequency_pos hr n
  positivity

 theorem heatResolventMode_bound {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam) (n : ℕ) (x z : ℝ) :
    ‖heatResolventMode r lam n x z‖ ≤ heatResolventBound r n := by
  have hf := heatFrequency_pos hr n
  have hc : |2/r * (Real.sin (heatFrequency r n*x) * Real.sin (heatFrequency r n*z))| ≤ 2/r := by
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hr)]
    apply mul_le_of_le_one_right (by positivity)
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  calc
    _ = |2/r * (Real.sin (heatFrequency r n*x) * Real.sin (heatFrequency r n*z))| /
        (lam + heatFrequency r n^2/2) := by
      rw [heatResolventMode, Real.norm_eq_abs, abs_div, abs_of_pos (heatResolventDenom_pos hr hlam n)]
    _ ≤ (2/r)/(heatFrequency r n^2/2) := div_le_div₀ (by positivity) hc (by positivity) (by linarith)
    _ = heatResolventBound r n := by
      unfold heatFrequency heatResolventBound
      field_simp
      norm_num

 theorem summable_heatResolventBound (r : ℝ) : Summable (heatResolventBound r) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  convert! h.mul_left (4*r/Real.pi^2) using 1
  funext n
  simp only [heatResolventBound, Nat.cast_add, Nat.cast_one]

 theorem summable_heatResolventMode {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam) (x z : ℝ) :
    Summable (fun n => heatResolventMode r lam n x z) :=
  (summable_heatResolventBound r).of_norm_bounded (fun n => heatResolventMode_bound hr hlam n x z)

 theorem integrableOn_laplace_heatMode {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam)
    (n : ℕ) (x z : ℝ) :
    IntegrableOn (fun t => Real.exp (-lam*t) * heatSpatialMode r 0 0 n t x z) (Ioi 0) := by
  have heq (t : ℝ) : Real.exp (-lam*t) * heatSpatialMode r 0 0 n t x z =
      (2/r * (Real.sin (heatFrequency r n*x) * Real.sin (heatFrequency r n*z))) *
        Real.exp (-(lam+heatFrequency r n^2/2)*t) := by
    unfold heatSpatialMode
    simp only [Nat.cast_zero, pow_zero, mul_one, zero_mul, zero_div, add_zero]
    rw [show -(lam+heatFrequency r n^2/2)*t = -lam*t + -(heatFrequency r n^2)*t/2 by ring, Real.exp_add]
    ring
  simp only [heq]
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos (heatResolventDenom_pos hr hlam n)) 0).const_mul _

 theorem integral_laplace_heatMode {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam)
    (n : ℕ) (x z : ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-lam*t) * heatSpatialMode r 0 0 n t x z) =
      heatResolventMode r lam n x z := by
  have heq (t : ℝ) : Real.exp (-lam*t) * heatSpatialMode r 0 0 n t x z =
      (2/r * (Real.sin (heatFrequency r n*x) * Real.sin (heatFrequency r n*z))) *
        Real.exp (-(lam+heatFrequency r n^2/2)*t) := by
    unfold heatSpatialMode
    simp only [Nat.cast_zero, pow_zero, mul_one, zero_mul, zero_div, add_zero]
    rw [show -(lam+heatFrequency r n^2/2)*t = -lam*t + -(heatFrequency r n^2)*t/2 by ring, Real.exp_add]
    ring
  simp only [heq]
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos (heatResolventDenom_pos hr hlam n)) 0]
  simp only [heatResolventMode, mul_zero, Real.exp_zero, div_neg, neg_div, neg_neg, mul_one_div]

 theorem integral_norm_laplace_heatMode {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam)
    (n : ℕ) (x z : ℝ) :
    (∫ t in Ioi (0 : ℝ), ‖Real.exp (-lam*t) * heatSpatialMode r 0 0 n t x z‖) =
      ‖heatResolventMode r lam n x z‖ := by
  have heq (t : ℝ) : ‖Real.exp (-lam*t) * heatSpatialMode r 0 0 n t x z‖ =
      |2/r * (Real.sin (heatFrequency r n*x) * Real.sin (heatFrequency r n*z))| *
        Real.exp (-(lam+heatFrequency r n^2/2)*t) := by
    unfold heatSpatialMode
    simp only [Nat.cast_zero, pow_zero, mul_one, zero_mul, zero_div, add_zero]
    rw [show -(lam+heatFrequency r n^2/2)*t = -lam*t + -(heatFrequency r n^2)*t/2 by ring, Real.exp_add]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    ring
  simp only [heq]
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos (heatResolventDenom_pos hr hlam n)) 0]
  simp only [heatResolventMode, mul_zero, Real.exp_zero, div_neg, neg_div, neg_neg, mul_one_div,
    Real.norm_eq_abs, abs_div, abs_of_pos (heatResolventDenom_pos hr hlam n)]

 theorem summable_integral_norm_laplace_heatMode {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam)
    (x z : ℝ) :
    Summable (fun n => ∫ t in Ioi (0 : ℝ), ‖Real.exp (-lam*t) * heatSpatialMode r 0 0 n t x z‖) := by
  simp only [integral_norm_laplace_heatMode hr hlam]
  exact (summable_heatResolventMode hr hlam x z).norm

/-- The time Laplace integral is justified by a full integrable absolute series, including time zero. -/
 theorem integral_laplace_dirichletHeatKernel {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam) (x z : ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-lam*t) * dirichletHeatKernel r t x z) =
      heatResolventSeries r lam x z := by
  have heq (t : ℝ) : Real.exp (-lam*t) * dirichletHeatKernel r t x z =
      ∑' n, Real.exp (-lam*t) * heatSpatialMode r 0 0 n t x z := by
    rw [tsum_mul_left]
    rfl
  simp only [heq]
  rw [← integral_tsum_of_summable_integral_norm (integrableOn_laplace_heatMode hr hlam · x z)
    (summable_integral_norm_laplace_heatMode hr hlam x z)]
  simp only [integral_laplace_heatMode hr hlam]
  rfl

 theorem integrableOn_laplace_dirichletHeatKernel {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam)
    (x z : ℝ) : IntegrableOn (fun t => Real.exp (-lam*t) * dirichletHeatKernel r t x z) (Ioi 0) := by
  let F : ℕ → ℝ → ℝ := fun n t => Real.exp (-lam*t) * heatSpatialMode r 0 0 n t x z
  have hi (n : ℕ) : IntegrableOn (F n) (Ioi 0) := integrableOn_laplace_heatMode hr hlam n x z
  have hm (n : ℕ) : Measurable (F n) := by dsimp only [F, heatSpatialMode]; fun_prop
  have heq : (fun t => Real.exp (-lam*t) * dirichletHeatKernel r t x z) = fun t => ∑' n, F n t := by
    funext t
    dsimp only [F, dirichletHeatKernel, heatSpatialSeries]
    rw [tsum_mul_left]
  rw [heq]
  refine ⟨(Measurable.tsum hm).aestronglyMeasurable, ?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  calc
    (∫⁻ t in Ioi (0 : ℝ), ‖∑' n, F n t‖ₑ) ≤ ∫⁻ t in Ioi (0 : ℝ), ∑' n, ‖F n t‖ₑ :=
      lintegral_mono (fun t => enorm_tsum_le_tsum_enorm)
    _ = ∑' n, ∫⁻ t in Ioi (0 : ℝ), ‖F n t‖ₑ := lintegral_tsum (fun n => (hm n).enorm.aemeasurable)
    _ = ∑' n, ENNReal.ofReal (∫ t in Ioi (0 : ℝ), ‖F n t‖) := by
      congr 1
      funext n
      exact (ofReal_integral_norm_eq_lintegral_enorm (hi n)).symm
    _ = ENNReal.ofReal (∑' n, ∫ t in Ioi (0 : ℝ), ‖F n t‖) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun t => norm_nonneg _))
        (summable_integral_norm_laplace_heatMode hr hlam x z)).symm
    _ < ∞ := ENNReal.ofReal_lt_top

 theorem continuous_heatResolventSeries_right {r lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam) (x : ℝ) :
    Continuous (heatResolventSeries r lam x) := by
  have hc (n : ℕ) : Continuous (fun z : ℝ => heatResolventMode r lam n x z) := by
    dsimp only [heatResolventMode]
    fun_prop
  exact continuous_tsum hc (summable_heatResolventBound r) (heatResolventMode_bound hr hlam · x ·)

end BrownianAffine
