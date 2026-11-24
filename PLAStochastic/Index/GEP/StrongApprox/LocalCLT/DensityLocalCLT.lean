import PLAStochastic.Index.GEP.StrongApprox.LocalCLT.SmoothedDensity
import PLAStochastic.Index.GEP.StrongApprox.LocalCLT.SmoothedLocalCLT

/-! # Pointwise density local CLT for Gaussian-smoothed convolution powers -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal Real

/-- The oscillatory Gaussian-smoothed Fourier integrand is integrable. -/
theorem integrable_phase_charFun_gaussian (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ} (hv : 0 < v) (x : ℝ) :
    Integrable (fun t : ℝ => cexp (-(↑(t * x) * I)) * charFun μ t *
      (Real.exp (-(v * t ^ 2 / 2)) : ℂ)) := by
  have hg : Integrable (fun t : ℝ => Real.exp (-(v * t ^ 2 / 2))) := by
    convert integrable_exp_neg_mul_sq (show 0 < v / 2 by positivity) using 1
    funext t
    congr 1
    ring
  refine hg.mono' (by fun_prop) (ae_of_all _ fun t => ?_)
  have hp : ‖cexp (-(↑(t * x) * I))‖ = 1 := by rw [Complex.norm_exp]; simp
  rw [norm_mul, norm_mul, hp, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) (norm_charFun_le_one t)

/-- Gaussian Fourier inversion as a special case of the smoothing identity. -/
theorem gaussianPDFReal_eq_fourier {v : ℝ} (hv : 0 < v) (x : ℝ) :
    (gaussianPDFReal 0 (Real.toNNReal v) x : ℂ) =
      ((2 * π)⁻¹ : ℂ) * ∫ t : ℝ, cexp (-(↑(t * x) * I)) *
        (Real.exp (-(v * t ^ 2 / 2)) : ℂ) := by
  have he := integral_gaussianPDFReal_eq_charFun (μ := Measure.dirac (0 : ℝ)) hv x
  simpa only [integral_dirac, charFun_dirac, inner_zero_left, ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one, gaussianPDFReal_symm x 0] using he

/-- Fourier `L¹` error controls the actual continuous smoothing density at every point. -/
theorem saGaussianDensity_sub_gaussian_le_fourier (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {h v : ℝ} (hh : 0 < h) (hv : 0 < v) (x : ℝ) :
    |saGaussianDensity μ (Real.toNNReal (h ^ 2)) x - gaussianPDFReal 0 (Real.toNNReal v) x| ≤
      (2 * π)⁻¹ * ∫ t : ℝ, ‖charFun μ t * (Real.exp (-(h ^ 2 * t ^ 2 / 2)) : ℂ) -
        (Real.exp (-(v * t ^ 2 / 2)) : ℂ)‖ := by
  let F := fun t : ℝ => cexp (-(↑(t * x) * I)) * charFun μ t *
    (Real.exp (-(h ^ 2 * t ^ 2 / 2)) : ℂ)
  let G := fun t : ℝ => cexp (-(↑(t * x) * I)) *
    (Real.exp (-(v * t ^ 2 / 2)) : ℂ)
  have hF : Integrable F := integrable_phase_charFun_gaussian μ (sq_pos_of_pos hh) x
  have hG : Integrable G := by
    have hg := integrable_phase_charFun_gaussian (Measure.dirac (0 : ℝ)) hv x
    simpa only [G, charFun_dirac, inner_zero_left, ofReal_zero, zero_mul, Complex.exp_zero,
      mul_one] using hg
  have he : ((saGaussianDensity μ (Real.toNNReal (h ^ 2)) x -
      gaussianPDFReal 0 (Real.toNNReal v) x : ℝ) : ℂ) =
      ((2 * π)⁻¹ : ℂ) * ∫ t, F t - G t := by
    rw [Complex.ofReal_sub, saGaussianDensity,
      integral_gaussianPDFReal_eq_charFun (sq_pos_of_pos hh) x,
      gaussianPDFReal_eq_fourier hv x, ← mul_sub, integral_sub hF hG]
  have hc : ‖((2 * π)⁻¹ : ℂ)‖ = (2 * π)⁻¹ := by
    have heq : ((2 * π)⁻¹ : ℂ) = (((2 * π)⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ = ‖((saGaussianDensity μ (Real.toNNReal (h ^ 2)) x -
        gaussianPDFReal 0 (Real.toNNReal v) x : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (2 * π)⁻¹ * ∫ t : ℝ, ‖F t - G t‖ := by
      rw [he, norm_mul, hc]
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      have hp : ‖cexp (-(↑(t * x) * I))‖ = 1 := by rw [Complex.norm_exp]; simp
      dsimp [F, G]
      rw [mul_assoc, ← mul_sub, norm_mul, hp, one_mul]

/-- Uniform pointwise density local CLT for an actual smoothed normalized iid sum. -/
theorem saGaussianDensity_normalized_convPow_error_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {σ β κ h vlo vhi : ℝ} (h3 : MemLp id 3 μ) (hm : ∫ x : ℝ, x ∂μ = 0)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (hβ : 1 ≤ β)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ β * σ ^ 3)
    (hvlo : 0 < vlo) (hlo : vlo ≤ σ ^ 2) (hhi : σ ^ 2 ≤ vhi)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hgap : ∀ t : ℝ, 1 / (β * σ) ≤ |t| → ‖charFun μ t‖ ≤ 1 - κ)
    (hh : 0 < h) {l : ℕ} (hl : 2 ≤ l) (hscale : 1 / h ≤ (l : ℝ) ^ 8) (x : ℝ) :
    |saGaussianDensity ((convPow μ l).map ((Real.sqrt l)⁻¹ * ·)) (Real.toNNReal (h ^ 2)) x -
      gaussianPDFReal 0 (Real.toNNReal (σ ^ 2 + h ^ 2)) x| ≤
      ((2 * π)⁻¹ * saFourierCLTConstant vlo vhi β κ) / Real.sqrt l := by
  let : IsProbabilityMeasure ((convPow μ l).map ((Real.sqrt l)⁻¹ * ·)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hf := saGaussianDensity_sub_gaussian_le_fourier
    ((convPow μ l).map ((Real.sqrt l)⁻¹ * ·)) hh (show 0 < σ ^ 2 + h ^ 2 by positivity) x
  have he := integral_smoothed_fourier_error_le_uniform h3 hm hvar hσ hβ hthird
    hvlo hlo hhi hκ hκ1 hgap hh hl hscale
  have hid : (fun t : ℝ => ‖charFun ((convPow μ l).map ((Real.sqrt l)⁻¹ * ·)) t *
      (Real.exp (-(h ^ 2 * t ^ 2 / 2)) : ℂ) -
      (Real.exp (-((σ ^ 2 + h ^ 2) * t ^ 2 / 2)) : ℂ)‖) =
      fun t : ℝ => ‖charFun μ (t / Real.sqrt l) ^ l *
      (Real.exp (-(h ^ 2 * t ^ 2 / 2)) : ℂ) -
      (Real.exp (-(t ^ 2 * (σ ^ 2 + h ^ 2) / 2)) : ℂ)‖ := by
    funext t
    rw [charFun_map_mul, charFun_convPow,
      show (Real.sqrt l)⁻¹ * t = t / Real.sqrt l by ring,
      mul_comm (σ ^ 2 + h ^ 2) (t ^ 2)]
  rw [hid] at hf
  apply hf.trans
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (2 * π)⁻¹)

end

end PGM
