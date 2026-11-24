import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LaplaceAnalytic
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LineShift
import Mathlib.Analysis.Fourier.Inversion

/-!
# Inversion of the Laplace transform along a vertical line

`laplace_inversion_line`: if `r` is continuous, `e^{a y} r(y)` is integrable and the transform on
the line `Re ζ = a` is an integrable function `F(a + i t)`, then
`r(x) = (2π)⁻¹ ∫ e^{-(a + i t) x} F(a + i t) dt` for every `x` (Mathlib's Fourier inversion,
after the change of variables `t = -2π ξ`).

`lineFourier_weight_eq`, `lintegral_norm_sq_laplaceC_le`: the Plancherel bound
`∫ |A(σ + i t)|² dt ≤ 2π · D²/(2(θ - σ))` for an exponential density and `σ < θ`.

`integral_inv_sq_add_sq`: `∫ dt / ((t - c)² + d²) = π / d`.
-/

noncomputable section

open MeasureTheory Complex Filter Topology Set FourierTransform
open scoped ENNReal Real

namespace PGM.WienerHopf

variable {g : ℝ → ℂ} {D θ : ℝ}

theorem lineFourier_weight_eq (g : ℝ → ℂ) (σ t : ℝ) :
    lineFourier (fun x => (Real.exp (σ * x) : ℂ) * g x) t = laplaceC g (σ + t * I) := by
  unfold lineFourier laplaceC
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- **Laplace inversion along a vertical line.** -/
theorem laplace_inversion_line {r : ℝ → ℂ} {F : ℂ → ℂ} {a : ℝ} (hr : Continuous r)
    (hri : Integrable fun y : ℝ => (Real.exp (a * y) : ℂ) * r y)
    (hF : ∀ t : ℝ, laplaceC r (a + t * I) = F (a + t * I))
    (hFi : Integrable fun t : ℝ => F (a + t * I)) (x : ℝ) :
    r x = (1 / (2 * π) : ℂ) * ∫ t : ℝ, cexp (-((a : ℂ) + t * I) * x) * F (a + t * I) := by
  set φ : ℝ → ℂ := fun y => (Real.exp (a * y) : ℂ) * r y
  have hφc : Continuous φ := (by fun_prop : Continuous fun y : ℝ => (Real.exp (a * y) : ℂ)).mul hr
  have hF𝓕 : ∀ ξ : ℝ, 𝓕 φ ξ = F (a + ((-2 * π * ξ : ℝ) : ℂ) * I) := by
    intro ξ
    rw [Real.fourier_real_eq_integral_exp_smul, ← hF, ← lineFourier_weight_eq]
    unfold lineFourier
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul, φ]
    congr 2
    push_cast; ring
  have hF𝓕i : Integrable (𝓕 φ) := by
    have h := hFi.comp_mul_left' (show (-2 * π : ℝ) ≠ 0 by positivity)
    refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
    rw [hF𝓕 ξ]
  have hinv := hri.fourierInv_fourier_eq hF𝓕i hφc.continuousAt (v := x)
  rw [Real.fourierInv_eq'] at hinv
  have hsub : ∫ ξ : ℝ, cexp (↑(2 * π * inner ℝ ξ x) * I) • 𝓕 φ ξ =
      (1 / (2 * π) : ℂ) * ∫ t : ℝ, cexp (-(t * I) * x) * F (a + t * I) := by
    have h := Measure.integral_comp_mul_left
      (fun t : ℝ => cexp (-(t * I) * x) * F (a + t * I)) (-2 * π)
    rw [show |(-2 * π)⁻¹| = 1 / (2 * π) by
      rw [abs_inv, abs_of_neg (by linarith [Real.pi_pos] : -2 * π < 0)]; ring] at h
    rw [Complex.real_smul] at h
    push_cast at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul, hF𝓕 ξ, RCLike.inner_apply, conj_trivial]
    push_cast
    ring_nf
  rw [hsub] at hinv
  have hx : r x = (Real.exp (-a * x) : ℂ) * φ x := by
    simp only [φ, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [show -a * x + a * x = 0 by ring, Real.exp_zero, Complex.ofReal_one, one_mul]
  rw [hx, ← hinv, ← mul_assoc, mul_comm (Real.exp (-a * x) : ℂ), mul_assoc, ← integral_const_mul]
  congr 2
  funext t
  rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast; ring

theorem integral_inv_sq_add_sq {d : ℝ} (hd : 0 < d) (c : ℝ) :
    Integrable (fun t : ℝ => ((t - c) ^ 2 + d ^ 2)⁻¹) ∧
      ∫ t : ℝ, ((t - c) ^ 2 + d ^ 2)⁻¹ = π / d := by
  have hfun : (fun t : ℝ => ((t - c) ^ 2 + d ^ 2)⁻¹) =
      fun t => (d ^ 2)⁻¹ * (1 + ((t - c) / d) ^ 2)⁻¹ := by
    funext t; field_simp; ring
  have hint1 : Integrable fun t : ℝ => (1 + ((t - c) / d) ^ 2)⁻¹ := by
    have h := (integrable_inv_one_add_sq.comp_div (show d ≠ 0 by positivity)).comp_sub_right c
    exact h
  refine ⟨by rw [hfun]; exact hint1.const_mul _, ?_⟩
  rw [hfun, integral_const_mul]
  have h1 : ∫ t : ℝ, (1 + ((t - c) / d) ^ 2)⁻¹ = ∫ t : ℝ, (1 + (t / d) ^ 2)⁻¹ :=
    integral_sub_right_eq_self (fun t => (1 + (t / d) ^ 2)⁻¹) c
  have h2 : ∫ t : ℝ, (1 + (t / d) ^ 2)⁻¹ = d * π := by
    rw [Measure.integral_comp_div (fun t => (1 + t ^ 2)⁻¹) d, integral_univ_inv_one_add_sq,
      abs_of_pos hd, smul_eq_mul]
  rw [h1, h2]
  field_simp

/-- The Plancherel bound on a vertical line: `∫ |A(σ + i t)|² dt ≤ 2π D²/(2(θ - σ))`. -/
theorem lintegral_norm_sq_laplaceC_le (hg : IsExpDensity g D θ) {σ : ℝ} (hσ : σ < θ) :
    ∫⁻ t : ℝ, ENNReal.ofReal (‖laplaceC g (σ + t * I)‖ ^ 2) ≤
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (D ^ 2 / (2 * (θ - σ))) := by
  set f : ℝ → ℂ := fun x => (Real.exp (σ * x) : ℂ) * g x
  have hD := hg.nonneg_D
  have hfm : Measurable f := (by fun_prop : Measurable fun x : ℝ => (Real.exp (σ * x) : ℂ)).mul
    hg.measurable
  have hfb : ∀ x, ‖f x‖ ≤ (Ioi (0 : ℝ)).indicator (fun x => D * Real.exp ((σ - θ) * x)) x := by
    intro x
    simp only [f, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hx]
      calc Real.exp (σ * x) * ‖g x‖ ≤ Real.exp (σ * x) * (D * Real.exp (-θ * x)) :=
            mul_le_mul_of_nonneg_left (hg.norm_le x) (Real.exp_pos _).le
        _ = D * Real.exp ((σ - θ) * x) := by rw [mul_comm, mul_assoc, ← Real.exp_add]; ring_nf
    · rw [indicator_of_notMem hx, hg.eq_zero_of_nonpos x (not_lt.mp hx), norm_zero, mul_zero]
  have hI : IntegrableOn (fun x : ℝ => D * Real.exp ((σ - θ) * x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul D
  have hfi : Integrable f := (hI.integrable_indicator measurableSet_Ioi).mono'
    hfm.aestronglyMeasurable (Filter.Eventually.of_forall hfb)
  have h := lintegral_norm_sq_lineFourier_le hfi hfm
  have hA : ∀ t, lineFourier f t = laplaceC g (σ + t * I) := fun t => lineFourier_weight_eq g σ t
  simp_rw [hA] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ bot_le)
  have hI2 : IntegrableOn (fun x : ℝ => D ^ 2 * Real.exp (2 * (σ - θ) * x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  calc ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)
      ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal (D ^ 2 * Real.exp (2 * (σ - θ) * x)) := by
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Ioi (0 : ℝ)
        · rw [indicator_of_mem hx]
          refine ENNReal.ofReal_le_ofReal ?_
          have := hfb x
          rw [indicator_of_mem hx] at this
          calc ‖f x‖ ^ 2 ≤ (D * Real.exp ((σ - θ) * x)) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) this 2
            _ = D ^ 2 * Real.exp (2 * (σ - θ) * x) := by
                rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
        · rw [indicator_of_notMem hx]
          have := hfb x
          rw [indicator_of_notMem hx] at this
          rw [le_antisymm this (norm_nonneg _)]; simp
    _ = ENNReal.ofReal (∫ x in Ioi 0, D ^ 2 * Real.exp (2 * (σ - θ) * x)) :=
        (ofReal_integral_eq_lintegral_ofReal hI2 ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Filter.Eventually.of_forall fun _ _ => by positivity))).symm
    _ = ENNReal.ofReal (D ^ 2 / (2 * (θ - σ))) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
        congr 1
        rw [mul_zero, Real.exp_zero, div_eq_mul_inv, div_eq_mul_inv,
          show 2 * (σ - θ) = -(2 * (θ - σ)) by ring, inv_neg]
        ring

end PGM.WienerHopf
