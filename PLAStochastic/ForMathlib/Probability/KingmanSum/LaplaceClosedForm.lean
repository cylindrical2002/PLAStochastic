import PLAStochastic.ForMathlib.Probability.KingmanSum.ExponentialSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

/-! # The closed form of the actual Kingman exponential-sum Laplace transform -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem euler_kingman_step {z : ℝ} (hz : 0 ≤ z) {ρ : ℂ}
    (hρ : ρ * (1 - ρ) = z) (N : ℕ) :
    (1 - ρ ^ 2 / ((N : ℂ) + 1) ^ 2) * (kingmanLaplaceFactor z N : ℂ) *
      (1 - ρ / ((N : ℂ) + 2)) = 1 - ρ / ((N : ℂ) + 1) := by
  have hn1 : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (by positivity : (N : ℝ) + 1 ≠ 0)
  have hn2 : (N : ℂ) + 2 ≠ 0 := by exact_mod_cast (by positivity : (N : ℝ) + 2 ≠ 0)
  have hd : ((N : ℂ) + 1) * ((N : ℂ) + 2) + z ≠ 0 := by
    exact_mod_cast (by positivity : ((N : ℝ) + 1) * ((N : ℝ) + 2) + z ≠ 0)
  simp only [kingmanLaplaceFactor, kingmanRate, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp
  rw [← hρ]
  ring

private theorem euler_kingman_product {z : ℝ} (hz : 0 ≤ z) {ρ : ℂ}
    (hρ : ρ * (1 - ρ) = z) (N : ℕ) :
    (∏ n ∈ Finset.range N, (1 - ρ ^ 2 / ((n : ℂ) + 1) ^ 2)) *
      (∏ n ∈ Finset.range N, (kingmanLaplaceFactor z n : ℂ)) *
      (1 - ρ / ((N : ℂ) + 1)) = 1 - ρ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (N : ℂ) + 1 + 1 = (N : ℂ) + 2 by ring]
    calc
      _ = ((∏ n ∈ Finset.range N, (1 - ρ ^ 2 / ((n : ℂ) + 1) ^ 2)) *
          (∏ n ∈ Finset.range N, (kingmanLaplaceFactor z n : ℂ))) *
          ((1 - ρ ^ 2 / ((N : ℂ) + 1) ^ 2) * (kingmanLaplaceFactor z N : ℂ) *
            (1 - ρ / ((N : ℂ) + 2))) := by ring
      _ = _ := by rw [euler_kingman_step hz hρ, ih]

/-- Euler's sine product evaluates the actual exponential-sum transform for any
complex factorization `z = ρ(1-ρ)`. -/
theorem kingmanLaplace_mul_sin {z : ℝ} (hz : 0 ≤ z) {ρ : ℂ}
    (hρ : ρ * (1 - ρ) = z) :
    Complex.sin (Real.pi * ρ) * (kingmanLaplace z : ℂ) = Real.pi * z := by
  have hp : Tendsto (fun N => ∏ n ∈ Finset.range N, (kingmanLaplaceFactor z n : ℂ)) atTop
      (𝓝 (kingmanLaplace z : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_prod] using
      (Complex.continuous_ofReal.tendsto _).comp (kingmanLaplace_tendsto_finiteProducts hz)
  have hr : Tendsto (fun N : ℕ => 1 - ρ / ((N : ℂ) + 1)) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero, mul_one_div] using
      tendsto_const_nhds.sub ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).const_mul ρ)
  have ht := ((Complex.tendsto_euler_sin_prod ρ).mul hp).mul hr
  simp only [mul_one] at ht
  have he (N : ℕ) :
      (Real.pi * ρ * ∏ n ∈ Finset.range N, (1 - ρ ^ 2 / ((n : ℂ) + 1) ^ 2)) *
        (∏ n ∈ Finset.range N, (kingmanLaplaceFactor z n : ℂ)) *
        (1 - ρ / ((N : ℂ) + 1)) = (Real.pi : ℂ) * z := by
    calc
      _ = (Real.pi : ℂ) * ρ *
        ((∏ n ∈ Finset.range N, (1 - ρ ^ 2 / ((n : ℂ) + 1) ^ 2)) *
          (∏ n ∈ Finset.range N, (kingmanLaplaceFactor z n : ℂ)) *
          (1 - ρ / ((N : ℂ) + 1))) := by ring
      _ = _ := by rw [euler_kingman_product hz hρ, mul_assoc, hρ]
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun N => (he N).symm))

theorem kingmanLaplace_eq_sin {z : ℝ} (hz : 0 < z) {ρ : ℂ}
    (hρ : ρ * (1 - ρ) = z) :
    (kingmanLaplace z : ℂ) = (Real.pi : ℂ) * z / Complex.sin (Real.pi * ρ) := by
  have h := kingmanLaplace_mul_sin hz.le hρ
  have hn : Complex.sin (Real.pi * ρ) ≠ 0 := by
    intro hn
    rw [hn, zero_mul] at h
    have hp : (Real.pi : ℂ) * z ≠ 0 := by exact_mod_cast (mul_pos Real.pi_pos hz).ne'
    exact hp h.symm
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using h

/-- The trigonometric form, including the discriminant-zero boundary. -/
theorem kingmanLaplace_eq_cos {z : ℝ} (hz : 0 < z) (hz' : z ≤ 1 / 4) :
    kingmanLaplace z = Real.pi * z / Real.cos (Real.pi / 2 * Real.sqrt (1 - 4 * z)) := by
  have hs : Real.sqrt (1 - 4 * z) ^ 2 = 1 - 4 * z :=
    Real.sq_sqrt (by linarith)
  have hρ : (((1 - Real.sqrt (1 - 4 * z)) / 2 : ℝ) : ℂ) *
      (1 - (((1 - Real.sqrt (1 - 4 * z)) / 2 : ℝ) : ℂ)) = z := by
    exact_mod_cast (show ((1 - Real.sqrt (1 - 4 * z)) / 2) *
      (1 - (1 - Real.sqrt (1 - 4 * z)) / 2) = z by nlinarith)
  have h := kingmanLaplace_eq_sin hz hρ
  have hr : kingmanLaplace z = Real.pi * z /
      Real.sin (Real.pi * ((1 - Real.sqrt (1 - 4 * z)) / 2)) := by
    exact_mod_cast h
  rw [show Real.pi * ((1 - Real.sqrt (1 - 4 * z)) / 2) =
    Real.pi / 2 - Real.pi / 2 * Real.sqrt (1 - 4 * z) by ring,
    Real.sin_pi_div_two_sub] at hr
  exact hr

/-- The hyperbolic form follows from the same complex Euler product. -/
theorem kingmanLaplace_eq_cosh {z : ℝ} (hz : 1 / 4 ≤ z) :
    kingmanLaplace z = Real.pi * z / Real.cosh (Real.pi / 2 * Real.sqrt (4 * z - 1)) := by
  have hs : (Real.sqrt (4 * z - 1) : ℂ) ^ 2 = ((4 * z - 1 : ℝ) : ℂ) := by
    exact_mod_cast (Real.sq_sqrt (by linarith : 0 ≤ 4 * z - 1))
  have hρ : ((1 - (Real.sqrt (4 * z - 1) : ℂ) * Complex.I) / 2) *
      (1 - (1 - (Real.sqrt (4 * z - 1) : ℂ) * Complex.I) / 2) = (z : ℂ) := by
    calc
      _ = (1 + (Real.sqrt (4 * z - 1) : ℂ) ^ 2) / 4 := by
        ring_nf
        rw [Complex.I_sq]
        ring
      _ = _ := by rw [hs]; push_cast; ring
  have h := kingmanLaplace_eq_sin (by linarith : 0 < z) hρ
  have he : Complex.sin ((Real.pi : ℂ) *
      ((1 - (Real.sqrt (4 * z - 1) : ℂ) * Complex.I) / 2)) =
      (Real.cosh (Real.pi / 2 * Real.sqrt (4 * z - 1)) : ℂ) := by
    rw [show (Real.pi : ℂ) * ((1 - (Real.sqrt (4 * z - 1) : ℂ) * Complex.I) / 2) =
      (Real.pi : ℂ) / 2 - ((Real.pi / 2 * Real.sqrt (4 * z - 1) : ℝ) : ℂ) * Complex.I by
        push_cast
        ring,
      Complex.sin_pi_div_two_sub, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  rw [he] at h
  exact_mod_cast h

/-- Continuity is proved directly from the actual expectation, including zero. -/
theorem continuousOn_kingmanLaplace : ContinuousOn kingmanLaplace (Ici 0) := by
  change ContinuousOn (fun z => ∫ ω, Real.exp (-(z * kingmanTotalReal ω)) ∂kingmanMeasure) (Ici 0)
  apply continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
  · intro z hz
    exact (integrable_laplace_kingmanTotalReal hz).aestronglyMeasurable
  · intro z hz
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hz ENNReal.toReal_nonneg))
  · exact integrable_const _
  · apply Eventually.of_forall
    intro ω
    fun_prop

theorem tendsto_kingmanLaplace_zero : Tendsto kingmanLaplace (𝓝[Ici 0] 0) (𝓝 1) := by
  have h := continuousOn_kingmanLaplace 0 (by simp)
  change Tendsto kingmanLaplace (𝓝[Ici 0] 0) (𝓝 (kingmanLaplace 0)) at h
  simpa only [kingmanLaplace_zero] using h

end BrownianAffine
