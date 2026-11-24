import PLAStochastic.Index.GEP.StrongApprox.LocalCLT.LowFrequency

/-! # Integrated low-frequency error for normalized iid sums -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal

/-- Gaussian damping makes the cubic Fourier error integrable. -/
theorem integrable_cubic_gaussian {v : ℝ} (hv : 0 < v) :
    Integrable (fun t : ℝ => |t| ^ 3 * Real.exp (-(t ^ 2 * v / 6))) := by
  have hi := integrable_rpow_mul_exp_neg_mul_sq (show 0 < v / 6 by positivity)
    (show (-1 : ℝ) < (3 : ℝ) by norm_num)
  have he : (fun t : ℝ => |t| ^ 3 * Real.exp (-(t ^ 2 * v / 6))) =
      fun t : ℝ => ‖t ^ (3 : ℝ) * Real.exp (-(v / 6) * t ^ 2)‖ := by
    funext t
    rw [Real.rpow_ofNat, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    congr 2
    ring
  rw [he]
  exact hi.norm

/-- The normalized characteristic powers have a uniform integrable low-frequency error envelope. -/
theorem normalized_charFun_pow_sub_gaussian_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {σ β : ℝ} (h3 : MemLp id 3 μ) (hm : ∫ x : ℝ, x ∂μ = 0)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (hβ : 1 ≤ β)
    (hκ : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ β * σ ^ 3) {n : ℕ} (hn : 2 ≤ n)
    {t : ℝ} (ht : |t| ≤ Real.sqrt n / (β * σ)) :
    ‖charFun μ (t / Real.sqrt n) ^ n - ((Real.exp (-(t ^ 2 * σ ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
      (β * σ ^ 3 / Real.sqrt n) * (|t| ^ 3 * Real.exp (-(t ^ 2 * σ ^ 2 / 6))) := by
  let r := Real.sqrt (n : ℝ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < r := Real.sqrt_pos.mpr hn0
  have hrsq : r ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hb : 0 < β * σ := mul_pos (lt_of_lt_of_le zero_lt_one hβ) hσ
  have htu : |t / r| ≤ 1 / (β * σ) := by
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
    simpa only [r, one_div, div_eq_mul_inv, mul_comm, mul_one] using ht
  have hp := charFun_pow_sub_gaussian_le h3 hm hvar hσ hβ hκ htu (n - 1)
  have hn1 : n - 1 + 1 = n := by omega
  rw [hn1] at hp
  have hnr : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hn1
  have hgauss : ((n - 1 : ℕ) + 1 : ℝ) * (t / r) ^ 2 * σ ^ 2 / 2 = t ^ 2 * σ ^ 2 / 2 := by
    rw [hnr, ← hrsq]
    field_simp
  have hcoef : ((n - 1 : ℕ) + 1 : ℝ) * (β * σ ^ 3 * |t / r| ^ 3) =
      (β * σ ^ 3 / r) * |t| ^ 3 := by
    rw [hnr, ← hrsq, abs_div, abs_of_pos hr, div_pow]
    field_simp
  rw [hgauss, hcoef] at hp
  have hdecay : Real.exp (-(((n - 1 : ℕ) : ℝ) * (t / r) ^ 2 * σ ^ 2 / 3)) ≤
      Real.exp (-(t ^ 2 * σ ^ 2 / 6)) := by
    apply Real.exp_le_exp.mpr
    have hhalf : (n : ℝ) / 2 ≤ ((n - 1 : ℕ) : ℝ) := by
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hm0 : 0 ≤ (t / r) ^ 2 * σ ^ 2 := by positivity
    have he : (n : ℝ) * ((t / r) ^ 2 * σ ^ 2) = t ^ 2 * σ ^ 2 := by
      rw [← hrsq]
      field_simp
    nlinarith [mul_le_mul_of_nonneg_right hhalf hm0]
  apply hp.trans
  calc
    (β * σ ^ 3 / r) * |t| ^ 3 * Real.exp (-(((n - 1 : ℕ) : ℝ) * (t / r) ^ 2 * σ ^ 2 / 3)) ≤
        (β * σ ^ 3 / r) * |t| ^ 3 * Real.exp (-(t ^ 2 * σ ^ 2 / 6)) := by
      exact mul_le_mul_of_nonneg_left hdecay (by have := hβ; positivity)
    _ = _ := by ring

/-- The explicit constant in the integrated low-frequency error. -/
def saLowFrequencyConstant (σ β : ℝ) : ℝ :=
  β * σ ^ 3 * ∫ t : ℝ, |t| ^ 3 * Real.exp (-(t ^ 2 * σ ^ 2 / 6))

/-- Integrating the complete complex low-frequency error gives the `n⁻¹/²` rate. -/
theorem integral_lowFrequency_error_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {σ β : ℝ} (h3 : MemLp id 3 μ) (hm : ∫ x : ℝ, x ∂μ = 0)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (hβ : 1 ≤ β)
    (hκ : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ β * σ ^ 3) {n : ℕ} (hn : 2 ≤ n) :
    (∫ t : ℝ in Icc (-(Real.sqrt n / (β * σ))) (Real.sqrt n / (β * σ)),
      ‖charFun μ (t / Real.sqrt n) ^ n - ((Real.exp (-(t ^ 2 * σ ^ 2 / 2)) : ℝ) : ℂ)‖) ≤
      saLowFrequencyConstant σ β / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hβ0 : 0 ≤ β := (by norm_num : (0 : ℝ) ≤ 1).trans hβ
  have hfac : 0 ≤ β * σ ^ 3 / Real.sqrt (n : ℝ) := by positivity
  have he : Continuous (fun t : ℝ =>
      ‖charFun μ (t / Real.sqrt n) ^ n - ((Real.exp (-(t ^ 2 * σ ^ 2 / 2)) : ℝ) : ℂ)‖) := by
    fun_prop
  have hg := (integrable_cubic_gaussian (sq_pos_of_pos hσ)).const_mul
    (β * σ ^ 3 / Real.sqrt (n : ℝ))
  calc
    _ ≤ ∫ t : ℝ in Icc (-(Real.sqrt n / (β * σ))) (Real.sqrt n / (β * σ)),
        (β * σ ^ 3 / Real.sqrt n) * (|t| ^ 3 * Real.exp (-(t ^ 2 * σ ^ 2 / 6))) := by
      apply integral_mono_ae he.integrableOn_Icc hg.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact normalized_charFun_pow_sub_gaussian_le h3 hm hvar hσ hβ hκ hn (abs_le.mpr ht)
    _ ≤ ∫ t : ℝ, (β * σ ^ 3 / Real.sqrt n) * (|t| ^ 3 * Real.exp (-(t ^ 2 * σ ^ 2 / 6))) :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun t => by positivity) hg
    _ = saLowFrequencyConstant σ β / Real.sqrt n := by
      rw [integral_const_mul]
      unfold saLowFrequencyConstant
      ring

/-- A variance bracket and a common standardized third-moment bound give one class constant. -/
theorem integral_lowFrequency_error_le_uniform {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {σ β vlo vhi : ℝ} (h3 : MemLp id 3 μ) (hm : ∫ x : ℝ, x ∂μ = 0)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (hβ : 1 ≤ β)
    (hκ : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ β * σ ^ 3)
    (hvlo : 0 < vlo) (hlo : vlo ≤ σ ^ 2) (hhi : σ ^ 2 ≤ vhi) {n : ℕ} (hn : 2 ≤ n) :
    (∫ t : ℝ in Icc (-(Real.sqrt n / (β * σ))) (Real.sqrt n / (β * σ)),
      ‖charFun μ (t / Real.sqrt n) ^ n - ((Real.exp (-(t ^ 2 * σ ^ 2 / 2)) : ℝ) : ℂ)‖) ≤
      (β * Real.sqrt vhi ^ 3 * ∫ t : ℝ, |t| ^ 3 * Real.exp (-(t ^ 2 * vlo / 6))) / Real.sqrt n := by
  apply (integral_lowFrequency_error_le h3 hm hvar hσ hβ hκ hn).trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  unfold saLowFrequencyConstant
  have hi : (∫ t : ℝ, |t| ^ 3 * Real.exp (-(t ^ 2 * σ ^ 2 / 6))) ≤
      ∫ t : ℝ, |t| ^ 3 * Real.exp (-(t ^ 2 * vlo / 6)) := by
    apply integral_mono (integrable_cubic_gaussian (sq_pos_of_pos hσ)) (integrable_cubic_gaussian hvlo)
    intro t
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlo (sq_nonneg t)]
  have hs : σ ≤ Real.sqrt vhi := (Real.le_sqrt hσ.le ((sq_nonneg σ).trans hhi)).mpr hhi
  have hb0 : 0 ≤ β := (by norm_num : (0 : ℝ) ≤ 1).trans hβ
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσ.le hs 3) hb0) hi
    (integral_nonneg fun t => by positivity) (by positivity)

end

end PGM
