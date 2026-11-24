import PLAStochastic.Index.GEP.StrongApprox.LocalCLT.LowFrequency

/-! # Gaussian smoothing and the uniform high-frequency Fourier bound -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Gaussian smoothing makes every characteristic power integrable, including singular laws. -/
theorem integrable_smoothed_charFun_power (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {h : ℝ} (hh : 0 < h) (l : ℕ) :
    Integrable (fun t : ℝ => ‖charFun μ t‖ ^ l * Real.exp (-(h ^ 2 * t ^ 2 / 2))) := by
  have hi : Integrable (fun t : ℝ => Real.exp (-(h ^ 2 * t ^ 2 / 2))) := by
    convert integrable_exp_neg_mul_sq (show 0 < h ^ 2 / 2 by positivity) using 1
    funext t
    congr 1
    ring
  refine hi.mono' (by fun_prop) (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (Real.exp_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one t))

/-- The Fourier damping mass has the expected inverse-width dependence. -/
theorem integral_gaussian_damping {h : ℝ} (hh : 0 < h) :
    (∫ t : ℝ, Real.exp (-(h ^ 2 * t ^ 2 / 2))) = Real.sqrt (2 * Real.pi) / h := by
  have he : (fun t : ℝ => Real.exp (-(h ^ 2 * t ^ 2 / 2))) =
      fun t : ℝ => Real.exp (-(h ^ 2 / 2) * t ^ 2) := by
    funext t
    congr 1
    ring
  rw [he, integral_gaussian]
  have hq : Real.pi / (h ^ 2 / 2) = (2 * Real.pi) / h ^ 2 := by field_simp
  rw [hq, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hh]

/-- A Cramer gap controls the entire smoothed high-frequency integral. -/
theorem integral_highFrequency_smoothed_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {δ κ h : ℝ} (hκ1 : κ ≤ 1) (hh : 0 < h)
    (hgap : ∀ t : ℝ, δ ≤ |t| → ‖charFun μ t‖ ≤ 1 - κ) (l : ℕ) :
    (∫ t : ℝ in {t : ℝ | δ ≤ |t|},
      ‖charFun μ t‖ ^ l * Real.exp (-(h ^ 2 * t ^ 2 / 2))) ≤
        (1 - κ) ^ l * (Real.sqrt (2 * Real.pi) / h) := by
  have hq : 0 ≤ 1 - κ := sub_nonneg.mpr hκ1
  have hi := integrable_smoothed_charFun_power μ hh l
  have hg : Integrable (fun t : ℝ => (1 - κ) ^ l * Real.exp (-(h ^ 2 * t ^ 2 / 2))) := by
    have hb : Integrable (fun t : ℝ => Real.exp (-(h ^ 2 * t ^ 2 / 2))) := by
      simpa using integrable_smoothed_charFun_power μ hh 0
    exact hb.const_mul _
  have hA : MeasurableSet {t : ℝ | δ ≤ |t|} := measurableSet_le measurable_const (by fun_prop)
  calc
    _ ≤ ∫ t : ℝ in {t : ℝ | δ ≤ |t|}, (1 - κ) ^ l * Real.exp (-(h ^ 2 * t ^ 2 / 2)) := by
      apply integral_mono_ae hi.integrableOn hg.integrableOn
      filter_upwards [ae_restrict_mem hA] with t ht
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hgap t ht) l)
        (Real.exp_nonneg _)
    _ ≤ ∫ t : ℝ, (1 - κ) ^ l * Real.exp (-(h ^ 2 * t ^ 2 / 2)) :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun t => by positivity) hg
    _ = _ := by rw [integral_const_mul, integral_gaussian_damping hh]

/-- A geometric factor absorbs any fixed polynomial power, with an explicit constant. -/
theorem pow_mul_geometric_le {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (l p : ℕ) :
    (l : ℝ) ^ p * (1 - κ) ^ l ≤ (p.factorial : ℝ) / κ ^ p := by
  have hq0 : 0 ≤ 1 - κ := sub_nonneg.mpr hκ1
  have hq : 1 - κ ≤ Real.exp (-κ) := by linarith [Real.add_one_le_exp (-κ)]
  have hp : (1 - κ) ^ l ≤ Real.exp (-(κ * l)) := by
    apply (pow_le_pow_left₀ hq0 hq l).trans_eq
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hf : 0 < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have hx := Real.pow_div_factorial_le_exp (κ * l) (by positivity) p
  rw [div_le_iff₀ hf] at hx
  have he : (κ * l) ^ p * Real.exp (-(κ * l)) ≤ (p.factorial : ℝ) := by
    apply (mul_le_mul_of_nonneg_right hx (Real.exp_nonneg _)).trans_eq
    rw [mul_right_comm, ← Real.exp_add]
    simp
  calc
    (l : ℝ) ^ p * (1 - κ) ^ l ≤ (l : ℝ) ^ p * Real.exp (-(κ * l)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (p.factorial : ℝ) / κ ^ p := by
      rw [le_div_iff₀ (pow_pos hκ p)]
      simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using he

/-- Width `h` with `h⁻¹ ≤ l⁸` gives the high-frequency `O(l⁻¹)` bound used by the blueprint. -/
theorem integral_highFrequency_smoothed_le_inv_length {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {δ κ h : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hh : 0 < h)
    (hgap : ∀ t : ℝ, δ ≤ |t| → ‖charFun μ t‖ ≤ 1 - κ)
    {l : ℕ} (hl : 1 ≤ l) (hscale : 1 / h ≤ (l : ℝ) ^ 8) :
    (∫ t : ℝ in {t : ℝ | δ ≤ |t|},
      ‖charFun μ t‖ ^ l * Real.exp (-(h ^ 2 * t ^ 2 / 2))) ≤
        (Real.sqrt (2 * Real.pi) * (Nat.factorial 9 : ℝ) / κ ^ 9) / l := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have hq0 : 0 ≤ 1 - κ := sub_nonneg.mpr hκ1
  apply (integral_highFrequency_smoothed_le hκ1 hh hgap l).trans
  calc
    (1 - κ) ^ l * (Real.sqrt (2 * Real.pi) / h) ≤
        Real.sqrt (2 * Real.pi) * ((l : ℝ) ^ 8 * (1 - κ) ^ l) := by
      have hm := mul_le_mul_of_nonneg_left hscale
        (mul_nonneg (Real.sqrt_nonneg (2 * Real.pi)) (pow_nonneg hq0 l))
      convert hm using 1 <;> first | rfl | ring
    _ ≤ (Real.sqrt (2 * Real.pi) * (Nat.factorial 9 : ℝ) / κ ^ 9) / l := by
      rw [le_div_iff₀ hl0]
      have hp := mul_le_mul_of_nonneg_left (pow_mul_geometric_le hκ hκ1 l 9)
        (Real.sqrt_nonneg (2 * Real.pi))
      convert hp using 1 <;> first | rfl | ring

end

end PGM
