import PLAStochastic.Index.GEP.OrbitClosure.SumDensity
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-! # Quantitative low-frequency characteristic-function estimates -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal

/-- A third absolute moment bounds the complete complex Taylor remainder. -/
theorem charFun_taylor_three_remainder {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {v K : ℝ} (h3 : MemLp id 3 μ) (hm : ∫ x : ℝ, x ∂μ = 0)
    (hv : ∫ x : ℝ, x ^ 2 ∂μ = v) (hK : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ K) (t : ℝ) :
    ‖charFun μ t - ((1 - v * t ^ 2 / 2 : ℝ) : ℂ)‖ ≤ K * |t| ^ 3 / 6 := by
  have hi1 : Integrable (fun x : ℝ => x) μ := h3.integrable (by norm_num)
  have hi2 : Integrable (fun x : ℝ => x ^ 2) μ :=
    (h3.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)).integrable_sq
  have hi3 : Integrable (fun x : ℝ => |x| ^ 3) μ := by
    simpa [Real.norm_eq_abs] using h3.integrable_norm_pow (by norm_num)
  let w : ℝ → ℂ := fun x => Complex.exp (((t * x : ℝ) : ℂ) * I)
  have hwi : Integrable w μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
    exact (Complex.norm_exp_ofReal_mul_I _).le
  let P : ℝ → ℂ := fun x => ((1 - t ^ 2 / 2 * x ^ 2 : ℝ) : ℂ) + ((t * x : ℝ) : ℂ) * I
  have hri : Integrable (fun x : ℝ => 1 - t ^ 2 / 2 * x ^ 2) μ :=
    (integrable_const 1).sub (hi2.const_mul _)
  have hii : Integrable (fun x : ℝ => t * x) μ := hi1.const_mul t
  have hPi : Integrable P μ := hri.ofReal.add (hii.ofReal.mul_const I)
  have hre : (∫ x : ℝ, 1 - t ^ 2 / 2 * x ^ 2 ∂μ) = 1 - v * t ^ 2 / 2 := by
    rw [integral_sub (integrable_const 1) (hi2.const_mul _), integral_const_mul, hv]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  have him : (∫ x : ℝ, t * x ∂μ) = 0 := by rw [integral_const_mul, hm, mul_zero]
  have hIP : (∫ x, P x ∂μ) = ((1 - v * t ^ 2 / 2 : ℝ) : ℂ) := by
    rw [show (∫ x, P x ∂μ) = _ from integral_add hri.ofReal (hii.ofReal.mul_const I),
      integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, hre, him]
    simp
  have hEq : charFun μ t - ((1 - v * t ^ 2 / 2 : ℝ) : ℂ) = ∫ x, w x - P x ∂μ := by
    rw [integral_sub hwi hPi, hIP]
    rfl
  have hp (x : ℝ) : ‖w x - P x‖ ≤ |t| ^ 3 / 6 * |x| ^ 3 := by
    have he : w x - P x = Complex.exp (((t * x : ℝ) : ℂ) * I) - 1 -
        ((t * x : ℝ) : ℂ) * I + (((t * x) ^ 2 / 2 : ℝ) : ℂ) := by
      dsimp [w, P]
      push_cast
      ring
    rw [he]
    calc
      _ ≤ |t * x| ^ 3 / 6 := norm_cexp_sub_taylor_two_le (t * x)
      _ = |t| ^ 3 / 6 * |x| ^ 3 := by rw [abs_mul, mul_pow]; ring
  rw [hEq]
  calc
    ‖∫ x, w x - P x ∂μ‖ ≤ ∫ x, ‖w x - P x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, |t| ^ 3 / 6 * |x| ^ 3 ∂μ :=
      integral_mono (hwi.sub hPi).norm (hi3.const_mul _) hp
    _ = |t| ^ 3 / 6 * ∫ x, |x| ^ 3 ∂μ := integral_const_mul _ _
    _ ≤ |t| ^ 3 / 6 * K := mul_le_mul_of_nonneg_left hK (by positivity)
    _ = K * |t| ^ 3 / 6 := by ring

/-- The existing Taylor modulus bound gives a Gaussian majorant near zero. -/
theorem norm_charFun_le_exp_small {μ : Measure ℝ} [IsProbabilityMeasure μ] {m σ β : ℝ}
    (h3 : MemLp id 3 μ) (hm : ∫ x, x ∂μ = m) (hvar : ∫ x, (x - m) ^ 2 ∂μ = σ ^ 2)
    (hσ : 0 < σ) (hβ : 1 ≤ β) (hκ : ∫ x, |x - m| ^ 3 ∂μ ≤ β * σ ^ 3) {t : ℝ}
    (ht : |t| ≤ 1 / (β * σ)) :
    ‖charFun μ t‖ ≤ Real.exp (-(t ^ 2 * σ ^ 2 / 3)) := by
  apply (norm_charFun_le_taylor h3 hm hvar hσ hβ hκ ht).trans
  have he := Real.add_one_le_exp (-(t ^ 2 * σ ^ 2 / 3))
  linarith

/-- The Gaussian characteristic function has a cubic local remainder with the same quadratic part. -/
theorem gaussian_taylor_three_remainder {σ t : ℝ} (hσ : 0 < σ) (ht : |t| * σ ≤ 1) :
    ‖((Real.exp (-(t ^ 2 * σ ^ 2 / 2)) : ℝ) : ℂ) - ((1 - t ^ 2 * σ ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      σ ^ 3 * |t| ^ 3 / 4 := by
  let a := |t| * σ
  have ha : 0 ≤ a := mul_nonneg (abs_nonneg _) hσ.le
  have ha1 : a ≤ 1 := ht
  have hsq : t ^ 2 * σ ^ 2 = a ^ 2 := by dsimp [a]; rw [mul_pow, sq_abs]
  have hcube : σ ^ 3 * |t| ^ 3 = a ^ 3 := by dsimp [a]; ring
  rw [hsq, hcube, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hu : ‖-(a ^ 2 / 2)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity : 0 ≤ a ^ 2 / 2)]
    nlinarith
  have he := Real.norm_exp_sub_one_sub_id_le hu
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ a ^ 2 / 2)] at he
  have hid : Real.exp (-(a ^ 2 / 2)) - (1 - a ^ 2 / 2) =
      Real.exp (-(a ^ 2 / 2)) - 1 - (-(a ^ 2 / 2)) := by ring
  rw [hid]
  apply he.trans
  have hp := mul_le_mul_of_nonneg_left ha1 (pow_nonneg ha 3)
  nlinarith

/-- The complex characteristic function differs from its matching Gaussian by a cubic error. -/
theorem charFun_sub_gaussian_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {σ β : ℝ}
    (h3 : MemLp id 3 μ) (hm : ∫ x : ℝ, x ∂μ = 0)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (hβ : 1 ≤ β)
    (hκ : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ β * σ ^ 3) {t : ℝ} (ht : |t| ≤ 1 / (β * σ)) :
    ‖charFun μ t - ((Real.exp (-(t ^ 2 * σ ^ 2 / 2)) : ℝ) : ℂ)‖ ≤ β * σ ^ 3 * |t| ^ 3 := by
  have hb : 0 < β * σ := mul_pos (lt_of_lt_of_le zero_lt_one hβ) hσ
  have ht' : |t| * σ ≤ 1 := by
    have htx := (le_div_iff₀ hb).mp ht
    have hp := mul_le_mul_of_nonneg_left hβ (mul_nonneg (abs_nonneg t) hσ.le)
    nlinarith
  have hr := charFun_taylor_three_remainder h3 hm hvar hκ t
  have hg := gaussian_taylor_three_remainder hσ ht'
  have hP : ((1 - σ ^ 2 * t ^ 2 / 2 : ℝ) : ℂ) = ((1 - t ^ 2 * σ ^ 2 / 2 : ℝ) : ℂ) := by
    congr 1
    ring
  rw [hP] at hr
  calc
    _ ≤ ‖charFun μ t - ((1 - t ^ 2 * σ ^ 2 / 2 : ℝ) : ℂ)‖ +
        ‖((Real.exp (-(t ^ 2 * σ ^ 2 / 2)) : ℝ) : ℂ) - ((1 - t ^ 2 * σ ^ 2 / 2 : ℝ) : ℂ)‖ :=
      (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_eq
        (congrArg (fun z : ℝ => ‖charFun μ t - ((1 - t ^ 2 * σ ^ 2 / 2 : ℝ) : ℂ)‖ + z)
          (norm_sub_rev _ _))
    _ ≤ (β * σ ^ 3) * |t| ^ 3 / 6 + σ ^ 3 * |t| ^ 3 / 4 := add_le_add hr hg
    _ ≤ β * σ ^ 3 * |t| ^ 3 := by
      have hp := mul_le_mul_of_nonneg_right hβ (mul_nonneg (pow_nonneg hσ.le 3) (pow_nonneg (abs_nonneg t) 3))
      nlinarith [mul_nonneg (pow_nonneg hσ.le 3) (pow_nonneg (abs_nonneg t) 3)]

/-- Telescoping powers preserves the common exponential contraction. -/
theorem norm_pow_succ_sub_pow_succ_le_of_bounds {a b : ℂ} {q e : ℝ}
    (hq : 0 ≤ q) (he : 0 ≤ e) (ha : ‖a‖ ≤ q) (hb : ‖b‖ ≤ q)
    (hab : ‖a - b‖ ≤ e) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ (n + 1) * q ^ n * e := by
  induction n with
  | zero => simpa using hab
  | succ n ih =>
      simp only [Nat.cast_add, Nat.cast_one]
      have heq : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
          a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by ring
      rw [heq]
      calc
        _ ≤ ‖a * (a ^ (n + 1) - b ^ (n + 1))‖ + ‖(a - b) * b ^ (n + 1)‖ := norm_add_le _ _
        _ = ‖a‖ * ‖a ^ (n + 1) - b ^ (n + 1)‖ + ‖a - b‖ * ‖b‖ ^ (n + 1) := by
          rw [norm_mul, norm_mul, norm_pow]
        _ ≤ q * ((n + 1) * q ^ n * e) + e * q ^ (n + 1) := add_le_add
          (mul_le_mul ha ih (norm_nonneg _) hq)
          (mul_le_mul hab (pow_le_pow_left₀ (norm_nonneg _) hb _) (by positivity) he)
        _ = (n + 1 + 1) * q ^ (n + 1) * e := by rw [pow_succ]; ring

/-- Low-frequency convolution powers differ from their matching Gaussian at the quantitative rate. -/
theorem charFun_pow_sub_gaussian_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {σ β : ℝ}
    (h3 : MemLp id 3 μ) (hm : ∫ x : ℝ, x ∂μ = 0)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (hβ : 1 ≤ β)
    (hκ : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ β * σ ^ 3) {t : ℝ} (ht : |t| ≤ 1 / (β * σ)) (n : ℕ) :
    ‖charFun μ t ^ (n + 1) -
      ((Real.exp (-((n + 1) * t ^ 2 * σ ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
        (n + 1) * (β * σ ^ 3 * |t| ^ 3) * Real.exp (-((n : ℝ) * t ^ 2 * σ ^ 2 / 3)) := by
  have hvar' : ∫ x : ℝ, (x - 0) ^ 2 ∂μ = σ ^ 2 := by simpa using hvar
  have hκ' : ∫ x : ℝ, |x - 0| ^ 3 ∂μ ≤ β * σ ^ 3 := by simpa using hκ
  have ha := norm_charFun_le_exp_small h3 hm hvar' hσ hβ hκ' ht
  have hb : ‖((Real.exp (-(t ^ 2 * σ ^ 2 / 2)) : ℝ) : ℂ)‖ ≤
      Real.exp (-(t ^ 2 * σ ^ 2 / 3)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg σ)]
  have hE : 0 ≤ β * σ ^ 3 * |t| ^ 3 := by have := hβ; positivity
  have hp := norm_pow_succ_sub_pow_succ_le_of_bounds (Real.exp_pos _).le hE ha hb
    (charFun_sub_gaussian_le h3 hm hvar hσ hβ hκ ht) n
  have hpow : ((Real.exp (-(t ^ 2 * σ ^ 2 / 2)) : ℝ) : ℂ) ^ (n + 1) =
      ((Real.exp (-((n + 1) * t ^ 2 * σ ^ 2 / 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hex : Real.exp (-(t ^ 2 * σ ^ 2 / 3)) ^ n =
      Real.exp (-((n : ℝ) * t ^ 2 * σ ^ 2 / 3)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpow, hex] at hp
  exact hp.trans_eq (by ring)

end

end PGM
