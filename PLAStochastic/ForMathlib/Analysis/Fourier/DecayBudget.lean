import PLAStochastic.ForMathlib.Analysis.Calculus.ExponentialDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary budgets for three-band Fourier estimates

These inequalities pay polynomial losses with a stretched exponential, a real
exponential in the large parameter, or one extra inverse power on a logarithmic band.
-/

noncomputable section

open Filter Topology

namespace PGM

/-- Every polynomial loss can be absorbed in half of a stretched-exponential rate. -/
theorem polynomial_mul_stretchedExp_le {c : ℝ} (hc : 0 < c) (d : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      (1 + t) ^ d * Real.exp (-c * Real.sqrt t) ≤ B * Real.exp (-(c / 2) * Real.sqrt t) := by
  let C : ℝ := ((2 * d).factorial : ℝ) / (c / 2) ^ (2 * d)
  refine ⟨C * Real.exp (c / 2), by dsimp [C]; positivity, fun t ht => ?_⟩
  have hs : 1 + t ≤ (1 + Real.sqrt t) ^ 2 := by
    nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]
  have hp := Real.pow_le_factorial_inv_mul_exp (2 * d) (by positivity : 0 < c / 2)
    (by positivity : 0 ≤ 1 + Real.sqrt t)
  calc
    _ ≤ (1 + Real.sqrt t) ^ (2 * d) * Real.exp (-c * Real.sqrt t) := by
      rw [pow_mul]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hs d) (Real.exp_pos _).le
    _ ≤ (C * Real.exp ((c / 2) * (1 + Real.sqrt t))) * Real.exp (-c * Real.sqrt t) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- A fixed real exponential pays any polynomial and any requested inverse order. -/
theorem polynomial_mul_exp_le_inverse {c : ℝ} (hc : 0 < c) (d n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ eps : ℝ, 1 ≤ eps →
      eps ^ d * Real.exp (-c * eps) ≤ B * (eps⁻¹) ^ n := by
  let B : ℝ := ((d + n).factorial : ℝ) / c ^ (d + n)
  refine ⟨B, by dsimp [B]; positivity, fun eps heps => ?_⟩
  have he : 0 < eps := zero_lt_one.trans_le heps
  have hp := Real.pow_le_factorial_inv_mul_exp (d + n) hc he.le
  have hb : eps ^ (d + n) * Real.exp (-c * eps) ≤ B := by
    calc
      _ ≤ (B * Real.exp (c * eps)) * Real.exp (-c * eps) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = B := by rw [mul_assoc, ← Real.exp_add]; simp
  apply (mul_le_mul_iff_right₀ (pow_pos he n)).mp
  calc
    _ = eps ^ (d + n) * Real.exp (-c * eps) := by rw [pow_add]; ring
    _ ≤ B := hb
    _ = _ := by
      calc
        B = B * (eps * eps⁻¹) ^ n := by simp [he.ne']
        _ = _ := by rw [mul_pow]; ring

/-- On a fixed logarithmic band, one extra inverse power absorbs every fixed polynomial loss. -/
theorem eventually_log_band_polynomial_le (A : ℝ) (d : ℕ) :
    ∀ᶠ eps : ℝ in atTop,
      (1 + (A * Real.log eps) ^ 2) ^ d ≤ (1 + A ^ 2) ^ d * eps := by
  have hlog := (Real.isLittleO_pow_log_id_atTop (n := 2 * d)).bound (show (0 : ℝ) < 1 by norm_num)
  have hlog1 : ∀ᶠ eps : ℝ in atTop, 1 ≤ Real.log eps :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hlog, hlog1, eventually_ge_atTop (1 : ℝ)] with eps hp hl he
  have hl0 : 0 ≤ Real.log eps := by linarith
  have hp' : Real.log eps ^ (2 * d) ≤ eps := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hl0 _), abs_of_nonneg (by linarith : 0 ≤ eps),
      mul_one, one_mul, id_eq] using hp
  calc
    _ ≤ ((1 + A ^ 2) * Real.log eps ^ 2) ^ d := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [sq_nonneg A]
    _ = (1 + A ^ 2) ^ d * Real.log eps ^ (2 * d) := by rw [mul_pow, ← pow_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hp' (by positivity)

/-- A logarithmic cutoff extracts any fixed inverse power from a stretched exponential. -/
theorem stretchedExp_log_cutoff {a A eps t : ℝ} {n : ℕ}
    (ha : 0 < a) (heps : 1 ≤ eps) (hA : (n : ℝ) ≤ a * A)
    (_ht : 0 ≤ t) (hcut : (A * Real.log eps) ^ 2 ≤ t) :
    Real.exp (-a * Real.sqrt t) ≤ (eps⁻¹) ^ n := by
  have he : 0 < eps := zero_lt_one.trans_le heps
  have hl : 0 ≤ Real.log eps := Real.log_nonneg heps
  have hsq : A * Real.log eps ≤ Real.sqrt t := by
    exact (le_abs_self _).trans (by simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hcut)
  calc
    _ ≤ Real.exp (-((n : ℝ) * Real.log eps)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = _ := by rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log he, inv_pow]

/-- The high-frequency derivative prior can pay any fixed inverse order at `eps^(1+δ)`. -/
theorem exists_high_frequency_order {δ : ℝ} (hδ : 0 < δ) (m n : ℕ) :
    ∃ r : ℕ, ∀ {eps t K y : ℝ}, 1 ≤ eps → eps ^ (1 + δ) ≤ t → 0 ≤ K → 0 ≤ y →
      t ^ r * y ≤ K * eps ^ (r + 2) →
      (1 + t) ^ (m + 2) * y ≤ 2 ^ (m + 2) * K * (eps⁻¹) ^ n := by
  obtain ⟨s, hs⟩ := exists_nat_gt (((n + m + 4 : ℕ) : ℝ) / δ)
  have hs' : ((n + m + 4 : ℕ) : ℝ) ≤ δ * s := by
    have h := (div_lt_iff₀ hδ).mp hs
    linarith
  let r := m + 2 + s
  refine ⟨r, fun {eps t K y} he ht hK hy hb => ?_⟩
  have he0 : 0 < eps := zero_lt_one.trans_le he
  have hcut1 : 1 ≤ eps ^ (1 + δ) := Real.one_le_rpow he (by linarith)
  have ht1 : 1 ≤ t := hcut1.trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hpow : eps ^ (r + 2 + n) ≤ t ^ s := by
    calc
      _ = eps ^ (((r + 2 + n : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
      _ ≤ eps ^ ((1 + δ) * s) := by
        apply Real.rpow_le_rpow_of_exponent_le he
        dsimp [r]
        push_cast at hs' ⊢
        linarith
      _ = (eps ^ (1 + δ)) ^ s := by rw [← Real.rpow_natCast, ← Real.rpow_mul he0.le]
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg he0.le _) ht s
  have hcore : t ^ (m + 2) * y ≤ K * (eps⁻¹) ^ n := by
    apply (mul_le_mul_iff_right₀ (pow_pos ht0 s)).mp
    calc
      _ = t ^ r * y := by dsimp [r]; rw [pow_add]; ring
      _ ≤ K * eps ^ (r + 2) := hb
      _ = (K * (eps⁻¹) ^ n) * eps ^ (r + 2 + n) := by
        rw [pow_add (eps) (r + 2) n, inv_pow]
        field_simp
      _ ≤ (K * (eps⁻¹) ^ n) * t ^ s := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (2 * t) ^ (m + 2) * y := by gcongr; linarith
    _ = 2 ^ (m + 2) * (t ^ (m + 2) * y) := by rw [mul_pow]; ring
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcore (by positivity : 0 ≤ (2 : ℝ) ^ (m + 2))

end PGM
