import PLAStochastic.Index.KEP.SpatialBudget

/-!
# An integer polynomial intensity cutoff for the spatial comparison

A fixed epsilon power 153 suffices for the epsilon-102 weighted two-thirds
spatial cutoff. Cubing both nonnegative sides avoids fractional-power
constants and preserves the original unrestricted sample-size quantifiers.
-/

set_option autoImplicit false

namespace PGM

theorem kep_spatial_cutoff_of_polynomial_intensity {eps n m delta : ℝ}
    (heps : 1 ≤ eps) (hm : 1 ≤ m) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hn : (1 / delta) ^ 3 * eps ^ 153 * m ≤ n) :
    1 ≤ n ∧ eps ^ 102 * (m / n) ^ (2 / 3 : ℝ) ≤ delta := by
  have heps0 : 0 < eps := zero_lt_one.trans_le heps
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hInv : 1 ≤ 1 / delta := (le_div_iff₀ hdelta).mpr (by simpa using hdelta1)
  have hN1 : 1 ≤ (1 / delta) ^ 3 * eps ^ 153 * m := by
    have h1 : 1 ≤ (1 / delta) ^ 3 := one_le_pow₀ hInv
    have h2 : 1 ≤ eps ^ 153 := one_le_pow₀ heps
    have h12 : 1 ≤ (1 / delta) ^ 3 * eps ^ 153 := by
      simpa only [one_mul] using mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : 0 ≤ (1 / delta) ^ 3)
    simpa only [one_mul] using mul_le_mul h12 hm (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 ≤ (1 / delta) ^ 3 * eps ^ 153)
  have hn1 : 1 ≤ n := hN1.trans hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn1
  have hratio : m / n ≤ delta ^ 3 / eps ^ 153 := by
    rw [div_le_div_iff₀ hn0 (pow_pos heps0 153)]
    have h := mul_le_mul_of_nonneg_left hn (pow_nonneg hdelta.le 3)
    have he : delta ^ 3 * ((1 / delta) ^ 3 * eps ^ 153 * m) = m * eps ^ 153 := by
      field_simp
    rw [he] at h
    simpa only [mul_comm] using h
  have hscaled : eps ^ 153 * (m / n) ≤ delta ^ 3 := by
    have h := (le_div_iff₀ (pow_pos heps0 153)).mp hratio
    simpa only [mul_comm] using h
  have hdelta3 : delta ^ 3 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hdelta.le hdelta1 3
  have hc : (eps ^ 102 * (m / n) ^ (2 / 3 : ℝ)) ^ 3 = (eps ^ 153 * (m / n)) ^ 2 := by
    rw [mul_pow, kep_two_thirds_cubed (div_nonneg hm0.le hn0.le)]
    ring
  refine ⟨hn1, ?_⟩
  apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ eps ^ 102 * (m / n) ^ (2 / 3 : ℝ))
    hdelta.le (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [hc]
  calc
    _ ≤ (delta ^ 3) ^ 2 := pow_le_pow_left₀ (by positivity) hscaled 2
    _ ≤ delta ^ 3 := by nlinarith [pow_nonneg hdelta.le 3]

end PGM
