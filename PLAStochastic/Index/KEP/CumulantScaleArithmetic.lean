import Mathlib.Tactic

/-!
# Uniform scale conditions for the conditional stopped cumulant

The reference lower compression bound pays both the small conditional tilt
and the quadratic cumulant remainder. The geometric window-to-compression
ratio pays the stopping compensator at the same fixed positive exponent.
-/

set_option autoImplicit false

namespace PGM

theorem kep_cumulant_small_tilt {theta R C : ℝ} (htheta : 0 < theta)
    (hR : 0 < R) (hC : 0 < C) (hlarge : 4 * R ≤ C) :
    2 * theta / C ≤ (theta / R) / 2 := by
  rw [div_le_iff₀ hC]
  have h := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ theta / R / 2 by positivity)
  have he : (theta / R / 2) * (4 * R) = 2 * theta := by field_simp; ring
  rw [he] at h
  exact h

theorem kep_cumulant_quadratic_cost {theta R C B : ℝ} (htheta : 0 < theta)
    (hR : 0 < R) (hC : 0 < C) (hlarge : 16 * B * R ≤ theta * C) :
    8 * B / (theta / R) ^ 2 * (2 * theta / C) ≤ R := by
  have he : 8 * B / (theta / R) ^ 2 * (2 * theta / C) =
      (16 * B * R) * R / (theta * C) := by field_simp; ring
  rw [he, div_le_iff₀ (mul_pos htheta hC)]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_right hlarge hR.le

theorem kep_cumulant_stopping_scale {theta R C A cb eps M : ℝ}
    (htheta : 0 ≤ theta) (hR : 0 < R) (hC : 0 < C) (hA : 0 < A) (hcb : 0 < cb)
    (hcompression : eps ^ 2 / cb ≤ C) (hM : M ≤ A * eps ^ 2)
    (hsmall : theta ≤ 1 / (864 * R * A * cb)) :
    (3 * R * (2 * theta / C)) * M ≤ 1 / 144 := by
  have hCb : eps ^ 2 ≤ C * cb := (div_le_iff₀ hcb).mp hcompression
  have hratio : M / C ≤ A * cb := by
    rw [div_le_iff₀ hC]
    calc
      _ ≤ A * eps ^ 2 := hM
      _ ≤ A * (C * cb) := mul_le_mul_of_nonneg_left hCb hA.le
      _ = _ := by ring
  have hthetaBudget : 864 * R * A * cb * theta ≤ 1 := by
    have h := (le_div_iff₀ (show 0 < 864 * R * A * cb by positivity)).mp hsmall
    simpa only [mul_comm] using h
  calc
    _ = 6 * R * theta * (M / C) := by ring
    _ ≤ 6 * R * theta * (A * cb) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ _ := by nlinarith

end PGM
