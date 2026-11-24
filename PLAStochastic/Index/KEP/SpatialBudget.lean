import PLAStochastic.Index.KEP.ReferenceScale.MeanSpan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Spatial cutoff arithmetic for the uniform Poisson induction

The two-thirds spatial error is tracked with a fixed polynomial epsilon
weight. Quadratic reference compression dominates its linear epsilon
propagation factor uniformly above one fixed threshold.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

def kepSpatialCutoff (eps n : ℝ) (j : ℕ) : ℝ :=
  eps ^ 102 * (kepReferenceSpan eps j / n) ^ (2 / 3 : ℝ)

def kepSpatialError (D eps n : ℝ) (j : ℕ) : ℝ :=
  D * eps ^ 100 * (kepReferenceSpan eps j / n) ^ (2 / 3 : ℝ)

theorem kep_two_thirds_cubed {C : ℝ} (hC : 0 ≤ C) :
    (C ^ (2 / 3 : ℝ)) ^ 3 = C ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hC]
  norm_num

theorem kep_unit_interval_le_two_thirds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q ≤ q ^ (2 / 3 : ℝ) := by
  apply (pow_le_pow_iff_left₀ hq0 (Real.rpow_nonneg hq0 _) (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [kep_two_thirds_cubed hq0]
  have h := mul_le_mul_of_nonneg_left hq1 (sq_nonneg q)
  nlinarith

theorem kep_two_thirds_compression_dominates {eps C K cb : ℝ}
    (heps : 0 < eps) (hcb : 0 < cb) (hK : 0 ≤ K)
    (hC : eps ^ 2 / cb ≤ C) (hbig : (2 * K) ^ 3 * cb ^ 2 ≤ eps) :
    2 * K * eps ≤ C ^ (2 / 3 : ℝ) := by
  have hCp : 0 ≤ C := (div_nonneg (sq_nonneg eps) hcb.le).trans hC
  apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ 2 * K * eps)
    (Real.rpow_nonneg hCp _) (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [kep_two_thirds_cubed hCp]
  calc
    _ ≤ (eps ^ 2 / cb) ^ 2 := by
      rw [div_pow, le_div_iff₀ (sq_pos_of_pos hcb)]
      calc
        _ = ((2 * K) ^ 3 * cb ^ 2) * eps ^ 3 := by ring
        _ ≤ eps * eps ^ 3 := mul_le_mul_of_nonneg_right hbig (by positivity)
        _ = _ := by ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hC 2

theorem kep_two_thirds_parent_scale {m C n : ℝ} (hm : 0 ≤ m) (hC : 0 ≤ C) (hn : 0 < n) :
    (m * C / n) ^ (2 / 3 : ℝ) = C ^ (2 / 3 : ℝ) * (m / n) ^ (2 / 3 : ℝ) := by
  rw [show m * C / n = C * (m / n) by ring,
    Real.mul_rpow hC (div_nonneg hm hn.le)]

theorem kepSpatialCutoff_mono {eps n : ℝ} (hn : 0 < n) {j k : ℕ}
    (hm : 0 ≤ kepReferenceSpan eps j) (hjk : kepReferenceSpan eps j ≤ kepReferenceSpan eps k) :
    kepSpatialCutoff eps n j ≤ kepSpatialCutoff eps n k := by
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (div_nonneg hm hn.le) (div_le_div_of_nonneg_right hjk hn.le) (by norm_num))
    (by positivity)

theorem kep_spatial_cutoff_lower_powers {eps q delta : ℝ} (heps : 1 ≤ eps)
    (hq : 0 ≤ q) (hcut : eps ^ 102 * q ≤ delta) (p : ℕ) (hp : p ≤ 102) :
    eps ^ p * q ≤ delta := by
  have hpow : eps ^ p ≤ eps ^ 102 := pow_le_pow_right₀ heps hp
  exact (mul_le_mul_of_nonneg_right hpow hq).trans hcut

theorem kep_base_spatial_error {eps n K D : ℝ} (heps : 1 ≤ eps) (hn : 1 ≤ n)
    (hK : 0 ≤ K) (hKD : K ≤ D) : K / n ≤ D * eps ^ 100 * (1 / n) ^ (2 / 3 : ℝ) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hq : 1 / n ≤ (1 / n) ^ (2 / 3 : ℝ) :=
    kep_unit_interval_le_two_thirds (by positivity) ((div_le_one hn0).mpr hn)
  have hpow : 1 ≤ eps ^ 100 := one_le_pow₀ heps
  calc
    _ = K * (1 / n) := by ring
    _ ≤ K * (1 / n) ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left hq hK
    _ ≤ D * (1 / n) ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_right hKD (Real.rpow_nonneg (by positivity) _)
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right (hK.trans hKD) hpow) (Real.rpow_nonneg (by positivity) _)

end

end PGM
