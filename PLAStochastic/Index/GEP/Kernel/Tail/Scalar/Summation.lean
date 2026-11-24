import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.OuterGreen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Explicit time and slope budgets for full marked pin tails -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 800000

/-- Small-slope Chernoff decay absorbs the two actual inverse-slope density
factors without losing exponential decay in total random time. -/
theorem kernel_small_slope_inverse_square {a c N : ℝ} (ha : 0 < a)
    (halo : a ≤ 1 / 2) (hc : 0 < c) (hN : 1 ≤ N) :
    a⁻¹ ^ 2 * Real.exp (-c * N / a) ≤ (8 / c ^ 2) * Real.exp (-c * N) := by
  have he₁ : Real.exp (-(c / (2 * a))) ≤ 8 * a ^ 2 / c ^ 2 := by
    have hh := kr_exp_neg_le (c := c) (w := 1 / (2 * a)) hc (by positivity)
    convert hh using 1 <;> field_simp
    ring
  have hexp : -c * N / a ≤ -(c / (2 * a)) + (-c * N) := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * a by positivity)).mp
    field_simp
    have hh := mul_le_mul_of_nonneg_right halo (show 0 ≤ c * N by positivity)
    nlinarith
  calc
    _ ≤ a⁻¹ ^ 2 * (Real.exp (-(c / (2 * a))) * Real.exp (-c * N)) := by
      rw [← Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (sq_nonneg _)
    _ ≤ a⁻¹ ^ 2 * ((8 * a ^ 2 / c ^ 2) * Real.exp (-c * N)) := by gcongr
    _ = _ := by field_simp

/-- The surviving large-slope scale has finite mass on the entire half-axis. -/
theorem kernel_integrable_inverse_square_half :
    IntegrableOn (fun a : ℝ => a⁻¹ ^ 2) (Ioi (1 / 2 : ℝ)) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (c := (1 / 2 : ℝ)) (by norm_num)
  convert h using 1
  funext a
  simp

theorem kernel_integral_inverse_square_half :
    (∫ a : ℝ in Ioi (1 / 2 : ℝ), a⁻¹ ^ 2) = 2 := by
  have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (c := (1 / 2 : ℝ)) (by norm_num)
  have he : (fun a : ℝ => a⁻¹ ^ 2) = fun a => a ^ (-2 : ℝ) := by
    funext a
    simp
  rw [he, h]
  norm_num

/-- Three independent random-length indices, including zero insertion sides,
cost at most four inverse spectral rates after the true linear bridge reward.
The shift `m+1` guarantees a genuine unmarked pin. -/
theorem kernel_triple_exp_sum_le {u w : ℝ} (hu : 0 < u) (hw : 0 ≤ w)
    (L R M : ℕ) :
    (∑ l ∈ Finset.range L, ∑ r ∈ Finset.range R, ∑ m ∈ Finset.range M,
      (((m : ℝ) + 1 + w) * Real.exp (-u * ((l : ℝ) + r + (m + 1))))) ≤
        (2 + w) * (1 + 1 / u) ^ 4 := by
  let q := Real.exp (-u)
  let G := 1 / (1 - q)
  have hq0 : 0 ≤ q := Real.exp_nonneg _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hG0 : 0 ≤ G := by positivity
  have hG1 : 1 ≤ G := by
    apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
    linarith
  have hgeom (N : ℕ) : ∑ n ∈ Finset.range N, q ^ n ≤ G := kr_geom_sum_le hq0 hq1 N
  have hgeomM : ∑ m ∈ Finset.range M, ((m : ℝ) + 1 + w) * q ^ m ≤ (2 + w) * G ^ 2 := by
    have he : (∑ m ∈ Finset.range M, ((m : ℝ) + 1 + w) * q ^ m) =
        (∑ m ∈ Finset.range M, (m : ℝ) * q ^ m) + (1 + w) * ∑ m ∈ Finset.range M, q ^ m := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    rw [he]
    have hh := kr_geom_sum_mul_le hq0 hq1 M
    have heG : 1 / (1 - q) ^ 2 = G ^ 2 := by simp [G]
    rw [heG] at hh
    have hh' := mul_le_mul_of_nonneg_left (hgeom M) (show 0 ≤ 1 + w by linarith)
    have hGsq : G ≤ G ^ 2 := by nlinarith
    have hgg := mul_le_mul_of_nonneg_left hGsq (show 0 ≤ 1 + w by linarith)
    nlinarith
  have hexp (l r m : ℕ) : Real.exp (-u * ((l : ℝ) + r + (m + 1))) ≤ q ^ l * q ^ r * q ^ m := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hfirst :
      (∑ l ∈ Finset.range L, ∑ r ∈ Finset.range R, ∑ m ∈ Finset.range M,
        (((m : ℝ) + 1 + w) * Real.exp (-u * ((l : ℝ) + r + (m + 1))))) ≤
      (∑ l ∈ Finset.range L, q ^ l) * (∑ r ∈ Finset.range R, q ^ r) * ((2 + w) * G ^ 2) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro l hl
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro r hr
    calc
      _ ≤ ∑ m ∈ Finset.range M, ((m : ℝ) + 1 + w) * (q ^ l * q ^ r * q ^ m) := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_left (hexp l r m) (by positivity)
      _ = q ^ l * q ^ r * ∑ m ∈ Finset.range M, ((m : ℝ) + 1 + w) * q ^ m := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hgeomM (show 0 ≤ q ^ l * q ^ r by positivity)
        simpa only [mul_assoc] using hh
  have hsecond :
      (∑ l ∈ Finset.range L, q ^ l) * (∑ r ∈ Finset.range R, q ^ r) * ((2 + w) * G ^ 2) ≤
      (2 + w) * G ^ 4 := by
    have hprod := mul_le_mul (hgeom L) (hgeom R) (Finset.sum_nonneg fun _ _ => by positivity) hG0
    have hh := mul_le_mul_of_nonneg_right hprod (show 0 ≤ (2 + w) * G ^ 2 by positivity)
    exact hh.trans_eq (by ring)
  apply (hfirst.trans hsecond).trans
  have hden : G ≤ 1 + 1 / u := kernel_one_div_one_sub_exp_neg_le hu
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hG0 hden 4) (by positivity)

end
end PGM
