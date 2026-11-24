import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-! # Reciprocal hyperbolic sine moments from a positive geometric expansion -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem hasSum_reciprocal_sinh {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => 2 * Real.exp (-((2 : ℝ) * n + 1) * x)) (1 / Real.sinh x) := by
  have hr : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := (hasSum_geometric_of_lt_one (Real.exp_nonneg (-2 * x)) hr).mul_left
    (2 * Real.exp (-x))
  convert! h using 1
  · funext n
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  · rw [Real.sinh_eq, Real.exp_neg,
      show -2 * x = -(2 * x) by ring, Real.exp_neg, show 2 * x = x + x by ring, Real.exp_add]
    have he : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
    have hn : Real.exp x ^ 2 - 1 ≠ 0 := by
      have hh := Real.one_lt_exp_iff.mpr hx
      nlinarith
    field_simp

theorem summable_odd_reciprocal_pow {k : ℕ} (hk : 1 < k) :
    Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ k) := by
  have h := (Real.summable_one_div_nat_pow.mpr hk).comp_injective
    (i := fun n : ℕ => 2 * n + 1) (by intro a b hab; dsimp only at hab; omega)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h

theorem hasSum_integral_pow_div_sinh {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 0 < k) :
    HasSum (fun n : ℕ => 2 * (k.factorial : ℝ) / (((2 : ℝ) * n + 1) * c) ^ (k + 1))
      (∫ y in Ioi 0, y ^ k / Real.sinh (c * y)) := by
  have hsum : Summable (fun n : ℕ => ‖(2 : ℂ)‖ /
      (((2 : ℝ) * n + 1) * c) ^ (((k + 1 : ℕ) : ℂ).re)) := by
    simp only [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, Complex.natCast_re, Real.rpow_natCast, mul_pow]
    convert! (summable_odd_reciprocal_pow (by omega : 1 < k + 1)).mul_left
      (2 / c ^ (k + 1)) using 1
    funext n
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum
      (fun n : ℕ => (2 : ℂ) * (Real.exp (-(((2 : ℝ) * n + 1) * c) * t) : ℂ))
      ((1 / Real.sinh (c * t) : ℝ) : ℂ) := by
    intro t ht
    have h := Complex.hasSum_ofReal.mpr (hasSum_reciprocal_sinh (mul_pos hc ht))
    convert! h using 1
    funext n
    push_cast
    congr 2
    ring
  have h := hasSum_mellin (a := fun _ : ℕ => (2 : ℂ))
    (p := fun n => ((2 : ℝ) * n + 1) * c)
    (F := fun t => ((1 / Real.sinh (c * t) : ℝ) : ℂ))
    (s := ((k + 1 : ℕ) : ℂ))
    (fun _ => Or.inr (by positivity)) (by simp; positivity) hF hsum
  have hg : Complex.Gamma ((k + 1 : ℕ) : ℂ) = (k.factorial : ℂ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.Gamma_nat_eq_factorial k
  have he : mellin (fun t => ((1 / Real.sinh (c * t) : ℝ) : ℂ)) ((k + 1 : ℕ) : ℂ) =
      ((∫ y in Ioi 0, y ^ k / Real.sinh (c * y) : ℝ) : ℂ) := by
    unfold mellin
    rw [← integral_complex_ofReal (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun y : ℝ => y ^ k / Real.sinh (c * y))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    dsimp only
    rw [show ((k + 1 : ℕ) : ℂ) - 1 = (k : ℂ) by push_cast; ring, Complex.cpow_natCast]
    simp [smul_eq_mul, div_eq_mul_inv]
  rw [he] at h
  apply Complex.hasSum_ofReal.mp
  convert! h using 1
  funext n
  rw [hg, Complex.cpow_natCast]
  push_cast
  ring

theorem tsum_reciprocal_pow_eq_zeta {k : ℕ} (hk : 1 < k) :
    (∑' n : ℕ, 1 / (n : ℝ) ^ k) = (riemannZeta (k : ℂ)).re := by
  have h : ((∑' n : ℕ, 1 / (n : ℝ) ^ k : ℝ) : ℂ) = riemannZeta (k : ℂ) := by
    rw [Complex.ofReal_tsum, zeta_nat_eq_tsum_of_gt_one hk]
    congr 1
    funext n
    push_cast
    rfl
  exact_mod_cast congrArg Complex.re h

theorem tsum_odd_reciprocal_pow_eq_zeta {k : ℕ} (hk : 1 < k) :
    (∑' n : ℕ, 1 / (2 * (n : ℝ) + 1) ^ k) =
      (1 - 1 / (2 : ℝ) ^ k) * (riemannZeta (k : ℂ)).re := by
  have hs := Real.summable_one_div_nat_pow.mpr hk
  have hev := hs.comp_injective (i := fun n : ℕ => 2 * n)
    (by intro a b hab; dsimp only at hab; omega)
  have hod := hs.comp_injective (i := fun n : ℕ => 2 * n + 1)
    (by intro a b hab; dsimp only at hab; omega)
  have h := tsum_even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ k) hev hod
  have he : (∑' n : ℕ, 1 / (2 * (n : ℝ)) ^ k) =
      (1 / (2 : ℝ) ^ k) * (∑' n : ℕ, 1 / (n : ℝ) ^ k) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  rw [he, tsum_reciprocal_pow_eq_zeta hk] at h
  linarith

theorem integral_pow_div_sinh_eq_zeta {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 0 < k) :
    (∫ y in Ioi 0, y ^ k / Real.sinh (c * y)) =
      2 * (k.factorial : ℝ) / c ^ (k + 1) *
        (1 - 1 / (2 : ℝ) ^ (k + 1)) * (riemannZeta ((k + 1 : ℕ) : ℂ)).re := by
  calc
    _ = ∑' n : ℕ, 2 * (k.factorial : ℝ) / (((2 : ℝ) * n + 1) * c) ^ (k + 1) :=
      (hasSum_integral_pow_div_sinh hc hk).tsum_eq.symm
    _ = (2 * (k.factorial : ℝ) / c ^ (k + 1)) *
        (∑' n : ℕ, 1 / (2 * (n : ℝ) + 1) ^ (k + 1)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [tsum_odd_reciprocal_pow_eq_zeta (by omega : 1 < k + 1)]; ring

/-- The exact hyperbolic integral appearing in the manuscript's odd-zeta formula. -/
theorem integral_even_pow_div_sinh_pi {j : ℕ} (hj : 0 < j) :
    (∫ y in Ioi 0, y ^ (2 * j) / Real.sinh (Real.pi * y / 2)) =
      2 * ((2 * j).factorial : ℝ) * ((2 : ℝ) ^ (2 * j + 1) - 1) /
        Real.pi ^ (2 * j + 1) * (riemannZeta ((2 * j + 1 : ℕ) : ℂ)).re := by
  have h := integral_pow_div_sinh_eq_zeta (c := Real.pi / 2) (by positivity)
    (k := 2 * j) (by omega)
  simp_rw [div_mul_eq_mul_div] at h
  rw [h, div_pow]
  field_simp

theorem integrableOn_pow_div_sinh {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 0 < k) :
    IntegrableOn (fun y => y ^ k / Real.sinh (c * y)) (Ioi 0) := by
  have h := hasSum_integral_pow_div_sinh hc hk
  have hp : 0 < ∑' n : ℕ, 2 * (k.factorial : ℝ) /
      (((2 : ℝ) * n + 1) * c) ^ (k + 1) :=
    h.summable.tsum_pos (fun _ => by positivity) 0 (by positivity)
  rw [h.tsum_eq] at hp
  by_contra hi
  rw [integral_undef hi] at hp
  exact (lt_irrefl 0) hp

theorem integrableOn_even_pow_div_sinh_pi {j : ℕ} (hj : 0 < j) :
    IntegrableOn (fun y => y ^ (2 * j) / Real.sinh (Real.pi * y / 2)) (Ioi 0) := by
  simpa only [div_mul_eq_mul_div] using
    integrableOn_pow_div_sinh (c := Real.pi / 2) (by positivity) (k := 2 * j) (by omega)

end BrownianAffine
