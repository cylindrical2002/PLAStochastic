import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # The derivative of the Riemann zeta function at the negative even integers

For `k ≥ 1`,
`ζ'(-2k) = (-1)^k (2k)! ζ(2k+1) / (2 (2π)^(2k))` (DLMF 25.4.2 differentiated at a trivial zero).
The proof differentiates Mathlib's functional equation `riemannZeta_one_sub` at `s = 2k+1`.
There the cosine factor vanishes, so only the derivative of the cosine survives. -/
noncomputable section
open Complex Filter
open scoped Topology Real
namespace BrownianAffine

/-- The Riemann zeta function is real at every integer `n ≥ 2`. -/
theorem riemannZeta_natCast_im {n : ℕ} (hn : 1 < n) : (riemannZeta n).im = 0 := by
  rw [zeta_nat_eq_tsum_of_gt_one hn]
  have h : (fun m : ℕ => 1 / (m : ℂ) ^ n) = fun m : ℕ => (((1 : ℝ) / (m : ℝ) ^ n : ℝ) : ℂ) := by
    funext m
    push_cast
    rfl
  rw [h, ← ofReal_tsum, ofReal_im]

theorem ofReal_re_riemannZeta_natCast {n : ℕ} (hn : 1 < n) :
    (((riemannZeta n).re : ℝ) : ℂ) = riemannZeta n :=
  Complex.ext (by simp) (by simp [riemannZeta_natCast_im hn])

/-- **(T10).** The derivative of `ζ` at a trivial zero `-2k`, `k ≥ 1`. -/
theorem deriv_riemannZeta_neg_two_mul_nat {k : ℕ} (hk : 1 ≤ k) :
    deriv riemannZeta (-2 * k) =
      (-1) ^ k * ((2 * k).factorial : ℂ) * riemannZeta (2 * k + 1) /
        (2 * (2 * π) ^ (2 * k)) := by
  set s₀ : ℂ := 2 * k + 1 with hs₀
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs₀re : s₀.re = 2 * k + 1 := by simp [hs₀]
  have hev : (fun s => riemannZeta (1 - s)) =ᶠ[𝓝 s₀]
      fun s => 2 * (2 * (π : ℂ)) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
    have hmem : s₀ ∈ {s : ℂ | 1 < s.re} := by
      simp only [Set.mem_ofPred_eq, hs₀re]
      linarith
    filter_upwards [hopen.mem_nhds hmem] with s hs
    apply riemannZeta_one_sub
    · intro n hn
      have := congrArg Complex.re hn
      simp only [neg_re, natCast_re] at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro h
      rw [h] at hs
      simp at hs
  have h1s : 1 - s₀ = -2 * k := by rw [hs₀]; ring
  have hne1 : 1 - s₀ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [sub_re, one_re, hs₀re] at this
    linarith
  have hL : HasDerivAt (fun s => riemannZeta (1 - s)) (deriv riemannZeta (1 - s₀) * (-1)) s₀ := by
    have h2 : HasDerivAt (fun s : ℂ => 1 - s) (-1) s₀ := by
      simpa using (hasDerivAt_id s₀).const_sub 1
    exact (differentiableAt_riemannZeta hne1).hasDerivAt.comp s₀ h2
  set A : ℂ → ℂ := fun s => 2 * (2 * (π : ℂ)) ^ (-s) * Gamma s with hA
  have hAd : DifferentiableAt ℂ A s₀ := by
    have hG : DifferentiableAt ℂ Gamma s₀ := by
      apply differentiableAt_Gamma
      intro m hm
      have := congrArg Complex.re hm
      simp only [neg_re, natCast_re, hs₀re] at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hpow : DifferentiableAt ℂ (fun s : ℂ => (2 * (π : ℂ)) ^ (-s)) s₀ :=
      differentiableAt_id.neg.const_cpow (Or.inl (by simp [Real.pi_ne_zero]))
    exact (hpow.const_mul 2).mul hG
  have hC : HasDerivAt (fun s : ℂ => cos (π * s / 2)) (-sin (π * s₀ / 2) * (π / 2)) s₀ := by
    have h2 : HasDerivAt (fun s : ℂ => π * s / 2) (π / 2) s₀ := by
      simpa using ((hasDerivAt_id s₀).const_mul (π : ℂ)).div_const 2
    exact h2.ccos
  have hZ : DifferentiableAt ℂ riemannZeta s₀ := by
    apply differentiableAt_riemannZeta
    intro h
    have := congrArg Complex.re h
    simp only [hs₀re, one_re] at this
    linarith
  have hR := (hAd.hasDerivAt.mul hC).mul hZ.hasDerivAt
  have hR' := hR.congr_of_eventuallyEq hev
  have harg : (π : ℂ) * s₀ / 2 = ((π / 2 + k * π : ℝ) : ℂ) := by
    rw [hs₀]; push_cast; ring
  have hcos : cos (π * s₀ / 2) = 0 := by
    rw [harg, ← ofReal_cos, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two]
    simp
  have hsin : sin (π * s₀ / 2) = (-1) ^ k := by
    rw [harg, ← ofReal_sin, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two]
    simp
  have hAval : A s₀ = 2 * ((2 * k).factorial : ℂ) / (2 * π) ^ (2 * k + 1) := by
    have hcast : s₀ = ((2 * k + 1 : ℕ) : ℂ) := by rw [hs₀]; push_cast; ring
    simp only [hA]
    rw [cpow_neg, hcast, cpow_natCast]
    have hG : Gamma ((2 * k + 1 : ℕ) : ℂ) = ((2 * k).factorial : ℂ) := by
      rw [Nat.cast_succ, Gamma_nat_eq_factorial]
    rw [hG]
    ring
  have huniq := hL.unique hR'
  rw [h1s] at huniq
  simp only [Pi.mul_apply, hcos, hsin, mul_zero, zero_mul, add_zero, zero_add] at huniq
  rw [hAval] at huniq
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hzeta : riemannZeta s₀ = riemannZeta (2 * k + 1) := by rw [hs₀]
  rw [hzeta] at huniq
  have hdk : deriv riemannZeta (-2 * k) =
      -(2 * ((2 * k).factorial : ℂ) / (2 * π) ^ (2 * k + 1) * (-(-1) ^ k * (π / 2)) *
        riemannZeta (2 * k + 1)) := by
    linear_combination -huniq
  rw [hdk]
  field_simp
  ring

/-- **(T10), real form.** The value `ζ'(-2k)` is the real number
`(-1)^k (2k)!/2^(2k+1) · ζ(2k+1)/π^(2k)`. -/
theorem deriv_riemannZeta_neg_two_mul_nat_eq_ofReal {k : ℕ} (hk : 1 ≤ k) :
    deriv riemannZeta (-2 * k) =
      (((-1) ^ k * ((2 * k).factorial : ℝ) / 2 ^ (2 * k + 1) *
        (riemannZeta (2 * k + 1)).re / π ^ (2 * k) : ℝ) : ℂ) := by
  have hz : (((riemannZeta (2 * k + 1)).re : ℝ) : ℂ) = riemannZeta (2 * k + 1) := by
    have := ofReal_re_riemannZeta_natCast (n := 2 * k + 1) (by omega)
    push_cast at this
    exact this
  rw [deriv_riemannZeta_neg_two_mul_nat hk]
  push_cast
  rw [hz]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-- The real part of `ζ'(-2k)`. -/
theorem re_deriv_riemannZeta_neg_two_mul_nat {k : ℕ} (hk : 1 ≤ k) :
    (deriv riemannZeta (-2 * k)).re =
      (-1) ^ k * ((2 * k).factorial : ℝ) / 2 ^ (2 * k + 1) *
        (riemannZeta (2 * k + 1)).re / π ^ (2 * k) := by
  rw [deriv_riemannZeta_neg_two_mul_nat_eq_ofReal hk, ofReal_re]

/-- `ζ'(-2k)` is real. -/
theorem im_deriv_riemannZeta_neg_two_mul_nat {k : ℕ} (hk : 1 ≤ k) :
    (deriv riemannZeta (-2 * k)).im = 0 := by
  rw [deriv_riemannZeta_neg_two_mul_nat_eq_ofReal hk, ofReal_im]

end BrownianAffine
