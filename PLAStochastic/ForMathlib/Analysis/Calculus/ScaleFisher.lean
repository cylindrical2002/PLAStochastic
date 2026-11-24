import PLAStochastic.ForMathlib.Analysis.Calculus.MellinOperator
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# First-order scale Fisher energy from absolute derivative bounds

For a nonnegative `C²` function `f` vanishing on `(-∞, 0]` with `f + |f''| ≤ E e^{-κ|x|}`,
the scale Fisher energy `∫ (mellinOp f)² / f` is finite with a bound depending only on
`E, κ` (`research/2026-09-29-ceps-full-expansion/output-closure.md` (O2)–(O3)); no lower
bound on `f` is used. Division by zero is zero, so the integrand vanishes where `f = 0`.

* `taylor_two_le`: one-sided Taylor bound `g(x + σt) ≤ g(x) + σ t g'(x) + M t²`.
* `sq_deriv_le_of_nonneg` ((O3)): a function nonnegative on `[x - h, x + h]` with
  `|g''| ≤ M` there has `g'(x)² ≤ 4 M g(x) + 4 g(x)²/h²`.
* `sq_mellinOp_div_le`: `(mellinOp f)²/f ≤ E (34 + 16x²) e^{-κx/2}` for `x > 0`.
* `integral_mellinOp_eq_zero`: `∫ mellinOp f = 0`, since `mellinOp f = (x f)'`.
-/

noncomputable section

open Set Filter Topology MeasureTheory

namespace PGM

/-- One-sided second-order Taylor bound along `x + σ t`, `|σ| = 1`. -/
theorem taylor_two_le {g g1 g2 : ℝ → ℝ} {x h0 M : ℝ}
    (hg : ∀ y, HasDerivAt g (g1 y) y) (hg1 : ∀ y, HasDerivAt g1 (g2 y) y)
    (hbound : ∀ y ∈ Icc (x - h0) (x + h0), |g2 y| ≤ M) {σ t : ℝ} (hσ : |σ| = 1)
    (ht : 0 ≤ t) (hth : t ≤ h0) :
    g (x + σ * t) ≤ g x + σ * t * g1 x + M * t ^ 2 := by
  rcases ht.eq_or_lt with rfl | htpos
  · simp
  have hmem : ∀ s, 0 ≤ s → s ≤ t → x + σ * s ∈ Icc (x - h0) (x + h0) := by
    intro s hs0 hst
    have : |σ * s| ≤ h0 := by rw [abs_mul, hσ, one_mul, abs_of_nonneg hs0]; linarith
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]
  have hψ : ∀ s, HasDerivAt (fun s => g (x + σ * s)) (g1 (x + σ * s) * σ) s := by
    intro s
    have h1 : HasDerivAt (fun s => x + σ * s) σ s := by
      simpa using (hasDerivAt_id s).const_mul σ |>.const_add x
    exact (hg (x + σ * s)).comp s h1
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun s => g (x + σ * s))
    (fun s => g1 (x + σ * s) * σ) htpos
    (fun s _ => (hψ s).continuousAt.continuousWithinAt) (fun s _ => hψ s)
  simp only [mul_zero, add_zero] at hξeq
  have hdiff : g (x + σ * t) - g x = t * (σ * g1 (x + σ * ξ)) := by
    rw [sub_zero, eq_div_iff htpos.ne'] at hξeq
    linear_combination (-1 : ℝ) * hξeq
  have hconv : Convex ℝ (Icc (x - h0) (x + h0)) := convex_Icc _ _
  have hx0 : x ∈ Icc (x - h0) (x + h0) := by simpa using hmem 0 le_rfl htpos.le
  have hlip : |g1 (x + σ * ξ) - g1 x| ≤ M * |σ * ξ| := by
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _ => (hg1 y).hasDerivWithinAt) (fun y hy => by
        rw [Real.norm_eq_abs]; exact hbound y hy) hx0 (hmem ξ hξ.1.le hξ.2.le)
    simpa [Real.norm_eq_abs] using this
  have hσξ : |σ * ξ| = ξ := by rw [abs_mul, hσ, one_mul, abs_of_pos hξ.1]
  rw [hσξ] at hlip
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound x ⟨by linarith, by linarith⟩)
  have hkey : σ * g1 (x + σ * ξ) ≤ σ * g1 x + M * t := by
    have h1 : σ * (g1 (x + σ * ξ) - g1 x) ≤ |σ * (g1 (x + σ * ξ) - g1 x)| := le_abs_self _
    rw [abs_mul, hσ, one_mul] at h1
    have h2 : M * ξ ≤ M * t := mul_le_mul_of_nonneg_left hξ.2.le hM
    nlinarith
  have : t * (σ * g1 (x + σ * ξ)) ≤ t * (σ * g1 x + M * t) :=
    mul_le_mul_of_nonneg_left hkey htpos.le
  nlinarith

/-- **Derivative bound for nonnegative functions** (`output-closure.md` (O3)). -/
theorem sq_deriv_le_of_nonneg {g g1 g2 : ℝ → ℝ} {x h0 M : ℝ} (hh0 : 0 < h0)
    (hg : ∀ y, HasDerivAt g (g1 y) y) (hg1 : ∀ y, HasDerivAt g1 (g2 y) y)
    (hpos : ∀ y ∈ Icc (x - h0) (x + h0), 0 ≤ g y)
    (hbound : ∀ y ∈ Icc (x - h0) (x + h0), |g2 y| ≤ M) :
    g1 x ^ 2 ≤ 4 * M * g x + 4 * g x ^ 2 / h0 ^ 2 := by
  have hxmem : x ∈ Icc (x - h0) (x + h0) := ⟨by linarith, by linarith⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound x hxmem)
  have hG : 0 ≤ g x := hpos x hxmem
  set a := |g1 x| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  set σ : ℝ := if 0 ≤ g1 x then -1 else 1 with hσdef
  have hσ : |σ| = 1 := by rw [hσdef]; split_ifs <;> simp
  have hσg : σ * g1 x = -a := by
    rw [hσdef, ha]
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.mp h)]; ring
  have hstep : ∀ t, 0 ≤ t → t ≤ h0 → t * a ≤ g x + M * t ^ 2 := by
    intro t ht0 hth
    have h1 := taylor_two_le hg hg1 hbound hσ ht0 hth
    have hmem : x + σ * t ∈ Icc (x - h0) (x + h0) := by
      have : |σ * t| ≤ h0 := by rw [abs_mul, hσ, one_mul, abs_of_nonneg ht0]; exact hth
      rw [abs_le] at this
      constructor <;> linarith [this.1, this.2]
    have h2 := hpos _ hmem
    have h3 : σ * t * g1 x = -(t * a) := by rw [mul_comm σ t, mul_assoc, hσg]; ring
    linarith
  have hsq : g1 x ^ 2 = a ^ 2 := by rw [ha, sq_abs]
  rw [hsq]
  have hR1 : 0 ≤ 4 * M * g x := by positivity
  have hR2 : 0 ≤ 4 * g x ^ 2 / h0 ^ 2 := by positivity
  by_cases hcase : 2 * M * h0 < a
  · have h1 := hstep h0 hh0.le le_rfl
    have h2 : M * h0 ^ 2 < a * h0 / 2 := by nlinarith
    have h3 : a * h0 < 2 * g x := by nlinarith
    have h4 : a < 2 * g x / h0 := by rw [lt_div_iff₀ hh0]; linarith
    have h5 : a ^ 2 ≤ (2 * g x / h0) ^ 2 := pow_le_pow_left₀ ha0 h4.le 2
    have h6 : (2 * g x / h0) ^ 2 = 4 * g x ^ 2 / h0 ^ 2 := by ring
    linarith
  · push Not at hcase
    rcases hM.eq_or_lt with hM0 | hMpos
    · rw [← hM0] at hcase
      have : a = 0 := le_antisymm (by linarith) ha0
      rw [this]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      linarith
    · have ht0 : 0 ≤ a / (2 * M) := by positivity
      have hth : a / (2 * M) ≤ h0 := by rw [div_le_iff₀ (by positivity)]; linarith
      have h1 := hstep _ ht0 hth
      have e1 : a / (2 * M) * a = a ^ 2 / (2 * M) := by ring
      have e2 : M * (a / (2 * M)) ^ 2 = a ^ 2 / (4 * M) := by field_simp; ring
      rw [e1, e2] at h1
      have h2 : a ^ 2 / (4 * M) ≤ g x := by
        have : a ^ 2 / (2 * M) - a ^ 2 / (4 * M) = a ^ 2 / (4 * M) := by field_simp; ring
        linarith
      have h3 : a ^ 2 ≤ 4 * M * g x := by
        rw [div_le_iff₀ (by positivity)] at h2
        linarith
      linarith

/-- **Pointwise scale Fisher bound** (`output-closure.md` (O2)) for `x > 0`. -/
theorem sq_mellinOp_div_le {f : ℝ → ℝ} {E κ : ℝ} (hκ : 0 < κ) (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x, 0 ≤ f x) (henv0 : ∀ x, f x ≤ E * Real.exp (-κ * |x|))
    (henv2 : ∀ x, |deriv (deriv f) x| ≤ E * Real.exp (-κ * |x|)) {x : ℝ} (hx : 0 < x) :
    mellinOp f x ^ 2 / f x ≤ E * ((34 + 16 * x ^ 2) * Real.exp (-(κ / 2) * x)) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (deriv f) := by
    have h1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
    exact h1.differentiable (by norm_num)
  rcases (hpos x).eq_or_lt with hfx | hfx
  · rw [← hfx, div_zero]
    have hE : 0 ≤ E := by
      have := henv0 x
      have h' : 0 ≤ E * Real.exp (-κ * |x|) := (hpos x).trans this
      exact nonneg_of_mul_nonneg_left h' (Real.exp_pos _)
    positivity
  set h0 : ℝ := min (x / 2) 1 with hh0def
  have hh0 : 0 < h0 := lt_min (by linarith) one_pos
  set M : ℝ := E * Real.exp (-(κ / 2) * x) with hMdef
  have hbound : ∀ y ∈ Icc (x - h0) (x + h0), |deriv (deriv f) y| ≤ M := by
    intro y hy
    have hy1 : x / 2 ≤ y := by
      have : h0 ≤ x / 2 := min_le_left _ _
      linarith [hy.1]
    have hy0 : 0 < y := by linarith
    refine (henv2 y).trans ?_
    have hE : 0 ≤ E := by
      have h' : 0 ≤ E * Real.exp (-κ * |y|) := (abs_nonneg _).trans (henv2 y)
      exact nonneg_of_mul_nonneg_left h' (Real.exp_pos _)
    rw [hMdef, abs_of_pos hy0]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hE
  have hsq := sq_deriv_le_of_nonneg (g := f) (g1 := deriv f) (g2 := deriv (deriv f)) hh0
    (fun y => (hd y).hasDerivAt) (fun y => (hd1 y).hasDerivAt) (fun y _ => hpos y) hbound
  have hE : 0 ≤ E := by
    have h' : 0 ≤ E * Real.exp (-κ * |x|) := (hpos x).trans (henv0 x)
    exact nonneg_of_mul_nonneg_left h' (Real.exp_pos _)
  have hfx' : f x ≤ E * Real.exp (-(κ / 2) * x) := by
    refine (henv0 x).trans ?_
    rw [abs_of_pos hx]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hE
  have hxh : x ^ 2 / h0 ^ 2 ≤ 4 + x ^ 2 := by
    rcases le_total (x / 2) 1 with hle | hle
    · have : h0 = x / 2 := min_eq_left hle
      rw [this]
      have : x ^ 2 / (x / 2) ^ 2 = 4 := by field_simp; ring
      rw [this]; nlinarith
    · have : h0 = 1 := min_eq_right hle
      rw [this]; simp
  set d := deriv f x with hd_def
  have hL : mellinOp f x = f x + x * d := rfl
  rw [hL, div_le_iff₀ hfx]
  -- `(f + x d)² ≤ 2 f² + 2 x² d²` and `d² ≤ 4 M f + 4 f²/h0²`
  have h1 : (f x + x * d) ^ 2 ≤ 2 * f x ^ 2 + 2 * x ^ 2 * d ^ 2 := by
    nlinarith [sq_nonneg (f x - x * d)]
  have h2 : x ^ 2 * d ^ 2 ≤ x ^ 2 * (4 * M * f x) + 4 * f x ^ 2 * (x ^ 2 / h0 ^ 2) := by
    have := mul_le_mul_of_nonneg_left hsq (sq_nonneg x)
    have e : x ^ 2 * (4 * M * f x + 4 * f x ^ 2 / h0 ^ 2) =
        x ^ 2 * (4 * M * f x) + 4 * f x ^ 2 * (x ^ 2 / h0 ^ 2) := by ring
    linarith
  have h3 : 4 * f x ^ 2 * (x ^ 2 / h0 ^ 2) ≤ 4 * f x ^ 2 * (4 + x ^ 2) :=
    mul_le_mul_of_nonneg_left hxh (by positivity)
  have hfM : f x * f x ≤ f x * M := mul_le_mul_of_nonneg_left hfx' hfx.le
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have h4 : f x ^ 2 * (34 + 8 * x ^ 2) ≤ f x * M * (34 + 8 * x ^ 2) := by
    have : f x ^ 2 = f x * f x := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hfM (by positivity)
  have hMe : M = E * Real.exp (-(κ / 2) * x) := rfl
  calc (f x + x * d) ^ 2 ≤ 2 * f x ^ 2 + 2 * x ^ 2 * d ^ 2 := h1
    _ ≤ 2 * f x ^ 2 + 2 * (x ^ 2 * (4 * M * f x) + 4 * f x ^ 2 * (4 + x ^ 2)) := by nlinarith
    _ = f x ^ 2 * (34 + 8 * x ^ 2) + 8 * x ^ 2 * M * f x := by ring
    _ ≤ f x * M * (34 + 8 * x ^ 2) + 8 * x ^ 2 * M * f x := by linarith
    _ = E * ((34 + 16 * x ^ 2) * Real.exp (-(κ / 2) * x)) * f x := by rw [hMe]; ring

/-- `∫ mellinOp f = 0`, since `mellinOp f = (x f)'`. -/
theorem integral_mellinOp_eq_zero {f : ℝ → ℝ} (hd : Differentiable ℝ f)
    (hint : Integrable fun x => x * f x) (hint' : Integrable (mellinOp f)) :
    ∫ x, mellinOp f x = 0 := by
  refine integral_eq_zero_of_hasDerivAt_of_integrable (f := fun x => x * f x) (fun x => ?_)
    hint' hint
  have := (hasDerivAt_id' x).fun_mul (hd x).hasDerivAt
  rw [mellinOp_apply]
  simpa using this

end PGM
