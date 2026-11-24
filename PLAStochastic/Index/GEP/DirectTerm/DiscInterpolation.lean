import PLAStochastic.Index.GEP.DirectTerm.Defs
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# WP4 leaf `DirectTerm`: analytic interpolation on a disc (`DiscInterp`)

`discInterp : DiscInterp` with the absolute constant `K = 432`.  The route (PD (5), `j = 1`) uses the
three lines theorem through `cosh`, then a Cauchy estimate; no Chebyshev series.

1. With `h = R / 16`, the map `ζ ↦ h + h cosh ζ` sends the closed strip `0 ≤ Re ζ ≤ 1` into
   `ball 0 R` (`‖cosh ζ‖ ≤ (e + 1) / 2 ≤ 2`) and the line `Re ζ = 0` onto the segment `[0, R/8]`
   (`cosh (i y) = cos y`).  Hadamard's three lines theorem for `g ζ = f (h + h cosh ζ)` gives
   `‖g ζ‖ ≤ δ ^ (1 - Re ζ) * M ^ Re ζ` (`discInterp_threeLines`).
2. Every `z` with `‖z‖ ≤ ρ² h`, `0 ≤ ρ ≤ 1`, is `h + h cosh ζ` with `0 ≤ Re ζ ≤ 3ρ`: for
   `u = z / h - 1` and `v² = u² - 1`, the roots `u ± v` of `w² - 2uw + 1` have product one; the
   one with `‖w‖ ≥ 1` gives `ζ = log w`, and `Re ζ = log ‖w‖ ≤ ‖u‖ + ‖v‖ - 1 ≤ ρ² + 2ρ`
   (`discInterp_cosh_preimage`).
3. For `L = log (M / δ)` and `ρ = 1 / (3 (1 + L))`, the exponent obeys `Re ζ · L ≤ 1`, so
   `δ ^ (1 - Re ζ) M ^ Re ζ = δ exp (Re ζ · L) ≤ 3 δ` on the circle `‖z‖ = s = ρ² R / 16`
   (`discInterp_rpow_le`).  Cauchy's estimate gives
   `‖f'(0)‖ ≤ 3 δ / s = 432 δ (1 + L)² / R`.
-/

namespace PGM

noncomputable section

open Set Metric

/-- `‖cosh ζ‖ ≤ 2` on the closed strip `0 ≤ Re ζ ≤ 1`. -/
theorem discInterp_norm_cosh_le_two {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    ‖Complex.cosh ζ‖ ≤ 2 := by
  have h2 : ‖(2 : ℂ) * Complex.cosh ζ‖ ≤ 4 := by
    rw [Complex.two_cosh]
    calc ‖Complex.exp ζ + Complex.exp (-ζ)‖ ≤ ‖Complex.exp ζ‖ + ‖Complex.exp (-ζ)‖ :=
          norm_add_le _ _
      _ = Real.exp ζ.re + Real.exp (-ζ.re) := by
          rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]
      _ ≤ 3 + 1 := by
          gcongr
          · exact (Real.exp_le_exp.2 h1).trans Real.exp_one_lt_three.le
          · exact Real.exp_le_one_iff.2 (by linarith)
      _ = 4 := by norm_num
  rw [norm_mul] at h2
  norm_num at h2
  linarith

/-- The interpolated bound is at most `3 δ` once the exponent `x log (M / δ)` is at most one. -/
theorem discInterp_rpow_le {δ M x : ℝ} (hδ : 0 < δ) (hδM : δ ≤ M)
    (hx : x * Real.log (M / δ) ≤ 1) : δ ^ (1 - x) * M ^ x ≤ 3 * δ := by
  have hM : 0 < M := hδ.trans_le hδM
  rw [Real.log_div hM.ne' hδ.ne'] at hx
  rw [Real.rpow_def_of_pos hδ, Real.rpow_def_of_pos hM, ← Real.exp_add]
  have : Real.log δ * (1 - x) + Real.log M * x = Real.log δ + x * (Real.log M - Real.log δ) := by
    ring
  rw [this, Real.exp_add, Real.exp_log hδ]
  have : Real.exp (x * (Real.log M - Real.log δ)) ≤ 3 :=
    (Real.exp_le_exp.2 hx).trans Real.exp_one_lt_three.le
  nlinarith

/-- **Three lines through `cosh`.**  For `0 < h ≤ R / 16` the function `ζ ↦ f (h + h cosh ζ)` is
bounded by `δ ^ (1 - Re ζ) * M ^ Re ζ` on the closed strip `0 ≤ Re ζ ≤ 1`. -/
theorem discInterp_threeLines (f : ℂ → ℂ) {R M δ h : ℝ} (hh : 0 < h) (hhR : h ≤ R / 16)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hM : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M)
    (hδ : ∀ t : ℝ, 0 ≤ t → t ≤ R / 8 → ‖f t‖ ≤ δ) {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    ‖f ((h : ℂ) + h * Complex.cosh ζ)‖ ≤ δ ^ (1 - ζ.re) * M ^ ζ.re := by
  set g : ℂ → ℂ := fun ζ => f ((h : ℂ) + h * Complex.cosh ζ) with hg
  have hmem : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → (h : ℂ) + h * Complex.cosh ζ ∈ ball (0 : ℂ) R := by
    intro ζ h0 h1
    rw [mem_ball_zero_iff]
    calc ‖(h : ℂ) + h * Complex.cosh ζ‖ ≤ ‖(h : ℂ)‖ + ‖(h : ℂ)‖ * ‖Complex.cosh ζ‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ h + h * 2 := by
          rw [Complex.norm_real, Real.norm_of_nonneg hh.le]
          gcongr
          exact discInterp_norm_cosh_le_two h0 h1
      _ < R := by linarith
  have hdiff : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → DifferentiableAt ℂ g ζ := by
    intro ζ h0 h1
    have hfd : DifferentiableAt ℂ f ((h : ℂ) + h * Complex.cosh ζ) :=
      hf.differentiableAt (isOpen_ball.mem_nhds (hmem ζ h0 h1))
    exact hfd.comp ζ ((differentiableAt_const _).add
      ((differentiableAt_const _).mul Complex.differentiable_cosh.differentiableAt))
  have hd : DiffContOnCl ℂ g (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    apply DifferentiableOn.diffContOnCl
    intro ζ hζ
    have hsub : Complex.HadamardThreeLines.verticalStrip 0 1 ⊆
        Complex.HadamardThreeLines.verticalClosedStrip 0 1 := fun x hx => ⟨hx.1.le, hx.2.le⟩
    have hc := closure_minimal hsub (isClosed_Icc.preimage Complex.continuous_re) hζ
    exact (hdiff ζ hc.1 hc.2).differentiableWithinAt
  have hB : BddAbove ((norm ∘ g) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨ζ, hζ, rfl⟩
    exact hM _ (hmem ζ hζ.1 hζ.2)
  have ha : ∀ z ∈ Complex.re ⁻¹' {0}, ‖g z‖ ≤ δ := by
    intro z hz
    have hz0 : z.re = 0 := hz
    have hzI : z = (z.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hz0]
    have hpt : (h : ℂ) + h * Complex.cosh z = ((h + h * Real.cos z.im : ℝ) : ℂ) := by
      rw [hzI, Complex.cosh_mul_I]
      push_cast
      simp
    simp only [hg, hpt]
    apply hδ
    · nlinarith [Real.neg_one_le_cos z.im]
    · nlinarith [Real.cos_le_one z.im]
  have hb : ∀ z ∈ Complex.re ⁻¹' {1}, ‖g z‖ ≤ M := by
    intro z hz
    have hz1 : z.re = 1 := hz
    exact hM _ (hmem z (by rw [hz1]; norm_num) hz1.le)
  exact Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' g ⟨h0, h1⟩ hd hB
    ha hb

/-- **Inverting `h + h cosh` near `0`.**  If `‖z‖ ≤ ρ² h` with `0 ≤ ρ ≤ 1`, then
`z = h + h cosh ζ` for some `ζ` with `0 ≤ Re ζ ≤ 3ρ`. -/
theorem discInterp_cosh_preimage {h ρ : ℝ} (hh : 0 < h) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {z : ℂ}
    (hz : ‖z‖ ≤ ρ ^ 2 * h) :
    ∃ ζ : ℂ, 0 ≤ ζ.re ∧ ζ.re ≤ 3 * ρ ∧ (h : ℂ) + h * Complex.cosh ζ = z := by
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hh.ne'
  set u : ℂ := z / h - 1 with hu
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (u ^ 2 - 1) two_pos
  have hprod : (u + v) * (u - v) = 1 := by linear_combination -hv
  have hu1 : ‖u + 1‖ ≤ ρ ^ 2 := by
    rw [hu, sub_add_cancel, norm_div, Complex.norm_real, Real.norm_of_nonneg hh.le,
      div_le_iff₀ hh]
    exact hz
  have hum1 : ‖u - 1‖ ≤ 2 + ρ ^ 2 := by
    calc ‖u - 1‖ = ‖(u + 1) - 2‖ := by ring_nf
      _ ≤ ‖u + 1‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 + ρ ^ 2 := by rw [Complex.norm_two]; linarith
  have hun : ‖u‖ ≤ 1 + ρ ^ 2 := by
    calc ‖u‖ = ‖(u + 1) - 1‖ := by ring_nf
      _ ≤ ‖u + 1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + ρ ^ 2 := by rw [norm_one]; linarith
  have hvsq : ‖v‖ ^ 2 ≤ 3 * ρ ^ 2 := by
    rw [← norm_pow, hv, show u ^ 2 - 1 = (u - 1) * (u + 1) by ring, norm_mul]
    calc ‖u - 1‖ * ‖u + 1‖ ≤ (2 + ρ ^ 2) * ρ ^ 2 :=
          mul_le_mul hum1 hu1 (norm_nonneg _) (by positivity)
      _ ≤ 3 * ρ ^ 2 := by
          have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith
          nlinarith [sq_nonneg ρ]
  have hv2 : ‖v‖ ≤ 2 * ρ := by nlinarith [norm_nonneg v]
  have key : ∃ w w' : ℂ, w * w' = 1 ∧ w + w' = 2 * u ∧ 1 ≤ ‖w‖ ∧ ‖w‖ ≤ ‖u‖ + ‖v‖ := by
    by_cases h1 : 1 ≤ ‖u + v‖
    · exact ⟨u + v, u - v, hprod, by ring, h1, norm_add_le _ _⟩
    · refine ⟨u - v, u + v, by rw [mul_comm]; exact hprod, by ring, ?_, norm_sub_le _ _⟩
      have hn : ‖u + v‖ * ‖u - v‖ = 1 := by rw [← norm_mul, hprod, norm_one]
      have h1' := not_le.mp h1
      nlinarith [norm_nonneg (u + v), norm_nonneg (u - v)]
  obtain ⟨w, w', hww, hsum, hw1, hw2⟩ := key
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hww
  have hw' : w⁻¹ = w' := inv_eq_of_mul_eq_one_right hww
  refine ⟨Complex.log w, ?_, ?_, ?_⟩
  · rw [Complex.log_re]
    exact Real.log_nonneg hw1
  · rw [Complex.log_re]
    have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hw1)
    nlinarith
  · have h2c := Complex.two_cosh (Complex.log w)
    rw [Complex.exp_neg, Complex.exp_log hw0, hw'] at h2c
    have hc : Complex.cosh (Complex.log w) = u := by linear_combination (h2c + hsum) / 2
    rw [hc, hu]
    field_simp
    ring

/-- **(DiscInterp)** holds with `K = 432`: three lines through `cosh` bound `f` by `3 δ` on the
circle of radius `R / (144 (1 + log (M/δ))²)`, and Cauchy's estimate on that circle bounds
`f'(0)`. -/
theorem discInterp : DiscInterp := by
  refine ⟨432, by norm_num, ?_⟩
  intro f R M δ hR hδ hδM hf hM hseg
  set L := Real.log (M / δ) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_div hδ).2 hδM)
  set ρ : ℝ := 1 / (3 * (1 + L)) with hρ
  have hρ0 : 0 < ρ := by positivity
  have h3ρ : 3 * ρ * (1 + L) = 1 := by rw [hρ]; field_simp
  have h3ρ1 : 3 * ρ ≤ 1 := by nlinarith
  have hρ1 : ρ ≤ 1 := by linarith
  set s : ℝ := ρ ^ 2 * (R / 16) with hs
  have hs0 : 0 < s := by positivity
  have hsR : s < R := by
    have : ρ ^ 2 ≤ 1 := by nlinarith
    rw [hs]; nlinarith
  have hcirc : ∀ z ∈ sphere (0 : ℂ) s, ‖f z‖ ≤ 3 * δ := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    obtain ⟨ζ, h0, h1, hζ⟩ :=
      discInterp_cosh_preimage (h := R / 16) (by positivity) hρ0.le hρ1 hz.le
    have h3 := discInterp_threeLines f (h := R / 16) (by positivity) le_rfl hf hM hseg h0
      (h1.trans h3ρ1)
    rw [hζ] at h3
    refine h3.trans (discInterp_rpow_le hδ hδM ?_)
    nlinarith
  have hd : DiffContOnCl ℂ f (ball 0 s) :=
    (hf.mono (closure_ball_subset_closedBall.trans (closedBall_subset_ball hsR))).diffContOnCl
  refine (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs0 hd hcirc).trans (le_of_eq ?_)
  rw [hs, hρ]
  field_simp
  ring

end

end PGM
