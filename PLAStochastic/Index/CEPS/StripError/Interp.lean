import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound
import Mathlib.Analysis.Convex.Segment

/-!
# WP9: one-sided Landau–Kolmogorov interpolation for holomorphic functions

If `f` is holomorphic and bounded by `M` on `B(c, r)`, the second-order Taylor bound of
`CauchyBound` gives, for any `z ∈ B(c, r/2)`,

`‖f'(c)‖ ≤ (‖f z‖ + ‖f c‖) / ‖z - c‖ + 32 M ‖z - c‖ / r²`

(`norm_deriv_le_of_two_points`). Only the values at the two points `c`, `z` need to be small:
the strip errors are small only on the closed right discount half-plane and on the imaginary
mark axis, so the second point is taken in the direction that stays there. Together with the mean
value inequality on a segment (`norm_sub_le_of_segment`) this replaces a division by a small
denominator `d` with an error that vanishes at the origin.
-/

noncomputable section

open Set Metric

namespace PGM

variable {f : ℂ → ℂ} {c : ℂ} {r M : ℝ}

theorem norm_deriv_le_of_two_points (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hM : ∀ z ∈ ball c r, ‖f z‖ ≤ M) {z : ℂ} (hz : z ∈ ball c (r / 2)) (hzc : z ≠ c) :
    ‖deriv f c‖ ≤ (‖f z‖ + ‖f c‖) / ‖z - c‖ + 32 * M / r ^ 2 * ‖z - c‖ := by
  have hT := norm_sub_sub_deriv_le_of_ball hr hf hM hz
  have hpos : 0 < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzc)
  have hk : ‖deriv f c * (z - c)‖ ≤ ‖f z‖ + ‖f c‖ + 32 * M / r ^ 2 * ‖z - c‖ ^ 2 := by
    have h1 := norm_sub_le (f z - f c) (f z - f c - deriv f c * (z - c))
    rw [show f z - f c - (f z - f c - deriv f c * (z - c)) = deriv f c * (z - c) by ring] at h1
    have h2 := norm_sub_le (f z) (f c)
    linarith
  rw [norm_mul] at hk
  rw [div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]
  nlinarith

/-- The mean value inequality on a segment of `ℂ`. -/
theorem norm_sub_le_of_segment {g : ℂ → ℂ} {a b : ℂ} {C : ℝ}
    (hd : ∀ x ∈ segment ℝ a b, DifferentiableAt ℂ g x) (hC : ∀ x ∈ segment ℝ a b, ‖deriv g x‖ ≤ C) :
    ‖g b - g a‖ ≤ C * ‖b - a‖ :=
  (convex_segment a b).norm_image_sub_le_of_norm_deriv_le hd hC (left_mem_segment ℝ a b)
    (right_mem_segment ℝ a b)

/-- Points of the segment `[0, b]` are real multiples of `b`. -/
theorem mem_segment_zero_iff {b x : ℂ} :
    x ∈ segment ℝ 0 b ↔ ∃ s : ℝ, s ∈ Icc (0 : ℝ) 1 ∧ x = (s : ℂ) * b := by
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    simp [AffineMap.lineMap_apply_module, Complex.real_smul]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    simp [AffineMap.lineMap_apply_module, Complex.real_smul]

/-- **Interpolation engine.** A function holomorphic and bounded by `M` on discs of radius `r`
around the points of the segment `[0, q]`, small (`≤ ε`) at these points and at their shifts by
`h u`, satisfies `‖F q - F 0‖ ≤ (2ε/h + 32 M h / r²) ‖q‖`. -/
theorem norm_sub_le_of_small_on_segment {F : ℂ → ℂ} {q u : ℂ} (hu : ‖u‖ = 1) {r h M ε : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hhr : h < r / 2)
    (hdiff : ∀ x ∈ segment ℝ 0 q, DifferentiableOn ℂ F (ball x r))
    (hM : ∀ x ∈ segment ℝ 0 q, ∀ z ∈ ball x r, ‖F z‖ ≤ M)
    (hx : ∀ x ∈ segment ℝ 0 q, ‖F x‖ ≤ ε) (hxu : ∀ x ∈ segment ℝ 0 q, ‖F (x + h * u)‖ ≤ ε) :
    ‖F q - F 0‖ ≤ (2 * ε / h + 32 * M / r ^ 2 * h) * ‖q‖ := by
  have hderiv : ∀ x ∈ segment ℝ 0 q, ‖deriv F x‖ ≤ 2 * ε / h + 32 * M / r ^ 2 * h := by
    intro x hxs
    have hz : x + h * u ∈ ball x (r / 2) := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, hu, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hh]
      exact hhr
    have hzx : x + h * u ≠ x := by
      intro he
      have : h * u = 0 := by linear_combination he
      rcases mul_eq_zero.mp this with h0 | h0
      · exact hh.ne' (Complex.ofReal_eq_zero.mp h0)
      · rw [h0, norm_zero] at hu; exact zero_ne_one hu
    have hnorm : ‖x + h * u - x‖ = h := by
      rw [add_sub_cancel_left, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hh]
    have h1 := norm_deriv_le_of_two_points hr (hdiff x hxs) (hM x hxs) hz hzx
    rw [hnorm] at h1
    calc _ ≤ _ := h1
      _ ≤ (ε + ε) / h + 32 * M / r ^ 2 * h := by
        gcongr
        · exact hxu x hxs
        · exact hx x hxs
      _ = _ := by ring
  have hdx : ∀ x ∈ segment ℝ 0 q, DifferentiableAt ℂ F x := fun x hxs =>
    (hdiff x hxs x (mem_ball_self hr)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have := norm_sub_le_of_segment hdx hderiv
  rwa [sub_zero] at this

/-- **The interpolation budget.** With the step `h = min (r/4) e^{-cl/2}` on a disc of radius
`r ≥ ρ'/(1+l)²`, an error `K e^{-cl}` at the two points and a polynomial disc bound
`M ≤ A (1+l)³`, the derivative budget is `O((1+l)⁷ e^{-cl/2})`. -/
theorem interp_budget_le {c K A ρ' r M l : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hρ' : 0 < ρ') (hl : 0 ≤ l) (hr : ρ' / (1 + l) ^ 2 ≤ r) (hM : M ≤ A * (1 + l) ^ 3) :
    2 * (K * Real.exp (-c * l)) / min (r / 4) (Real.exp (-(c / 2) * l)) +
        32 * M / r ^ 2 * min (r / 4) (Real.exp (-(c / 2) * l)) ≤
      (8 * K / ρ' + 2 * K + 32 * A / ρ' ^ 2) * (1 + l) ^ 7 * Real.exp (-(c / 2) * l) := by
  set E := Real.exp (-(c / 2) * l) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have h1l : 1 ≤ 1 + l := by linarith
  have hp : 0 < (1 + l) ^ 2 := by positivity
  have hrpos : 0 < r := lt_of_lt_of_le (div_pos hρ' hp) hr
  set h := min (r / 4) E with hhdef
  have hh : 0 < h := lt_min (by positivity) hE
  have hhE : h ≤ E := min_le_right _ _
  have hEE : Real.exp (-c * l) = E * E := by
    rw [hEdef, ← Real.exp_add]; congr 1; ring
  -- `1/h ≤ 4/r + 1/E`
  have hinv : 1 / h ≤ 4 / r + 1 / E := by
    rcases min_choice (r / 4) E with hmin | hmin
    · rw [hhdef, hmin]
      have : 0 ≤ 1 / E := by positivity
      rw [show 1 / (r / 4) = 4 / r by field_simp]
      linarith
    · rw [hhdef, hmin]
      have : 0 ≤ 4 / r := by positivity
      linarith
  have hrinv : 1 / r ≤ (1 + l) ^ 2 / ρ' := by
    rw [div_le_div_iff₀ hrpos hρ']
    have := (div_le_iff₀ hp).mp hr
    nlinarith
  have hp7 : (1 + l) ^ 2 ≤ (1 + l) ^ 7 := pow_le_pow_right₀ h1l (by norm_num)
  have hp7' : (1 : ℝ) ≤ (1 + l) ^ 7 := one_le_pow₀ h1l
  have hEle : E ≤ 1 := by
    rw [hEdef]; exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hterm1 : 2 * (K * Real.exp (-c * l)) / h ≤ (8 * K / ρ' + 2 * K) * (1 + l) ^ 7 * E := by
    rw [hEE]
    calc 2 * (K * (E * E)) / h = 2 * K * E * E * (1 / h) := by ring
      _ ≤ 2 * K * E * E * (4 / r + 1 / E) := by gcongr
      _ = 8 * K * E * E * (1 / r) + 2 * K * E := by field_simp; ring
      _ ≤ 8 * K * E * 1 * ((1 + l) ^ 2 / ρ') + 2 * K * E := by gcongr
      _ = 8 * K / ρ' * (1 + l) ^ 2 * E + 2 * K * E := by ring
      _ ≤ 8 * K / ρ' * (1 + l) ^ 7 * E + 2 * K * ((1 + l) ^ 7 * E) := by
        gcongr
        nlinarith
      _ = _ := by ring
  have hterm2 : 32 * M / r ^ 2 * h ≤ 32 * A / ρ' ^ 2 * (1 + l) ^ 7 * E := by
    have hr2 : 1 / r ^ 2 ≤ (1 + l) ^ 4 / ρ' ^ 2 := by
      have := mul_le_mul hrinv hrinv (by positivity) (by positivity)
      calc 1 / r ^ 2 = 1 / r * (1 / r) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    calc 32 * M / r ^ 2 * h = 32 * M * (1 / r ^ 2) * h := by ring
      _ ≤ 32 * (A * (1 + l) ^ 3) * ((1 + l) ^ 4 / ρ' ^ 2) * E := by gcongr
      _ = _ := by ring
  calc _ ≤ (8 * K / ρ' + 2 * K) * (1 + l) ^ 7 * E + 32 * A / ρ' ^ 2 * (1 + l) ^ 7 * E :=
        add_le_add hterm1 hterm2
    _ = _ := by ring

/-- **Real one-sided interpolation.** If `e' = g` on `[a, a+δ]`, `g` moves by at most
`L (x - a)` there and `e` is small at both ends, then `‖g a‖ ≤ 2ε/δ + L δ`. -/
theorem norm_le_of_real_secant {e g : ℝ → ℂ} {a δ ε L : ℝ} (hδ : 0 < δ)
    (hd : ∀ x ∈ Icc a (a + δ), HasDerivAt e (g x) x)
    (hL : ∀ x ∈ Icc a (a + δ), ‖g x - g a‖ ≤ L * (x - a))
    (he0 : ‖e a‖ ≤ ε) (he1 : ‖e (a + δ)‖ ≤ ε) : ‖g a‖ ≤ 2 * ε / δ + L * δ := by
  set k : ℝ → ℂ := fun x => e x - (x : ℂ) * g a with hk
  have hkd : ∀ x ∈ Icc a (a + δ), HasDerivWithinAt k (g x - g a) (Icc a (a + δ)) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * g a) (1 * g a) x :=
      (hasDerivAt_id x).ofReal_comp.mul_const (g a)
    have := (hd x hx).sub h1
    rw [one_mul] at this
    exact this.hasDerivWithinAt
  have hkb : ∀ x ∈ Ico a (a + δ), ‖g x - g a‖ ≤ L * δ := by
    intro x hx
    refine (hL x ⟨hx.1, hx.2.le⟩).trans ?_
    have hL0 : 0 ≤ L := by
      have := hL a ⟨le_rfl, by linarith⟩
      have h2 := hL (a + δ) ⟨by linarith, le_rfl⟩
      rw [add_sub_cancel_left] at h2
      nlinarith [norm_nonneg (g (a + δ) - g a)]
    exact mul_le_mul_of_nonneg_left (by linarith [hx.2]) hL0
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hkd hkb (a + δ) ⟨by linarith, le_rfl⟩
  rw [add_sub_cancel_left] at hmv
  have he : (δ : ℂ) * g a = e (a + δ) - e a - (k (a + δ) - k a) := by
    simp only [hk]
    push_cast
    ring
  have hn : δ * ‖g a‖ ≤ ε + ε + L * δ * δ := by
    have := norm_mul (δ : ℂ) (g a)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] at this
    rw [← this, he]
    calc _ ≤ ‖e (a + δ) - e a‖ + ‖k (a + δ) - k a‖ := norm_sub_le _ _
      _ ≤ (‖e (a + δ)‖ + ‖e a‖) + L * δ * δ := add_le_add (norm_sub_le _ _) hmv
      _ ≤ _ := by linarith
  rw [div_add' _ _ _ hδ.ne', le_div_iff₀ hδ]
  nlinarith

end PGM
