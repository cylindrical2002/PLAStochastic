import PLAStochastic.ForMathlib.Analysis.ConvexAntitoneSumIntegral

/-! # Assembly of the overshoot-mean Lipschitz bound (roadmap 1.1(e))

Abstract real-variable form of the Appendix I argument `1/2 ≤ β' ≤ 3/4`.  Given
functions `β m τ : ℝ → ℝ` on `(0,∞)` with

* the mean identity `β x = x/2 - 1/(2x) + m x`  (`β(a) = a/2 - 1/(2a) + 𝔼M_a`),
* the argmax envelope `(y - x) τ y ≤ m x - m y ≤ (y - x) τ x` for `x ≤ y`
  (`(c-a)τ*_c ≤ M_a - M_c ≤ (c-a)τ*_a` integrated),
* the Sparre Andersen bracket `1/(2x²) - 1/4 ≤ τ x ≤ 1/(2x²)`
  (`𝔼τ*_a = ∑ Φ(-a√n)` with `Fluctuation.tsum_gaussianTailSqrt_bounds`),

every `0 < a ≤ c` satisfies `(c - a)/2 ≤ β c - β a ≤ 3 (c - a)/4`.  No derivative of
`β` is used: the local two-sided bounds have a quadratic error which the
telescoping lemma removes.
-/
noncomputable section
namespace SwingRepair
namespace Fluctuation

/-- The local upper bound with quadratic error. -/
theorem overshootMean_local_upper {β m τ : ℝ → ℝ}
    (hβ : ∀ x, 0 < x → β x = x / 2 - 1 / (2 * x) + m x)
    (henv : ∀ x y, 0 < x → x ≤ y → (y - x) * τ y ≤ m x - m y)
    (hτ : ∀ x, 0 < x → 1 / (2 * x ^ 2) - 1 / 4 ≤ τ x)
    {a x y : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxy : x ≤ y) :
    β y - β x ≤ (y - x) * (3 / 4 + 1 / (2 * a ^ 3) * (y - x)) := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have h1 := henv x y hx hxy
  have h2 := hτ y hy
  rw [hβ x hx, hβ y hy]
  -- β y - β x = (y-x)/2 + (y-x)/(2xy) - (m x - m y)
  have hid : y / 2 - 1 / (2 * y) + m y - (x / 2 - 1 / (2 * x) + m x) =
      (y - x) / 2 + (y - x) / (2 * x * y) - (m x - m y) := by
    field_simp
    ring
  rw [hid]
  have h3 : (y - x) * τ y ≥ (y - x) * (1 / (2 * y ^ 2) - 1 / 4) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  -- (y-x)/(2xy) - (y-x)/(2y²) = (y-x)²/(2xy²) ≤ (y-x)²/(2a³)
  have h4 : (y - x) / (2 * x * y) - (y - x) * (1 / (2 * y ^ 2)) = (y - x) ^ 2 / (2 * x * y ^ 2) := by
    field_simp
  have h5 : (y - x) ^ 2 / (2 * x * y ^ 2) ≤ (y - x) ^ 2 / (2 * a ^ 3) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    have hay : a ≤ y := hax.trans hxy
    have : a ^ 3 ≤ x * y ^ 2 := by
      calc a ^ 3 = a * (a * a) := by ring
        _ ≤ x * (y * y) := by
            apply mul_le_mul hax _ (by positivity) hx.le
            exact mul_le_mul hay hay ha.le hy.le
        _ = x * y ^ 2 := by ring
    linarith
  have h6 : (y - x) * (3 / 4 + 1 / (2 * a ^ 3) * (y - x)) =
      (y - x) / 2 + (y - x) / 4 + (y - x) ^ 2 / (2 * a ^ 3) := by
    field_simp
    ring
  rw [h6]
  linarith

/-- The local lower bound with quadratic error. -/
theorem overshootMean_local_lower {β m τ : ℝ → ℝ}
    (hβ : ∀ x, 0 < x → β x = x / 2 - 1 / (2 * x) + m x)
    (henv : ∀ x y, 0 < x → x ≤ y → m x - m y ≤ (y - x) * τ x)
    (hτ : ∀ x, 0 < x → τ x ≤ 1 / (2 * x ^ 2))
    {a x y : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxy : x ≤ y) :
    (y - x) * (1 / 2 - 1 / (2 * a ^ 3) * (y - x)) ≤ β y - β x := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have h1 := henv x y hx hxy
  have h2 := hτ x hx
  rw [hβ x hx, hβ y hy]
  have hid : y / 2 - 1 / (2 * y) + m y - (x / 2 - 1 / (2 * x) + m x) =
      (y - x) / 2 + (y - x) / (2 * x * y) - (m x - m y) := by
    field_simp
    ring
  rw [hid]
  have h3 : (y - x) * τ x ≤ (y - x) * (1 / (2 * x ^ 2)) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  -- (y-x)/(2x²) - (y-x)/(2xy) = (y-x)²/(2x²y) ≤ (y-x)²/(2a³)
  have h4 : (y - x) * (1 / (2 * x ^ 2)) - (y - x) / (2 * x * y) = (y - x) ^ 2 / (2 * x ^ 2 * y) := by
    field_simp
  have h5 : (y - x) ^ 2 / (2 * x ^ 2 * y) ≤ (y - x) ^ 2 / (2 * a ^ 3) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    have hay : a ≤ y := hax.trans hxy
    have : a ^ 3 ≤ x ^ 2 * y := by
      calc a ^ 3 = (a * a) * a := by ring
        _ ≤ (x * x) * y := by
            apply mul_le_mul _ hay ha.le (by positivity)
            exact mul_le_mul hax hax ha.le hx.le
        _ = x ^ 2 * y := by ring
    linarith
  have h6 : (y - x) * (1 / 2 - 1 / (2 * a ^ 3) * (y - x)) =
      (y - x) / 2 - (y - x) ^ 2 / (2 * a ^ 3) := by
    field_simp
  rw [h6]
  linarith

/-- **`(c-a)/2 ≤ β(c) - β(a) ≤ 3(c-a)/4`** from the mean identity, the argmax
envelope and the Sparre Andersen bracket. -/
theorem overshootMean_bounds_of_inputs {β m τ : ℝ → ℝ}
    (hβ : ∀ x, 0 < x → β x = x / 2 - 1 / (2 * x) + m x)
    (henv_lo : ∀ x y, 0 < x → x ≤ y → (y - x) * τ y ≤ m x - m y)
    (henv_hi : ∀ x y, 0 < x → x ≤ y → m x - m y ≤ (y - x) * τ x)
    (hτ_lo : ∀ x, 0 < x → 1 / (2 * x ^ 2) - 1 / 4 ≤ τ x)
    (hτ_hi : ∀ x, 0 < x → τ x ≤ 1 / (2 * x ^ 2))
    {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    1 / 2 * (c - a) ≤ β c - β a ∧ β c - β a ≤ 3 / 4 * (c - a) := by
  have hC : (0 : ℝ) ≤ 1 / (2 * a ^ 3) := by positivity
  constructor
  · exact le_sub_of_local_quadratic_bound hac hC fun x y hax hxy _ =>
      overshootMean_local_lower hβ henv_hi hτ_hi ha hax hxy
  · exact sub_le_of_local_quadratic_bound hac hC fun x y hax hxy _ =>
      overshootMean_local_upper hβ henv_lo hτ_lo ha hax hxy

end Fluctuation
end SwingRepair
