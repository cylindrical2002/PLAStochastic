import PLAStochastic.Index.CEPS.Normal.DividedDifference

/-!
# The merged-root divided difference is nonzero at large width

The actual derivative of `g = exp (-ζ*l) * Q * exp (-2*L)` is computed first.
A bound on `Q'/Q - 2*L'`, strictly smaller than the real width, then gives a
positive lower bound for that derivative. Thus the merged denominator is
paid by an explicit factor budget rather than assumed nonzero.
-/

noncomputable section
open Complex
namespace PGM
namespace CepsNormalData

variable (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q : ℂ)

/-- The logarithmic derivative formula follows from genuine spatial derivatives. -/
theorem hasDerivAt_normalG {l β Q' L' : ℂ}
    (hQ : HasDerivAt a.Q Q' β) (hL : HasDerivAt (L μ q) L' β)
    (hQ0 : a.Q β ≠ 0) :
    HasDerivAt (a.normalG L μ q l)
      (a.normalG L μ q l β * (-l + Q' / a.Q β - 2 * L')) β := by
  have h := ((((hasDerivAt_id β).neg.mul_const l).cexp).mul hQ).mul
    ((hL.const_mul (-2)).cexp)
  refine h.congr_deriv ?_
  dsimp [normalG]
  field_simp
  ring

/-- A concrete derivative budget pays the merged denominator, with a quantitative bound. -/
theorem normalG_deriv_lower {l M : ℝ} {β Q' L' : ℂ}
    (hQ : HasDerivAt a.Q Q' β) (hL : HasDerivAt (L μ q) L' β)
    (hQ0 : a.Q β ≠ 0) (hbudget : ‖Q' / a.Q β - 2 * L'‖ ≤ M)
    (hl : M < l) :
    (l - M) * ‖a.normalG L μ q l β‖ ≤ ‖deriv (a.normalG L μ q l) β‖ := by
  have hl0 : 0 < l := lt_of_le_of_lt ((norm_nonneg _).trans hbudget) hl
  have htri := norm_sub_norm_le (l : ℂ) (Q' / a.Q β - 2 * L')
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl0] at htri
  have hnorm : l - M ≤ ‖-(l : ℂ) + Q' / a.Q β - 2 * L'‖ := by
    have he : -(l : ℂ) + Q' / a.Q β - 2 * L' =
        -((l : ℂ) - (Q' / a.Q β - 2 * L')) := by ring
    rw [he, norm_neg]
    linarith
  rw [(a.hasDerivAt_normalG L μ q hQ hL hQ0).deriv, norm_mul]
  calc
    (l - M) * ‖a.normalG L μ q l β‖ = ‖a.normalG L μ q l β‖ * (l - M) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)

theorem normalG_deriv_ne {l M : ℝ} {β Q' L' : ℂ}
    (hQ : HasDerivAt a.Q Q' β) (hL : HasDerivAt (L μ q) L' β)
    (hQ0 : a.Q β ≠ 0) (hbudget : ‖Q' / a.Q β - 2 * L'‖ ≤ M)
    (hl : M < l) : deriv (a.normalG L μ q l) β ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le
    (mul_pos (sub_pos.mpr hl) (norm_pos_iff.mpr (a.normalG_ne L μ q l hQ0)))
    (a.normalG_deriv_lower L μ q hQ hL hQ0 hbudget hl)

/-- At a merged root, the first divided difference is the paid derivative. -/
theorem normalG_merged_dslope_ne {l M : ℝ} {Q' L' : ℂ}
    (hroots : a.βp = a.βm)
    (hQ : HasDerivAt a.Q Q' a.βm) (hL : HasDerivAt (L μ q) L' a.βm)
    (hQ0 : a.Q a.βm ≠ 0) (hbudget : ‖Q' / a.Q a.βm - 2 * L'‖ ≤ M)
    (hl : M < l) : dslope (a.normalG L μ q l) a.βm a.βp ≠ 0 := by
  rw [hroots, dslope_same]
  exact a.normalG_deriv_ne L μ q hQ hL hQ0 hbudget hl

end CepsNormalData
end PGM
