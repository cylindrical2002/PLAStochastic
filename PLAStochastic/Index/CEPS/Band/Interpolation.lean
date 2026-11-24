import PLAStochastic.Index.CEPS.Band.SecondWidth

/-!
# Secant interpolation with a Lipschitz first derivative

This is the derivative upgrade needed for the strip-error argument. Its inputs
are genuine first derivatives and a Lipschitz derivative budget, so a pointwise
classical second derivative is unnecessary.
-/

namespace PGM
noncomputable section
open Set
open scoped NNReal

/-- A small function and a polynomial `C¹,¹` budget control its first derivative through a
short secant. The result applies directly to complex-valued strip errors. -/
theorem cepsBand_norm_deriv_le_secant {f : ℝ → ℂ} {a δ : ℝ} (hδ : 0 < δ)
    {L : ℝ≥0} (hdiff : ∀ x ∈ Icc a (a + δ), HasDerivAt f (deriv f x) x)
    (hLip : LipschitzOnWith L (deriv f) (Icc a (a + δ))) :
    ‖deriv f a‖ ≤ (‖f (a + δ)‖ + ‖f a‖) / δ + (L : ℝ) * δ := by
  let g : ℝ → ℂ := f - fun x : ℝ => (x : ℂ) * deriv f a
  have hg : ∀ x ∈ Icc a (a + δ), HasDerivAt g (deriv f x - deriv f a) x := by
    intro x hx
    convert (hdiff x hx).sub (((hasDerivAt_id x).ofReal_comp).mul_const (deriv f a)) using 1 <;>
      first | rfl | simp
  have hb : ∀ x ∈ Ico a (a + δ), ‖deriv f x - deriv f a‖ ≤ (L : ℝ) * δ := by
    intro x hx
    have h := hLip.dist_le_mul x ⟨hx.1, hx.2.le⟩ a ⟨le_rfl, by linarith⟩
    rw [dist_eq_norm, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith [hx.2]) L.coe_nonneg)
  have hres := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x hx => (hg x hx).hasDerivWithinAt) hb (a + δ) ⟨by linarith, le_rfl⟩
  rw [add_sub_cancel_left] at hres
  have he : (δ : ℂ) * deriv f a = f (a + δ) - f a - (g (a + δ) - g a) := by
    dsimp [g]
    push_cast
    ring
  have hn : δ * ‖deriv f a‖ ≤ ‖f (a + δ)‖ + ‖f a‖ + (L : ℝ) * δ * δ := by
    calc
      _ = ‖(δ : ℂ) * deriv f a‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
      _ = ‖f (a + δ) - f a - (g (a + δ) - g a)‖ := by rw [he]
      _ ≤ ‖f (a + δ) - f a‖ + ‖g (a + δ) - g a‖ := norm_sub_le _ _
      _ ≤ ‖f (a + δ)‖ + ‖f a‖ + (L : ℝ) * δ * δ :=
        add_le_add (norm_sub_le _ _) hres
  calc
    ‖deriv f a‖ ≤ (‖f (a + δ)‖ + ‖f a‖ + (L : ℝ) * δ * δ) / δ :=
      (le_div_iff₀ hδ).mpr (by nlinarith [hn])
    _ = (‖f (a + δ)‖ + ‖f a‖) / δ + (L : ℝ) * δ := by field_simp

end
end PGM
