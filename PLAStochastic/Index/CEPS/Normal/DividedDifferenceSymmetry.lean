import PLAStochastic.Index.CEPS.Normal.DividedDifference

/-!
# Root exchange for divided differences, including marker collisions

The second divided difference is symmetric in its two root centers, even
when the marker equals a center. Those cases use the genuine derivative of
the first divided difference, so no zero-denominator formula is substituted.
-/

noncomputable section
open Complex Filter Topology
namespace PGM

theorem cepsNormal_dslope_swap (g : ℂ → ℂ) (a b : ℂ) :
    dslope g a b = dslope g b a := by
  by_cases h : b = a
  · rw [h]
  · rw [dslope_of_ne _ h, dslope_of_ne _ (Ne.symm h), slope_def_field, slope_def_field]
    field_simp
    ring

/-- Away from the center, the derivative is computed from the genuine quotient rule. -/
theorem cepsNormal_deriv_dslope_of_ne {g : ℂ → ℂ} {a b g' : ℂ}
    (hg : HasDerivAt g g' b) (hb : b ≠ a) :
    deriv (dslope g a) b = (g' * (b - a) - (g b - g a)) / (b - a) ^ 2 := by
  have hd := (hg.sub_const (g a)).div ((hasDerivAt_id b).sub_const a) (sub_ne_zero.mpr hb)
  have heq : (fun z => (g z - g a) / (z - a)) =ᶠ[𝓝 b] dslope g a := by
    filter_upwards [isOpen_ne.mem_nhds hb] with z hz
    rw [dslope_of_ne _ hz, slope_def_field]
  simpa only [mul_one, id_eq] using (hd.congr_of_eventuallyEq heq.symm).deriv

/-- The two root centers can be exchanged, including both marker collisions. -/
theorem cepsNormal_second_dslope_swap {g : ℂ → ℂ} {a b : ℂ}
    (ha : DifferentiableAt ℂ g a) (hb : DifferentiableAt ℂ g b) (t : ℂ) :
    dslope (dslope g b) a t = dslope (dslope g a) b t := by
  by_cases hab : a = b
  · rw [hab]
  by_cases hta : t = a
  · subst t
    rw [dslope_same (dslope g b) a, cepsNormal_deriv_dslope_of_ne ha.hasDerivAt hab,
      dslope_of_ne (dslope g a) hab, slope_def_field, dslope_same g a,
      dslope_of_ne g (Ne.symm hab), slope_def_field]
    field_simp
    ring
  by_cases htb : t = b
  · subst t
    rw [dslope_same (dslope g a) b, cepsNormal_deriv_dslope_of_ne hb.hasDerivAt (Ne.symm hab),
      dslope_of_ne (dslope g b) (Ne.symm hab), slope_def_field, dslope_same g b,
      dslope_of_ne g hab, slope_def_field]
    field_simp
    ring
  · rw [dslope_of_ne (dslope g b) hta, dslope_of_ne (dslope g a) htb,
      slope_def_field, slope_def_field,
      dslope_of_ne g htb, dslope_of_ne g hab, dslope_of_ne g hta,
      dslope_of_ne g (Ne.symm hab), slope_def_field, slope_def_field,
      slope_def_field, slope_def_field]
    field_simp
    ring

end PGM
