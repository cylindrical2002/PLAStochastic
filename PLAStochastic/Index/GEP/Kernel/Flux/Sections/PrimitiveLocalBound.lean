import PLAStochastic.Index.GEP.Kernel.Flux.Sections.PrimitiveSeries

/-!
# Local bounds on primitive constants

Only the derivative mass on one bounded interval is used. In particular,
weighted output kernels do not need a global integrable derivative.
-/

namespace PGM
noncomputable section
open MeasureTheory Set Filter

theorem kernel_aePrimitive_constant_bound_local {J j : ℝ → ℝ} {B R : ℝ}
    (hp : AEPrimitive J j) (hR : 0 < R)
    (hJ : ∀ x ∈ Ioo (0 : ℝ) R, |J x| ≤ B) :
    ∃ c : ℝ, (∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      J x = c + ∫ t in (0 : ℝ)..x, j t) ∧
      |c| ≤ B + ∫ t in (0 : ℝ)..R, |j t| := by
  obtain ⟨hi, c, hc⟩ := hp
  have : NeZero (volume (Ioo (0 : ℝ) R)) := by
    refine ⟨?_⟩
    simpa only [Real.volume_Ioo, sub_zero, ne_eq, ENNReal.ofReal_eq_zero] using not_le.mpr hR
  have he := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioi_self :
    Ioo (0 : ℝ) R ⊆ Ioi 0) hc
  obtain ⟨x, hx, heq⟩ := ((ae_restrict_mem measurableSet_Ioo).and he).exists
  have hbound : |∫ t in (0 : ℝ)..x, j t| ≤ ∫ t in (0 : ℝ)..R, |j t| := by
    rw [intervalIntegral.integral_of_le hR.le]
    calc
      _ ≤ ∫ t in Ioc 0 x, |j t| := by
        simpa only [Real.norm_eq_abs, uIoc_of_le hx.1.le] using
          (intervalIntegral.norm_integral_le_integral_norm_uIoc
            (μ := volume) (f := j) (a := 0) (b := x))
      _ ≤ ∫ t in Ioc 0 R, |j t| := by
        apply setIntegral_mono_set
        · exact (hi R).1.abs
        · exact Eventually.of_forall fun _ => abs_nonneg _
        · exact Eventually.of_forall fun _ h => ⟨h.1, h.2.trans hx.2.le⟩
  refine ⟨c, hc, ?_⟩
  calc
    |c| = |J x - ∫ t in (0 : ℝ)..x, j t| := by rw [heq, add_sub_cancel_right]
    _ ≤ |J x| + |∫ t in (0 : ℝ)..x, j t| := abs_sub _ _
    _ ≤ B + ∫ t in (0 : ℝ)..R, |j t| := add_le_add (hJ x hx) hbound

end
end PGM
