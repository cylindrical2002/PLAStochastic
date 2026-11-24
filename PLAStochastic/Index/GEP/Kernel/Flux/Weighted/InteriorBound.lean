import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.DominatedBound

/-!
# Local mass of the interior derivative

The spatial integral of the expected interior derivative is controlled by the
ordinary compact-spatial path majorant. The statement includes the negative
half-line, on which all genuine positive sections vanish.
-/

namespace PGM
noncomputable section
open MeasureTheory Set Filter
open scoped Interval

theorem flux_section_interior_mass_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {A : Set (Ω × ℝ)} {f : Ω → ℝ → ℝ} {B : ℝ → Ω → ℝ}
    (hA : MeasurableSet A) (hA0 : ∀ᵐ ω ∂P, ∀ t, (ω, t) ∈ A → 0 ≤ t)
    (hf : Measurable (fun p : Ω × ℝ => f p.1 p.2))
    (hBi : ∀ R, Integrable (B R) P)
    (hB : ∀ R, ∀ᵐ ω ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖f ω x‖ ≤ B R ω) (R : ℝ) :
    (∫ x in Ι (0 : ℝ) R, ‖∫ ω, A.indicator (fun p : Ω × ℝ => f p.1 p.2) (ω, x) ∂P‖) ≤
      |R| * ∫ ω, B R ω ∂P := by
  have : IsFiniteMeasure (volume.restrict (Ι (0 : ℝ) R)) := ⟨by simp [Real.volume_uIoc]⟩
  have hprod := flux_section_integrable_prod_of_local_bound P hA hA0 hf hBi hB R
  have hh (x : ℝ) (hx : x ∈ Ι (0 : ℝ) R) :
      ‖∫ ω, A.indicator (fun p : Ω × ℝ => f p.1 p.2) (ω, x) ∂P‖ ≤ ∫ ω, B R ω ∂P := by
    apply norm_integral_le_of_norm_le (hBi R)
    filter_upwards [hA0, hB R] with ω hω0 hωB
    by_cases hω : (ω, x) ∈ A
    · rw [indicator_of_mem hω]
      exact hωB x ⟨hω0 x hω, hx.2⟩
    · rw [indicator_of_notMem hω, norm_zero]
      exact (norm_nonneg _).trans (hωB 0 ⟨le_rfl, le_max_left _ _⟩)
  calc
    _ ≤ ∫ _x in Ι (0 : ℝ) R, (∫ ω, B R ω ∂P) :=
      integral_mono_ae hprod.integral_prod_right.norm (integrable_const _)
        ((ae_restrict_mem measurableSet_uIoc).mono fun x hx => hh x hx)
    _ = _ := by simp [measureReal_def, Real.volume_uIoc, smul_eq_mul]

end
end PGM
