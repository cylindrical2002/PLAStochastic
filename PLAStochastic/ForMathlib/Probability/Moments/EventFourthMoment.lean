import PLAStochastic.ForMathlib.Probability.Hellinger.Observables

/-!
# A fourth moment pays a second moment restricted to an event

The event may depend arbitrarily on the observable. Its actual probability
is retained by the Hilbert-space Cauchy--Schwarz inequality.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]

theorem integral_event_sq_le_fourth_moment {X : Ω → ℝ}
    (hX : Measurable X) (hfour : Integrable (fun w => X w ^ 4) P)
    {s : Set Ω} (hs : MeasurableSet s) :
    Integrable (s.indicator (fun w => X w ^ 2)) P ∧
      ∫ w, s.indicator (fun w => X w ^ 2) w ∂P ≤
        Real.sqrt (∫ w, X w ^ 4 ∂P) * Real.sqrt (P.real s) := by
  let F : Ω → ℝ := fun w => X w ^ 2
  let G : Ω → ℝ := s.indicator (fun _ => 1)
  have hF : MemLp F 2 P := by
    apply (memLp_two_iff_integrable_sq (hX.pow_const 2).aestronglyMeasurable).mpr
    simpa only [F, ← pow_mul] using hfour
  have hG : MemLp G 2 P := (memLp_const (1 : ℝ)).indicator hs
  have hprod : Integrable (fun w => F w * G w) P :=
    HellingerDensity.integrable_mul_of_memLp_two hF hG
  have he : (fun w => F w * G w) = s.indicator (fun w => X w ^ 2) := by
    funext w
    by_cases hw : w ∈ s
    · simp only [F, G, Set.indicator_of_mem hw, mul_one]
    · simp only [G, Set.indicator_of_notMem hw, mul_zero]
  have hnF : ‖hF.toLp F‖ = Real.sqrt (∫ w, X w ^ 4 ∂P) := by
    have hsq := HellingerDensity.norm_toLp_sq hF
    simp only [F, ← pow_mul] at hsq
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hnG : ‖hG.toLp G‖ = Real.sqrt (P.real s) := by
    have hsq := HellingerDensity.norm_toLp_sq hG
    have hGs : (fun w => G w ^ 2) = G := by
      funext w
      by_cases hw : w ∈ s
      · simp only [G, Set.indicator_of_mem hw, one_pow]
      · simp only [G, Set.indicator_of_notMem hw, zero_pow two_ne_zero]
    rw [hGs, integral_indicator_const 1 hs, smul_eq_mul, mul_one] at hsq
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨he ▸ hprod, ?_⟩
  rw [← he, ← HellingerDensity.inner_toLp_eq_integral_mul hF hG]
  exact (le_abs_self _).trans
    ((abs_real_inner_le_norm (hF.toLp F) (hG.toLp G)).trans_eq (by rw [hnF, hnG]))

end

end ProbabilityTheory
