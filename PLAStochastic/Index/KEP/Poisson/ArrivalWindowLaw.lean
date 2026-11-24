import PLAStochastic.Index.KEP.Poisson.ArrivalWindowCount

/-!
# The actual arrival configuration has the original Poisson window law

The measurable configuration cut out of the canonical exponential arrival
sequence has Poisson count and the proved conditional sorted-uniform kernel.
The equality uses the same poissonWindow object as the finite-sample height
bridge, with no window-law premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Renyi
open scoped ENNReal unitInterval Nat

theorem kepArrivalWindowConfiguration_law {s : ℝ} (hs : 0 < s) (p : ℝ) :
    expSeqMeasure.map (kepArrivalWindowConfiguration s p) =
      poissonMeasure ⟨s, hs.le⟩ ⊗ₘ winKernel p := by
  apply Measure.ext_nat_prod
  intro k C hC
  rw [Measure.map_apply (measurable_kepArrivalWindowConfiguration s p)
    ((measurableSet_singleton k).prod hC)]
  have he : (kepArrivalWindowConfiguration s p ⁻¹' ({k} ×ˢ C) : Set (ℕ → ℝ)) =ᵐ[expSeqMeasure]
      (kepArrivalCountEvent s k ∩
        (fun g => padScale p (kepArrivalWindowCoordinates s k g)) ⁻¹' C : Set (ℕ → ℝ)) := by
    filter_upwards [kepArrivalCount_ae_spec hs] with g hg
    apply propext
    change (kepArrivalCount s g = k ∧
      padScale p (kepArrivalWindowCoordinates s (kepArrivalCount s g) g) ∈ C) ↔
      g ∈ kepArrivalCountEvent s k ∧ padScale p (kepArrivalWindowCoordinates s k g) ∈ C
    constructor
    · rintro ⟨hcount, hpad⟩
      rw [hcount] at hg hpad
      exact ⟨hg, hpad⟩
    · rintro ⟨hevent, hpad⟩
      have hcount := (kepArrivalCount_eq_iff s g k).mpr (Or.inl hevent)
      exact ⟨hcount, by rw [hcount]; exact hpad⟩
  rw [measure_congr he, expSeqMeasure_arrival_window_kernel hs p k hC,
    Measure.compProd_apply_prod (measurableSet_singleton k) hC, lintegral_singleton, mul_comm]

theorem kepPoissonWindow_actual_configuration_law (M : ℕ) (p : I)
    (hM : 0 < (M : ℝ)) (hp : 0 < (p : ℝ)) :
    expSeqMeasure.map (kepArrivalWindowConfiguration ((M : ℝ) * p) p) = poissonWindow M p := by
  exact kepArrivalWindowConfiguration_law (mul_pos hM hp) p

theorem kepPoissonWindow_actual_event (M : ℕ) (p : I)
    (hM : 0 < (M : ℝ)) (hp : 0 < (p : ℝ))
    {A : Set (ℕ × (ℕ → ℝ))} (hA : MeasurableSet A) :
    (poissonWindow M p).real A =
      expSeqMeasure.real (kepArrivalWindowConfiguration ((M : ℝ) * p) p ⁻¹' A) := by
  rw [← kepPoissonWindow_actual_configuration_law M p hM hp,
    map_measureReal_apply (measurable_kepArrivalWindowConfiguration _ _) hA]

end

end PGM
