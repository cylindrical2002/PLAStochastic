import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Paying a joint event by a uniform fresh-noise fiber bound

The observed-state event is retained in the product measure. A bound on each
fresh-noise section multiplies its actual probability, which is the
conditional step needed for geometric stopping tails.
-/

set_option autoImplicit false

namespace MeasureTheory

noncomputable section

open Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem measure_prod_fiber_event_le (mu : Measure α) (nu : Measure β) [SFinite nu]
    {s : Set α} {t : Set (α × β)} (hs : MeasurableSet s) (ht : MeasurableSet t)
    {q : ℝ≥0∞} (hfiber : ∀ x ∈ s, nu (Prod.mk x ⁻¹' t) ≤ q) :
    mu.prod nu ((s ×ˢ univ) ∩ t) ≤ q * mu s := by
  classical
  rw [Measure.prod_apply ((hs.prod MeasurableSet.univ).inter ht)]
  calc
    _ ≤ ∫⁻ x, s.indicator (fun _ => q) x ∂mu := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ s
      · rw [indicator_of_mem hx]
        exact (measure_mono (by intro z hz; exact hz.2)).trans (hfiber x hx)
      · rw [indicator_of_notMem hx]
        have he : Prod.mk x ⁻¹' ((s ×ˢ univ) ∩ t) = ∅ := by
          ext z
          simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true,
            mem_empty_iff_false, iff_false]
          exact not_and.mpr (fun h _ => hx h)
        change nu (Prod.mk x ⁻¹' ((s ×ˢ univ) ∩ t)) ≤ 0
        rw [he, measure_empty]
    _ = _ := lintegral_indicator_const hs q

end

end MeasureTheory
