import PLAStochastic.Index.KEP.StoppedPrefixes
import PLAStochastic.ForMathlib.Probability.Moments.ExponentialPolynomial

/-!
# Nonnegative stopped prefixes inherit the actual full-path integer moments

The original stop may depend arbitrarily on every observed increment. Its
nonnegative stopped cumulative sum is bounded pointwise by the full sum at
the same deterministic horizon, which pays both integrability and its moment.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

theorem kepStoppedPrefix_gapKeys_nonneg_le (eps : ℝ) (N : ℕ) {g : ℕ → ℝ}
    (hg : ∀ i, 0 ≤ g i) :
    0 ≤ gapKeys (kepStoppedPrefix eps N g) N ∧
      gapKeys (kepStoppedPrefix eps N g) N ≤ gapKeys g N := by
  have hp (i : ℕ) (hi : i < N) :
      0 ≤ kepStoppedPrefix eps N g i ∧ kepStoppedPrefix eps N g i ≤ g i := by
    by_cases ht : (i : ℕ∞) < gapSegLen eps g
    · simp only [kepStoppedPrefix, hi, ht, and_self, if_true, le_refl, and_true]
      exact hg i
    · simp only [kepStoppedPrefix, ht, and_false, if_false, le_refl, true_and]
      exact hg i
  exact ⟨sum_nonneg (fun i hi => (hp i (mem_range.mp hi)).1),
    sum_le_sum (fun i hi => (hp i (mem_range.mp hi)).2)⟩

theorem integrable_stopped_gapKeys_power_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℕ → ℝ} (hX : Measurable X)
    (hpos : ∀ᵐ w ∂P, ∀ i, 0 ≤ X w i) (eps : ℝ) (N p : ℕ)
    (hi : Integrable (fun w => gapKeys (X w) N ^ p) P) :
    Integrable (fun w => gapKeys (kepStoppedPrefix eps N (X w)) N ^ p) P ∧
      ∫ w, gapKeys (kepStoppedPrefix eps N (X w)) N ^ p ∂P ≤
        ∫ w, gapKeys (X w) N ^ p ∂P := by
  have hbound : ∀ᵐ w ∂P,
      ‖gapKeys (kepStoppedPrefix eps N (X w)) N ^ p‖ ≤ gapKeys (X w) N ^ p := by
    filter_upwards [hpos] with w hw
    have hs := kepStoppedPrefix_gapKeys_nonneg_le eps N hw
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs.1 p)]
    exact pow_le_pow_left₀ hs.1 hs.2 p
  have hmeas : Measurable (fun w => gapKeys (kepStoppedPrefix eps N (X w)) N ^ p) :=
    (((measurable_pi_apply N).comp measurable_gapKeys).comp
      ((measurable_kepStoppedPrefix eps N).comp hX)).pow_const p
  have hint : Integrable (fun w => gapKeys (kepStoppedPrefix eps N (X w)) N ^ p) P :=
    hi.mono' hmeas.aestronglyMeasurable hbound
  exact ⟨hint, integral_mono_ae hint hi
    (hbound.mono (fun _w hw => (le_abs_self _).trans hw))⟩

end

end PGM
