import PLAStochastic.Index.KEP.ReferenceScale.FinitePrefixLaw
import PLAStochastic.Index.KEP.ReferenceScale.LawOrbit

/-!
# Exact finite surviving windows and actual reference-law tails

Every window of the original surviving prefix is feasible. Its finite iid
probability is exactly the original shifted stopping probability, so the
proved regular-class stopping tail applies uniformly to all reference layers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

def kepFiniteWindowEvent (eps : ℝ) (n a w : ℕ) : Set (Fin n → ℝ) :=
  {x | (w : ℕ∞) < gapSegLen eps (fun t => kepFiniteGapSequence x (a + t))}

theorem measurableSet_kepFiniteWindowEvent (eps : ℝ) (n a w : ℕ) :
    MeasurableSet (kepFiniteWindowEvent eps n a w) := by
  exact (measurableSet_lt_gapSegLen eps w).preimage
    (measurable_pi_lambda _ fun t => (measurable_pi_apply (a + t)).comp
      (measurable_kepFiniteGapSequence n))

theorem kepFiniteWindowEvent_congr {eps : ℝ} {n a w : ℕ} {x y : Fin n → ℝ}
    (hxy : ∀ i : Fin n, a ≤ i.val → i.val < a + w → x i = y i) :
    x ∈ kepFiniteWindowEvent eps n a w ↔ y ∈ kepFiniteWindowEvent eps n a w := by
  change (w : ℕ∞) < gapSegLen eps (fun t => kepFiniteGapSequence x (a + t)) ↔ _
  unfold gapSegLen
  apply lt_segLen_congr
  apply gapKeys_congr (t := w)
  intro t ht
  by_cases hq : a + t < n
  · simp only [kepFiniteGapSequence, dif_pos hq]
    exact hxy ⟨a + t, hq⟩ (by change a ≤ a + t; omega)
      (by change a + t < a + w; omega)
  · simp only [kepFiniteGapSequence, dif_neg hq]

theorem kepFinite_survival_subset_window (eps : ℝ) {n a w : ℕ} (haw : a + w ≤ n) :
    (kepFiniteStoppedEvent eps n)ᶜ ⊆ kepFiniteWindowEvent eps n a w := by
  intro x hx
  have hn : (n : ℕ∞) < gapSegLen eps (kepFiniteGapSequence x) := not_le.mp hx
  rw [gapSegLen, lt_segLen_iff] at hn
  have hwin := prefixAffineFeasible_window hn (r := a) (w := w + 1) (by omega)
  change (w : ℕ∞) < gapSegLen eps (fun t => kepFiniteGapSequence x (a + t))
  rw [gapSegLen, lt_segLen_iff]
  have heq : (fun i => gapKeys (kepFiniteGapSequence x) (a + i)) =
      fun i => 1 * gapKeys (fun t => kepFiniteGapSequence x (a + t)) i +
        gapKeys (kepFiniteGapSequence x) a := by
    funext i
    rw [gapKeys_shift]
    ring
  rw [heq, prefixAffineFeasible_affine_iff one_ne_zero] at hwin
  exact hwin

theorem kep_iidLaw_map_shift (nu : ProbabilityMeasure ℝ) (a : ℕ) :
    (iidLaw nu).map (fun (g : ℕ → ℝ) (t : ℕ) => g (a + t)) = iidLaw nu := by
  rw [iidLaw, Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h => Nat.add_left_cancel h)]

theorem kepFiniteWindowEvent_prefix_iff (eps : ℝ) {n a w : ℕ} (haw : a + w ≤ n)
    (g : ℕ → ℝ) :
    (fun i : Fin n => g i) ∈ kepFiniteWindowEvent eps n a w ↔
      (w : ℕ∞) < gapSegLen eps (fun t => g (a + t)) := by
  change (w : ℕ∞) < gapSegLen eps (fun t => kepFiniteGapSequence (fun i : Fin n => g i) (a + t)) ↔ _
  unfold gapSegLen
  apply lt_segLen_congr
  apply gapKeys_congr (t := w)
  intro t ht
  simp only [kepFiniteGapSequence, dif_pos (show a + t < n by omega)]

theorem kep_pi_finite_window_eq_stopping_tail (nu : ProbabilityMeasure ℝ) (eps : ℝ)
    {n a w : ℕ} (haw : a + w ≤ n) :
    Measure.pi (fun _ : Fin n => (nu : Measure ℝ)) (kepFiniteWindowEvent eps n a w) =
      iidLaw nu {g | (w : ℕ∞) < gapSegLen eps g} := by
  have hp : Measurable (fun (g : ℕ → ℝ) (i : Fin n) => g i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
  rw [← kep_iidLaw_map_finite_prefix nu n, Measure.map_apply hp
    (measurableSet_kepFiniteWindowEvent eps n a w)]
  have hset : (fun (g : ℕ → ℝ) (i : Fin n) => g i) ⁻¹' kepFiniteWindowEvent eps n a w =
      (fun (g : ℕ → ℝ) (t : ℕ) => g (a + t)) ⁻¹' {g | (w : ℕ∞) < gapSegLen eps g} := by
    ext g
    exact kepFiniteWindowEvent_prefix_iff eps haw g
  rw [hset, ← Measure.map_apply (measurable_pi_lambda _ fun t => measurable_pi_apply (a + t))
    (measurableSet_lt_gapSegLen eps w), kep_iidLaw_map_shift]

theorem kepReference_finite_window_tail :
    ∃ c eps0 : ℝ, 0 < c ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ j n a w : ℕ, a + w ≤ n →
        Measure.pi (fun _ : Fin n => (kepReferenceLaw eps j : Measure ℝ))
          (kepFiniteWindowEvent eps n a w) ≤
          ENNReal.ofReal (72 / 71 * Real.exp (-c * w / eps ^ 2)) := by
  obtain ⟨D, theta, vlo, vhi, e0, _, ht, hvlo, _, hreg⟩ := kepReferenceLaw_regular
  refine ⟨tailRate * regV vlo, max kepReferenceClassicalThreshold
    (max e0 (epsZero (regB vhi) (regBeta D theta vlo))), mul_pos tailRate_pos (regV_pos hvlo),
    le_max_left _ _, ?_⟩
  intro eps he j n a w haw
  rw [kep_pi_finite_window_eq_stopping_tail _ eps haw]
  apply gapSegLen_tail (regV_pos hvlo)
    ((le_max_right _ _).trans ((le_max_right _ _).trans he))
    ((hreg eps ((le_max_left _ _).trans ((le_max_right _ _).trans he)) j).momClass ht hvlo)

end

end PGM
