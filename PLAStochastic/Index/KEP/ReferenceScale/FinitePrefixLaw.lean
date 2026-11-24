import PLAStochastic.Index.KEP.ReferenceScale.FiniteGapGeometry
import Mathlib.Probability.ProductMeasure

/-!
# Exact finite coordinates of the original iid stopped prefix

The finite product is the exact marginal of the unchanged iid sequence.
Zero padding preserves the original stopping event through the full finite
length, and the event is a cone under every nonzero dilation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kep_iidLaw_map_finite_prefix (nu : ProbabilityMeasure ℝ) (n : ℕ) :
    (iidLaw nu).map (fun g : ℕ → ℝ => fun i : Fin n => g i) =
      Measure.pi (fun _ : Fin n => (nu : Measure ℝ)) := by
  rw [iidLaw, Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
    Measure.infinitePi_eq_pi]

theorem kep_iidLaw_finite_prefix_integral (nu : ProbabilityMeasure ℝ) (n : ℕ)
    {F : (Fin n → ℝ) → ℝ} (hF : Measurable F) :
    (∫ g, F (fun i : Fin n => g i) ∂iidLaw nu) =
      ∫ x, F x ∂Measure.pi (fun _ : Fin n => (nu : Measure ℝ)) := by
  rw [← kep_iidLaw_map_finite_prefix nu n]
  have hp : Measurable (fun g : ℕ → ℝ => fun i : Fin n => g i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
  exact (integral_map hp.aemeasurable
    hF.aestronglyMeasurable).symm

theorem kepFiniteGapSequence_prefix {n : ℕ} (g : ℕ → ℝ) {m : ℕ} (hm : m ≤ n) :
    gapKeys (kepFiniteGapSequence (fun i : Fin n => g i)) m = gapKeys g m := by
  apply gapKeys_congr (t := n) _ m hm
  intro i hi
  simp only [kepFiniteGapSequence, dif_pos hi]

theorem kepFiniteStoppedEvent_prefix_iff (eps : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    (fun i : Fin n => g i) ∈ kepFiniteStoppedEvent eps n ↔ gapSegLen eps g ≤ (n : ℕ∞) := by
  change gapSegLen eps (kepFiniteGapSequence (fun i : Fin n => g i)) ≤ (n : ℕ∞) ↔ _
  rw [← not_lt, ← not_lt]
  simp only [gapSegLen, lt_segLen_iff]
  exact not_congr (prefixAffineFeasible_congr fun i hi => kepFiniteGapSequence_prefix g (by omega))

theorem kepFiniteStoppedEvent_smul (eps : ℝ) (n : ℕ) {c : ℝ} (hc : c ≠ 0)
    (x : Fin n → ℝ) :
    c • x ∈ kepFiniteStoppedEvent eps n ↔ x ∈ kepFiniteStoppedEvent eps n := by
  change gapSegLen eps (kepFiniteGapSequence (c • x)) ≤ (n : ℕ∞) ↔ _
  rw [kepFiniteGapSequence_smul, gapSegLen_const_mul eps _ hc]
  rfl

theorem kep_iidLaw_stopped_prefix_integral (nu : ProbabilityMeasure ℝ) (eps : ℝ) (n : ℕ)
    {phi : ℝ → ℝ} (hphi : Measurable phi) :
    (∫ g in {g : ℕ → ℝ | gapSegLen eps g ≤ (n : ℕ∞)}, phi (gapKeys g n) ∂iidLaw nu) =
      ∫ x in kepFiniteStoppedEvent eps n, phi (∑ i, x i)
        ∂Measure.pi (fun _ : Fin n => (nu : Measure ℝ)) := by
  have hstop : MeasurableSet {g : ℕ → ℝ | gapSegLen eps g ≤ (n : ℕ∞)} := by
    convert (measurableSet_lt_gapSegLen eps n).compl using 1
    ext g
    simp only [mem_ofPred_eq, mem_compl_iff, not_lt]
  let F := (kepFiniteStoppedEvent eps n).indicator (fun x : Fin n → ℝ => phi (∑ i, x i))
  have hm : Measurable F := (hphi.comp (Finset.measurable_sum _
    (fun i _ => measurable_pi_apply i))).indicator (measurableSet_kepFiniteStoppedEvent eps n)
  have hh := kep_iidLaw_finite_prefix_integral nu n hm
  dsimp only [F] at hh
  rw [integral_indicator (measurableSet_kepFiniteStoppedEvent eps n)] at hh
  rw [← integral_indicator hstop]
  apply Eq.trans _ hh
  apply integral_congr_ae
  exact ae_of_all _ fun g => by
    by_cases hg : gapSegLen eps g ≤ (n : ℕ∞)
    · have hx := (kepFiniteStoppedEvent_prefix_iff eps n g).mpr hg
      have hg' : g ∈ {g : ℕ → ℝ | gapSegLen eps g ≤ (n : ℕ∞)} := hg
      dsimp only
      rw [indicator_of_mem hg', indicator_of_mem hx]
      rw [← kepFiniteGapSequence_total, kepFiniteGapSequence_prefix g le_rfl]
    · have hx := mt (kepFiniteStoppedEvent_prefix_iff eps n g).mp hg
      have hg' : g ∉ {g : ℕ → ℝ | gapSegLen eps g ≤ (n : ℕ∞)} := hg
      dsimp only
      rw [indicator_of_notMem hg', indicator_of_notMem hx]

end

end PGM
