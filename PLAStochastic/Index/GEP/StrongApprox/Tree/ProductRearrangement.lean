import PLAStochastic.Index.GEP.StrongApprox.Quantile.SplitLaw
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Product measure rearrangements for the dyadic random construction -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Function
open scoped ENNReal

attribute [local fun_prop] SADensity.measurable_splitQuantile

/-- Independent pairs can be regrouped into two independent parent/innovation pairs. -/
theorem sa_map_prod_four_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (η : Measure D)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure η] :
    ((μ.prod ν).prod (ρ.prod η)).map
      (fun z : (A × B) × (C × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2))) =
        (μ.prod ρ).prod (ν.prod η) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop)]
  calc
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, f ((a, c), (b, d)) ∂η ∂ρ ∂ν ∂μ := by
      rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro a
      apply lintegral_congr
      intro b
      exact lintegral_prod _ (by fun_prop)
    _ = ∫⁻ a, ∫⁻ c, ∫⁻ b, ∫⁻ d, f ((a, c), (b, d)) ∂η ∂ν ∂ρ ∂μ := by
      apply lintegral_congr
      intro a
      exact lintegral_lintegral_swap (by fun_prop)
    _ = _ := by
      rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro a
      apply lintegral_congr
      intro c
      exact (lintegral_prod (fun z : B × D => f ((a, c), z))
        (by fun_prop : AEMeasurable (fun z : B × D => f ((a, c), z)) (ν.prod η))).symm

/-- The single-node split is compatible with two fresh independent subtree innovations. -/
theorem SADensity.splitQuantile_subtree_law {p : ℝ → ℝ} (hp : SADensity p)
    {E : Type*} [MeasurableSpace E] (η : Measure E) [IsProbabilityMeasure η] :
    ((hp.sumDensity.law : Measure ℝ).prod (saUniform.prod (η.prod η))).map
      (fun z : ℝ × (ℝ × E × E) =>
        ((saSplitQuantile hp z.1 z.2.1, z.2.2.1),
          (z.1 - saSplitQuantile hp z.1 z.2.1, z.2.2.2))) =
        ((hp.law : Measure ℝ).prod η).prod ((hp.law : Measure ℝ).prod η) := by
  let f : ℝ × ℝ → ℝ × ℝ := fun z => (saSplitQuantile hp z.1 z.2,
    z.1 - saSplitQuantile hp z.1 z.2)
  have hf : Measurable f := hp.measurable_splitQuantile.prodMk
    (measurable_fst.sub hp.measurable_splitQuantile)
  have hq : Measurable (fun z : ℝ × (ℝ × E × E) => saSplitQuantile hp z.1 z.2.1) :=
    hp.measurable_splitQuantile.comp (f := fun z : ℝ × (ℝ × E × E) => (z.1, z.2.1))
      (by fun_prop)
  have hms : Measurable (fun z : ℝ × (ℝ × E × E) =>
      ((saSplitQuantile hp z.1 z.2.1, z.2.2.1),
        (z.1 - saSplitQuantile hp z.1 z.2.1, z.2.2.2))) :=
    (hq.prodMk measurable_snd.snd.fst).prodMk
    ((measurable_fst.sub hq).prodMk measurable_snd.snd.snd)
  have hassoc := prodAssoc_prod (μ := (hp.sumDensity.law : Measure ℝ))
    (ν := saUniform) (τ := η.prod η)
  rw [← hassoc, Measure.map_map hms MeasurableEquiv.prodAssoc.measurable]
  have hprod := map_prod_map ((hp.sumDensity.law : Measure ℝ).prod saUniform) (η.prod η)
    hf measurable_id
  rw [hp.splitQuantile_pair_law, Measure.map_id] at hprod
  have hshuffle := sa_map_prod_four_shuffle (hp.law : Measure ℝ) (hp.law : Measure ℝ) η η
  rw [hprod, Measure.map_map (by fun_prop) (hf.prodMap measurable_id)] at hshuffle
  exact hshuffle

/-- The left child's total and its future noise have their exact product law. -/
theorem SADensity.splitQuantile_subtree_left_law {p : ℝ → ℝ} (hp : SADensity p)
    {E : Type*} [MeasurableSpace E] (η : Measure E) [IsProbabilityMeasure η] :
    ((hp.sumDensity.law : Measure ℝ).prod (saUniform.prod (η.prod η))).map
      (fun z : ℝ × (ℝ × E × E) => (saSplitQuantile hp z.1 z.2.1, z.2.2.1)) =
        (hp.law : Measure ℝ).prod η := by
  have he := congrArg (fun μ : Measure ((ℝ × E) × (ℝ × E)) => μ.map Prod.fst)
    (hp.splitQuantile_subtree_law η)
  rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod, measure_univ,
    one_smul] at he
  exact he

/-- The right child's total and its future noise have their exact product law. -/
theorem SADensity.splitQuantile_subtree_right_law {p : ℝ → ℝ} (hp : SADensity p)
    {E : Type*} [MeasurableSpace E] (η : Measure E) [IsProbabilityMeasure η] :
    ((hp.sumDensity.law : Measure ℝ).prod (saUniform.prod (η.prod η))).map
      (fun z : ℝ × (ℝ × E × E) => (z.1 - saSplitQuantile hp z.1 z.2.1, z.2.2.2)) =
        (hp.law : Measure ℝ).prod η := by
  have he := congrArg (fun μ : Measure ((ℝ × E) × (ℝ × E)) => μ.map Prod.snd)
    (hp.splitQuantile_subtree_law η)
  rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod, measure_univ,
    one_smul] at he
  exact he

end

end PGM
