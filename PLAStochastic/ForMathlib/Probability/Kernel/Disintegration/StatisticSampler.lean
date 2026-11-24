import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# WP5: measurable lifting from block totals to original increments

Disintegration and one fresh uniform variable reconstruct an original sample
given any measurable statistic. The joint graph law is preserved exactly, so
the reconstructed statistic equals the prescribed total almost surely.
-/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Filter Function
open scoped unitInterval ENNReal

/-- Randomizing a regular conditional distribution reconstructs the entire joint law. -/
theorem sa_exists_joint_sampler {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    [StandardBorelSpace E] [Nonempty E] (ρ : Measure (A × E)) [IsProbabilityMeasure ρ] :
    ∃ f : A → I → E, Measurable (uncurry f) ∧
      (ρ.fst.prod (volume : Measure I)).map (fun z => (z.1, f z.1 z.2)) = ρ := by
  obtain ⟨f, hf, hmap⟩ := ρ.condKernel.exists_measurable_map_eq_unitInterval
  refine ⟨f, hf, ?_⟩
  have hm : Measurable (fun z : A × I => (z.1, f z.1 z.2)) := measurable_fst.prodMk hf
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hm]
  have hgm : Measurable (fun z : A × I => g (z.1, f z.1 z.2)) := hg.comp hm
  rw [lintegral_prod _ hgm.aemeasurable]
  have hd : ρ.fst ⊗ₘ ρ.condKernel = ρ := ρ.disintegrate ρ.condKernel
  conv_rhs => rw [← hd]
  rw [Measure.lintegral_compProd hg]
  apply lintegral_congr
  intro a
  have hga : Measurable (fun x : E => g (a, x)) := hg.comp measurable_prodMk_left
  rw [← hmap a, lintegral_map hga hf.of_uncurry_left]

/-- A sampler conditioned on a measurable statistic preserves the original law and statistic. -/
theorem sa_exists_map_sampler {A E : Type*} [MeasurableSpace A] [MeasurableEq A]
    [MeasurableSpace E]
    [StandardBorelSpace E] [Nonempty E] (μ : Measure E) [IsProbabilityMeasure μ]
    {S : E → A} (hS : Measurable S) :
    ∃ f : A → I → E, Measurable (uncurry f) ∧
      ((μ.map S).prod (volume : Measure I)).map (fun z => (z.1, f z.1 z.2)) =
        μ.map (fun x => (S x, x)) ∧
      ((μ.map S).prod (volume : Measure I)).map (uncurry f) = μ ∧
      (∀ᵐ z ∂((μ.map S).prod (volume : Measure I)), S (f z.1 z.2) = z.1) := by
  let ρ : Measure (A × E) := μ.map (fun x => (S x, x))
  have hm : Measurable (fun x => (S x, x)) := hS.prodMk measurable_id
  have : IsProbabilityMeasure ρ := isProbabilityMeasure_map hm.aemeasurable
  have hfst : ρ.fst = μ.map S := by
    change (μ.map (fun x => (S x, x))).map Prod.fst = μ.map S
    rw [Measure.map_map measurable_fst hm]
    rfl
  obtain ⟨f, hf, hgraph⟩ := sa_exists_joint_sampler ρ
  rw [hfst] at hgraph
  have hmf : Measurable (fun z : A × I => (z.1, f z.1 z.2)) := measurable_fst.prodMk hf
  have hE : MeasurableSet {z : A × E | S z.2 = z.1} :=
    measurableSet_eq_fun (hS.comp measurable_snd) measurable_fst
  refine ⟨f, hf, hgraph, ?_, ?_⟩
  · have h := congrArg (fun η : Measure (A × E) => η.map Prod.snd) hgraph
    change _ = (μ.map (fun x => (S x, x))).map Prod.snd at h
    rw [Measure.map_map measurable_snd hmf, Measure.map_map measurable_snd hm] at h
    exact h.trans Measure.map_id
  · have hρ : ∀ᵐ z ∂ρ, S z.2 = z.1 := by
      apply (ae_map_iff hm.aemeasurable hE).2
      exact ae_of_all _ fun _ => rfl
    rw [← hgraph] at hρ
    exact (ae_map_iff hmf.aemeasurable hE).1 hρ

/-- A block-total sampler preserves both the original vector law and its exact total. -/
theorem sa_exists_statistic_sampler {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] [Nonempty E] (μ : Measure E) [IsProbabilityMeasure μ]
    {S : E → ℝ} (hS : Measurable S) :
    ∃ f : ℝ → I → E, Measurable (uncurry f) ∧
      ((μ.map S).prod (volume : Measure I)).map (fun z => (z.1, f z.1 z.2)) =
        μ.map (fun x => (S x, x)) ∧
      ((μ.map S).prod (volume : Measure I)).map (uncurry f) = μ ∧
      (∀ᵐ z ∂((μ.map S).prod (volume : Measure I)), S (f z.1 z.2) = z.1) :=
  sa_exists_map_sampler μ hS

end

end PGM
