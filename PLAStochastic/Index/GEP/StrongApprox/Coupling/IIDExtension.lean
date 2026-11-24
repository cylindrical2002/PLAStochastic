import PLAStochastic.ForMathlib.Probability.Kernel.Disintegration.StatisticSampler
import PLAStochastic.Index.GEP.Universality.StrongApproxInterface
import Mathlib.Probability.Independence.InfinitePi

/-! # Lifting a coupling of statistics to the original sample laws

Applied to finite prefixes of iid sequences, this extends a finite coupling to
infinite sequences while preserving its entire finite-dimensional joint law.
-/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Function
open scoped unitInterval ENNReal

/-- Any coupling of two statistics lifts to a coupling of the original laws. -/
theorem sa_exists_coupling_lift {A B E F : Type*}
    [MeasurableSpace A] [MeasurableEq A] [MeasurableSpace B] [MeasurableEq B]
    [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    [MeasurableSpace F] [StandardBorelSpace F] [Nonempty F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {S : E → A} {T : F → B} (hS : Measurable S) (hT : Measurable T)
    (ρ : Measure (A × B)) [IsProbabilityMeasure ρ]
    (hleft : ρ.fst = μ.map S) (hright : ρ.snd = ν.map T) :
    ∃ π : Measure (E × F), IsProbabilityMeasure π ∧ π.fst = μ ∧ π.snd = ν ∧
      π.map (Prod.map S T) = ρ := by
  obtain ⟨f, hf, _, hflaw, hfstat⟩ := sa_exists_map_sampler μ hS
  obtain ⟨g, hg, _, hglaw, hgstat⟩ := sa_exists_map_sampler ν hT
  let P : Measure (((A × B) × I) × I) := (ρ.prod volume).prod volume
  let u : ((A × B) × I) × I → A × I := fun z => (z.1.1.1, z.1.2)
  let v : ((A × B) × I) × I → B × I := fun z => (z.1.1.2, z.2)
  have hu : Measurable u := measurable_fst.fst.fst.prodMk measurable_fst.snd
  have hv : Measurable v := measurable_fst.fst.snd.prodMk measurable_snd
  have hulaw : P.map u = (μ.map S).prod volume := by
    have h := map_prod_map ρ (volume : Measure I) measurable_fst measurable_id
    change ρ.fst.prod ((volume : Measure I).map id) = _ at h
    rw [hleft, map_id] at h
    calc
      P.map u = ((ρ.prod (volume : Measure I)).map (Prod.map Prod.fst id)) := by
        change P.map (Prod.map Prod.fst id ∘ Prod.fst) = _
        rw [← Measure.map_map (measurable_fst.prodMap measurable_id) measurable_fst]
        simp [P]
      _ = _ := h.symm
  have hvlaw : P.map v = (ν.map T).prod volume := by
    have h := map_prod_map (ρ.prod (volume : Measure I)) (volume : Measure I)
      (measurable_fst.snd : Measurable (fun z : (A × B) × I => z.1.2)) measurable_id
    have he : (ρ.prod (volume : Measure I)).map (fun z : (A × B) × I => z.1.2) =
        ρ.snd := by
      change (ρ.prod (volume : Measure I)).map (Prod.snd ∘ Prod.fst) = ρ.snd
      rw [← Measure.map_map measurable_snd measurable_fst]
      simp [Measure.snd]
    rw [he, hright, map_id] at h
    exact h.symm
  have hf' : Measurable (uncurry f ∘ u) := hf.comp hu
  have hg' : Measurable (uncurry g ∘ v) := hg.comp hv
  let H : ((A × B) × I) × I → E × F := fun z => (f (u z).1 (u z).2, g (v z).1 (v z).2)
  have hH : Measurable H := hf'.prodMk hg'
  have hP : IsProbabilityMeasure P := inferInstanceAs
    (IsProbabilityMeasure ((ρ.prod (volume : Measure I)).prod (volume : Measure I)))
  refine ⟨P.map H, isProbabilityMeasure_map hH.aemeasurable, ?_, ?_, ?_⟩
  · change (P.map H).map Prod.fst = μ
    rw [Measure.map_map measurable_fst hH]
    change P.map (uncurry f ∘ u) = μ
    rw [← Measure.map_map hf hu, hulaw, hflaw]
  · change (P.map H).map Prod.snd = ν
    rw [Measure.map_map measurable_snd hH]
    change P.map (uncurry g ∘ v) = ν
    rw [← Measure.map_map hg hv, hvlaw, hglaw]
  · have hfae : ∀ᵐ z ∂P, S (f (u z).1 (u z).2) = (u z).1 := by
      rw [← hulaw] at hfstat
      exact (ae_map_iff hu.aemeasurable
        (measurableSet_eq_fun (hS.comp hf) measurable_fst)).1 hfstat
    have hgae : ∀ᵐ z ∂P, T (g (v z).1 (v z).2) = (v z).1 := by
      rw [← hvlaw] at hgstat
      exact (ae_map_iff hv.aemeasurable
        (measurableSet_eq_fun (hT.comp hg) measurable_fst)).1 hgstat
    rw [Measure.map_map (hS.prodMap hT) hH]
    calc
      P.map (Prod.map S T ∘ H) = P.map (fun z => z.1.1) := by
        apply Measure.map_congr
        filter_upwards [hfae, hgae] with z hz₁ hz₂
        exact Prod.ext hz₁ hz₂
      _ = ρ := by
        change P.map (Prod.fst ∘ Prod.fst) = ρ
        rw [← Measure.map_map measurable_fst measurable_fst]
        simp [P]

/-- The first `N` coordinates of the infinite iid law have the finite product law. -/
theorem sa_iidLaw_prefix (ν : ProbabilityMeasure ℝ) (N : ℕ) :
    (iidLaw ν).map (fun x : ℕ → ℝ => fun i : Fin N => x i) =
      Measure.pi (fun _ : Fin N => (ν : Measure ℝ)) := by
  rw [iidLaw, Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
    Measure.infinitePi_eq_pi]

/-- Every finite iid coupling has an infinite iid extension with exactly the same prefix law. -/
theorem sa_exists_iid_coupling_extension (ν ρ : ProbabilityMeasure ℝ) (N : ℕ)
    (π : Measure ((Fin N → ℝ) × (Fin N → ℝ))) [IsProbabilityMeasure π]
    (hleft : π.fst = Measure.pi (fun _ : Fin N => (ν : Measure ℝ)))
    (hright : π.snd = Measure.pi (fun _ : Fin N => (ρ : Measure ℝ))) :
    ∃ πext : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure πext ∧
      πext.fst = iidLaw ν ∧ πext.snd = iidLaw ρ ∧
      πext.map (Prod.map (fun x : ℕ → ℝ => fun i : Fin N => x i)
        (fun x : ℕ → ℝ => fun i : Fin N => x i)) = π := by
  exact sa_exists_coupling_lift (iidLaw ν) (iidLaw ρ)
    (S := fun x : ℕ → ℝ => fun i : Fin N => x i)
    (T := fun x : ℕ → ℝ => fun i : Fin N => x i)
    (measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ))
    (measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)) π
    (hleft.trans (sa_iidLaw_prefix ν N).symm) (hright.trans (sa_iidLaw_prefix ρ N).symm)

end

end PGM
