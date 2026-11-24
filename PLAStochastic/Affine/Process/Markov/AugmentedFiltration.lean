import PLAStochastic.Affine.Process.PathLaw.PathSpace
import PLAStochastic.Brownian.Markov.StrongMarkov

/-!
# A measurable continuous version and the augmented natural filtration

The augmentation includes ambient measurable sets which agree almost surely
with a natural-filtration event. The ambient measure and sample space stay
unchanged. A measurable random continuous path is chosen only after proving
measurability of the actual whole path through countably many observations.
Consequently the version agrees at every time on one common full-measure set.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

instance fullPathMeasurableSpace : MeasurableSpace C(ℝ, ℝ) := borel C(ℝ, ℝ)
instance fullPathBorelSpace : BorelSpace C(ℝ, ℝ) := ⟨rfl⟩

def fullPathObservations (f : C(ℝ, ℝ)) : ℚ → ℝ := fun q => f q

theorem measurableEmbedding_fullPathObservations : MeasurableEmbedding fullPathObservations := by
  have hc : Continuous fullPathObservations := continuous_pi (fun q => continuous_eval_const (q : ℝ))
  apply hc.measurableEmbedding
  intro f g h
  apply DFunLike.ext'
  exact (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).equalizer f.continuous g.continuous
    (funext (fun q => congrFun h q))

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem aemeasurable_processPath (hB : IsBrownianReal B μ) :
    AEMeasurable (processPath B) μ := by
  apply measurableEmbedding_fullPathObservations.aemeasurable_comp_iff.mp
  apply (aemeasurable_pi_lambda _ (fun q : ℚ => hB.aemeasurable (q : ℝ).toNNReal)).congr
  filter_upwards [hB.cont] with ω hω
  funext q
  change B (q : ℝ).toNNReal ω = processPath B ω q
  have hc : Continuous (fun t : ℝ => B t.toNNReal ω) := hω.comp continuous_real_toNNReal
  exact (ContinuousMap.mkD_apply_of_continuous hc).symm

/-- A globally measurable random continuous path, not merely coordinatewise
measurable representatives with unrelated exceptional sets. -/
def continuousBrownianPath (hB : IsBrownianReal B μ) : Ω → C(ℝ, ℝ) :=
  (aemeasurable_processPath hB).mk (processPath B)

theorem measurable_continuousBrownianPath (hB : IsBrownianReal B μ) :
    Measurable (continuousBrownianPath hB) := (aemeasurable_processPath hB).measurable_mk

theorem continuousBrownianPath_ae_eq (hB : IsBrownianReal B μ) :
    continuousBrownianPath hB =ᵐ[μ] processPath B := (aemeasurable_processPath hB).ae_eq_mk.symm

/-- Equality is simultaneous in all times, hence valid at arbitrary random times. -/
theorem continuousBrownianPath_all_times_ae_eq (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, continuousBrownianPath hB ω t = B t ω := by
  filter_upwards [continuousBrownianPath_ae_eq hB, hB.cont] with ω heq hc
  intro t
  rw [heq]
  exact processPath_apply_of_continuous hc t

/-- Completion inside the ambient sigma-algebra; no new measure is introduced. -/
def augmentedFiltration (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) : Filtration ℝ≥0 mΩ where
  seq t := mΩ ⊓ eventuallyMeasurableSpace (ℱ t) (ae μ)
  mono' := by
    intro s t hst A hA
    exact ⟨hA.1, by
      obtain ⟨D, hD, heq⟩ := hA.2
      exact ⟨D, ℱ.mono hst _ hD, heq⟩⟩
  le' _ := inf_le_left

theorem measurableSet_augmentedFiltration_iff (ℱ : Filtration ℝ≥0 mΩ) (t : ℝ≥0) (A : Set Ω) :
    MeasurableSet[augmentedFiltration ℱ μ t] A ↔
      MeasurableSet A ∧ ∃ D, MeasurableSet[ℱ t] D ∧ A =ᵐ[μ] D := Iff.rfl

def augmentedBrownianFiltration (hB : IsPreBrownianReal B μ) : Filtration ℝ≥0 mΩ :=
  augmentedFiltration (brownianNaturalFiltration hB) μ

/-- Deterministic independence survives augmentation because its events are
almost surely equal to genuine natural-filtration events. -/
theorem indep_augmentedFiltration {ℱ : Filtration ℝ≥0 mΩ} {mOther : MeasurableSpace Ω}
    {t : ℝ≥0} (h : @Indep Ω mOther (ℱ t) mΩ μ) :
    @Indep Ω mOther (@augmentedFiltration Ω mΩ ℱ μ t) mΩ μ := by
  apply (@Indep_iff Ω mOther (@augmentedFiltration Ω mΩ ℱ μ t) mΩ μ).mpr
  intro C A hC hA
  obtain ⟨D, hD, hAD⟩ := hA.2
  rw [measure_congr (ae_eq_set_inter EventuallyEq.rfl hAD), measure_congr hAD]
  exact (@Indep_iff Ω mOther (ℱ t) mΩ μ).mp h C D hC hD

theorem continuous_unitPath_in_path (T : ℝ) : Continuous (fun f : C(ℝ, ℝ) => unitPath f T) :=
  ContinuousMap.continuous_precomp ⟨fun u : Icc (0 : ℝ) 1 => T * (u : ℝ), by fun_prop⟩

theorem measurable_continuousBrownianError (hB : IsBrownianReal B μ) (T : ℝ≥0) :
    Measurable (fun ω => anchoredTimeError (continuousBrownianPath hB ω) T) :=
  ((continuous_anchoredError 1).comp (continuous_unitPath_in_path T)).measurable.comp
    (measurable_continuousBrownianPath hB)

/-- At time T the sampled error of the measurable version uses observations
only from [0,T], so it is measurable in the raw natural filtration. -/
theorem measurable_sampledBrownianError_natural (hB : IsPreBrownianReal B μ) (T : ℝ≥0) :
    Measurable[brownianNaturalFiltration hB T]
      (fun ω => sampledAnchoredError (sampledProcess (measurableBrownian hB) T ω)) := by
  refine measurable_sampledAnchoredError.comp
    (@measurable_pi_lambda Ω ErrorSample (fun _ => ℝ) (brownianNaturalFiltration hB T)
      (fun _ => inferInstance) _ (fun s => ?_))
  have ht : T * errorSampleTime s ≤ T := by
    apply mul_le_of_le_one_right T.property
    exact s.1.property.2
  have hm := (Filtration.stronglyAdapted_natural
    (fun t => (measurable_measurableBrownian hB t).stronglyMeasurable) (T * errorSampleTime s)).measurable
  exact hm.mono (brownianNaturalFiltration hB |>.mono ht) le_rfl

/-- The actual continuous fitting error is adapted in the augmented filtration.
Both ambient measurability and the natural-filtration representative are proved. -/
theorem adapted_continuousBrownianError (hB : IsBrownianReal B μ) :
    Adapted (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (fun T ω => anchoredTimeError (continuousBrownianPath hB ω) T) := by
  intro T A hA
  refine ⟨measurable_continuousBrownianError hB T hA, ?_⟩
  let Y := fun ω => sampledAnchoredError (sampledProcess (measurableBrownian hB.toIsPreBrownianReal) T ω)
  refine ⟨Y ⁻¹' A, measurable_sampledBrownianError_natural hB.toIsPreBrownianReal T hA, ?_⟩
  have heq : (fun ω => anchoredTimeError (continuousBrownianPath hB ω) T) =ᵐ[μ] Y := by
    filter_upwards [continuousBrownianPath_ae_eq hB, hB.cont,
      measurableBrownian_countable_ae_eq hB.toIsPreBrownianReal (fun s : ErrorSample => T * errorSampleTime s)]
      with ω hp hc hs
    rw [hp]
    change anchoredError (unitPath (processPath B ω) T) = Y ω
    rw [← sampledAnchoredError_eq]
    congr 1
    funext s
    exact (unitPath_processPath_sample hc T s).trans (hs s).symm
  exact heq.preimage A

end BrownianAffine
