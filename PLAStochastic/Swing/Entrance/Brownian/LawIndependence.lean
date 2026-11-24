import PLAStochastic.Swing.Entrance.Brownian.Measurability

/-!
# Law independence of the Brownian entrance quantities

The continuous-path representative `processPath B` of any real Brownian motion on any
probability space has one and the same law on the Borel path space `C(ℝ, ℝ)`: its observations
at the rational times have the Brownian finite-dimensional laws, a projective limit determines
the law of a countable observation vector, and these observations form a measurable embedding
of the path space.

Since the entrance quantities agree almost surely with measurable path functionals, the joint
law of `(σ, m_*, s, I)` and in particular `P(I > 0)` do not depend on the Brownian motion. The
selection probability `entranceSelectionProb`, defined through the canonical Brownian motion,
is therefore the value of `P(I > 0)` for every Brownian motion.
-/

open MeasureTheory ProbabilityTheory Set Filter BrownianAffine
open scoped ENNReal NNReal Topology

namespace SwingRepair

noncomputable section

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  {ν : Measure Ω'} {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ω' → ℝ}

/-- Countable Brownian observation vectors have the same law on any two probability spaces. -/
theorem identDistrib_brownian_countable_observations {ι : Type*} [Countable ι]
    (hB : IsPreBrownianReal B μ) (hC : IsPreBrownianReal C ν) (t : ι → ℝ≥0) :
    IdentDistrib (fun ω i => B (t i) ω) (fun ω i => C (t i) ω) μ ν := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have : IsProbabilityMeasure ν := hC.isGaussianProcess.isProbabilityMeasure
  have hBm : AEMeasurable (fun ω i => B (t i) ω) μ :=
    aemeasurable_pi_lambda _ (fun i => hB.aemeasurable (t i))
  have hCm : AEMeasurable (fun ω i => C (t i) ω) ν :=
    aemeasurable_pi_lambda _ (fun i => hC.aemeasurable (t i))
  refine ⟨hBm, hCm, ?_⟩
  have hfdd : ∀ I : Finset ι, μ.map (fun ω => I.restrict (fun i => B (t i) ω)) =
      ν.map (fun ω => I.restrict (fun i => C (t i) ω)) := by
    intro I
    classical
    let J := I.image t
    let project : (J → ℝ) → I → ℝ := fun z i =>
      z ⟨t i.1, Finset.mem_image.mpr ⟨i.1, i.property, rfl⟩⟩
    have hp : Measurable project := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    exact (((hB.hasLaw J).identDistrib (hC.hasLaw J)).comp hp).map_eq
  have h1 := isProjectiveLimit_map (X := fun i ω => B (t i) ω) hBm
  have h2 := isProjectiveLimit_map (X := fun i ω => C (t i) ω) hCm
  have h1' : IsProjectiveLimit (μ.map (fun ω i => B (t i) ω))
      (fun I : Finset ι => ν.map (fun ω => I.restrict (fun i => C (t i) ω))) := by
    intro I
    exact (h1 I).trans (hfdd I)
  exact h1'.unique h2

omit [MeasurableSpace Ω] in
theorem processPath_apply_real {ω : Ω} (hω : Continuous (B · ω)) (t : ℝ) :
    processPath B ω t = B t.toNNReal ω := by
  unfold processPath
  exact ContinuousMap.mkD_apply_of_continuous (hω.comp continuous_real_toNNReal)

/-- The continuous Brownian path has the same law for every Brownian motion. -/
theorem identDistrib_processPath (hB : IsBrownianReal B μ) (hC : IsBrownianReal C ν) :
    IdentDistrib (processPath B) (processPath C) μ ν := by
  have hobs := identDistrib_brownian_countable_observations hB.toIsPreBrownianReal
    hC.toIsPreBrownianReal (fun q : ℚ => (q : ℝ).toNNReal)
  have hB' : (fun ω => fullPathObservations (processPath B ω)) =ᵐ[μ]
      (fun ω (q : ℚ) => B (q : ℝ).toNNReal ω) := by
    filter_upwards [hB.cont] with ω hω
    funext q
    exact processPath_apply_real hω q
  have hC' : (fun ω => fullPathObservations (processPath C ω)) =ᵐ[ν]
      (fun ω (q : ℚ) => C (q : ℝ).toNNReal ω) := by
    filter_upwards [hC.cont] with ω hω
    funext q
    exact processPath_apply_real hω q
  have hBm : AEMeasurable (fun ω => fullPathObservations (processPath B ω)) μ :=
    measurableEmbedding_fullPathObservations.measurable.comp_aemeasurable
      (aemeasurable_processPath hB)
  have hCm : AEMeasurable (fun ω => fullPathObservations (processPath C ω)) ν :=
    measurableEmbedding_fullPathObservations.measurable.comp_aemeasurable
      (aemeasurable_processPath hC)
  have h2 : IdentDistrib (fun ω => fullPathObservations (processPath B ω))
      (fun ω => fullPathObservations (processPath C ω)) μ ν :=
    ((IdentDistrib.of_ae_eq hBm hB').trans hobs).trans (IdentDistrib.of_ae_eq hCm hC').symm
  obtain ⟨F, hF, hFeq⟩ := measurableEmbedding_fullPathObservations.exists_measurable_extend
    (g := id) measurable_id (fun _ => ⟨(0 : C(ℝ, ℝ))⟩)
  have hid : ∀ f, F (fullPathObservations f) = f := fun f => congrFun hFeq f
  have h3 := h2.comp hF
  simpa only [Function.comp_def, hid] using h3

/-- The quadruple `(σ, m_*, s, I)` of the Brownian entrance. -/
def entranceData (f : C(ℝ, ℝ)) : ℝ × ℝ × ℝ × ℝ :=
  (entrancePinch f, entranceSlope f, entranceSign f, entranceArea f)

/-- Its measurable version on the path space. -/
def entranceDataM (f : C(ℝ, ℝ)) : ℝ × ℝ × ℝ × ℝ := (pinchM f, slopeM f, signM f, areaM f)

theorem measurable_entranceDataM : Measurable entranceDataM :=
  measurable_pinchM.prodMk (measurable_slopeM.prodMk (measurable_signM.prodMk measurable_areaM))

theorem entranceData_eq_entranceDataM {f : C(ℝ, ℝ)} (hf : |f 0| < 1) :
    entranceData f = entranceDataM f := by
  simp only [entranceData, entranceDataM, entrancePinch_eq_pinchM hf, entranceSlope_eq_slopeM hf,
    entranceSign_eq_signM hf, entranceArea_eq_areaM hf]

theorem entranceData_ae_eq (hB : IsBrownianReal B μ) :
    (fun ω => entranceData (processPath B ω)) =ᵐ[μ]
      (fun ω => entranceDataM (processPath B ω)) := by
  filter_upwards [processPath_abs_zero_lt_ae hB] with ω hω
  exact entranceData_eq_entranceDataM hω

theorem aemeasurable_entranceData (hB : IsBrownianReal B μ) :
    AEMeasurable (fun ω => entranceData (processPath B ω)) μ :=
  (measurable_entranceDataM.comp_aemeasurable (aemeasurable_processPath hB)).congr
    (entranceData_ae_eq hB).symm

/-- The joint law of `(σ, m_*, s, I)` is the same for every Brownian motion. -/
theorem identDistrib_entranceData (hB : IsBrownianReal B μ) (hC : IsBrownianReal C ν) :
    IdentDistrib (fun ω => entranceData (processPath B ω))
      (fun ω => entranceData (processPath C ω)) μ ν := by
  have h := (identDistrib_processPath hB hC).comp measurable_entranceDataM
  exact ((IdentDistrib.of_ae_eq (aemeasurable_entranceData hB) (entranceData_ae_eq hB)).trans
    h).trans (IdentDistrib.of_ae_eq (aemeasurable_entranceData hC) (entranceData_ae_eq hC)).symm

theorem identDistrib_entranceArea (hB : IsBrownianReal B μ) (hC : IsBrownianReal C ν) :
    IdentDistrib (fun ω => entranceArea (processPath B ω))
      (fun ω => entranceArea (processPath C ω)) μ ν :=
  (identDistrib_entranceData hB hC).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))

/-- The selection probability is `P(I > 0)` for every Brownian motion on every probability
space. -/
theorem measureReal_entranceArea_pos (hB : IsBrownianReal B μ) :
    μ.real {ω | 0 < entranceArea (processPath B ω)} = entranceSelectionProb := by
  have h := (identDistrib_entranceArea hB isBrownianReal_canonicalBrownian).measure_mem_eq
    (measurableSet_Ioi (a := (0 : ℝ)))
  rw [entranceSelectionProb, measureReal_def, measureReal_def]
  exact congrArg ENNReal.toReal h

end

end SwingRepair
