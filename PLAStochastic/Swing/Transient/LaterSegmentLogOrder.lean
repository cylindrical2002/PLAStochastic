import PLAStochastic.Swing.Transient.MeanPassage
import PLAStochastic.Swing.Transient.SlopeAlgebra
import PLAStochastic.Swing.ConstantEvaluation.KernelRewardIteration
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! # Theorem 4.4 (`thm:transientconvergence`) for the actual stream

`E L_{k,E} = Θ_k(E log E)` for every fixed `k ≥ 3`, and

`limsup_{E→∞} |E L_{k,E}/(E log E) - γ_Swing| ≤ B (3/4)^{k-3}`

with a constant `B` independent of `k`.

The Lean segment index is shifted by one: `nativeRecordingDurationNat X E j` is the
segment started from the margin law `ρ_{j,E}`, so the paper's `L_{k,E}` is the
Lean segment `k-1`; the theorem is stated for the segments `m+2`, `m ≥ 0`, i.e.
`k = m+3`, and the rate is `(3/4)^m`.

**The subsequence argument.**  Both the lower bound and the geometric bound are
`∀ᶠ E in atTop` statements about `f(E) = E L/(E log E)`.  Each is proved by
contradiction: if `f(E) ∉ U` frequently for the relevant open set `U`, restrict
to the filter `atTop ⊓ 𝓟 {f ∉ U}`, extract a weak cluster point `ν` of the
first-restart margin laws (tightness, `exists_clusterPt_nativeTransientMarginProb`),
pass to the further restriction on which `ρ_{1,E} ⇒ ν`; the mean passage
(`nativeRecordingDurationNat_normalizedMean_tendsto`) then gives
`f(E) → ∫ v d(νK^{m+1})`, which lies in `U` by the slope algebra
(`transient_coefficient_geometric_bound`, `exists_transient_coefficient_lower_bound`),
so `f(E) ∈ U` eventually on a nontrivial filter on which `f(E) ∉ U` — a contradiction.
The restricted filters are countably generated because the weak topology on
`ProbabilityMeasure ℝ` is metrizable.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open LeadingCoefficient KernelLimit SlopeEvaluation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- `E L/(E log E)` for the actual segment started from `ρ_{j,E}`. -/
def transientNormalizedMean (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E : ℝ) (j : ℕ) : ℝ :=
  (∫ ω, (nativeRecordingDurationNat X E j ω : ℝ) ∂μ) / (E * Real.log E)

/-! ### The upper bound `E L_{k,E} = O_k(E log E)` -/

theorem transientNormalizedMean_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (m : ℕ) :
    transientNormalizedMean X μ E (m+1) ≤
      transientRewardGrowthConstant * (1 + transientMarginMomentBound m 1) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEpos : 0 < E := lt_of_lt_of_le stationaryScaleThreshold_pos hE
  have hEexp : Real.exp 1 ≤ E := (le_max_right _ _).trans ((le_max_left _ _).trans hE)
  have hρ : IsProbabilityMeasure (nativeTransientMarginLaw X μ E (m+1)) :=
    nativeTransientMarginLaw_isProbability hX E (m+1)
  obtain ⟨habs, hM⟩ := nativeTransientMarginLaw_abs_le hX hi hG hE m
  unfold transientNormalizedMean
  rw [nativeRecordingDurationNat_normalizedMean_eq_margin_integral hX hi hG hEpos (m+1)]
  have hA := transientRewardGrowthConstant_nonneg
  have hE1 : (1 : ℝ) ≤ E := by
    have : (1 : ℝ) ≤ Real.exp 1 := by norm_num
    exact this.trans hEexp
  calc (∫ r, normalizedFrozenMean X μ E r ∂(nativeTransientMarginLaw X μ E (m+1)))
      ≤ ∫ r, transientRewardGrowthConstant * (1 + |r|) ∂(nativeTransientMarginLaw X μ E (m+1)) := by
        refine integral_mono_of_nonneg
          (ae_of_all _ fun r => normalizedFrozenMean_nonneg hX hi hG hE1)
          (((integrable_const _).add habs).const_mul _)
          (ae_of_all _ fun r => normalizedFrozenMean_le_growth hX hi hG hEexp r)
    _ = transientRewardGrowthConstant * (1 + ∫ r, |r| ∂(nativeTransientMarginLaw X μ E (m+1))) := by
        rw [integral_const_mul, integral_add (integrable_const _) habs, integral_const,
          probReal_univ, one_smul]
    _ ≤ transientRewardGrowthConstant * (1 + transientMarginMomentBound m 1) := by gcongr

/-! ### The subsequence principle -/

/-- **The subsequence principle for Theorem 4.4.**  If every possible transient
coefficient `∫ v d(νK^{m+1})` — over all entrance laws `ν` with the uniform
first moment of Lemma G.1 — lies in an open set `U`, then the normalised means of
the `(m+2)`-nd segments lie in `U` for all large budgets. -/
theorem transient_eventually_mem_of_limits [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) (m : ℕ) {U : Set ℝ} (hU : IsOpen U)
    (hΛ : ∀ ν : ProbabilityMeasure ℝ, Integrable (fun r : ℝ => |r|) (ν : Measure ℝ) →
      (∫ r, |r| ∂(ν : Measure ℝ)) ≤ transientMarginMomentBound 0 1 →
      Integrable (marginLeadingReward X μ)
        ((fun σ : Measure ℝ => swingMarginKernel X μ ∘ₘ σ)^[m+1] (ν : Measure ℝ)) →
      (∫ r, marginLeadingReward X μ r ∂
        ((fun σ : Measure ℝ => swingMarginKernel X μ ∘ₘ σ)^[m+1] (ν : Measure ℝ))) ∈ U) :
    ∀ᶠ E in atTop, transientNormalizedMean X μ E (m+2) ∈ U := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let : IsMarkovKernel (swingMarginKernel X μ) := swingMarginKernel_isMarkov hX hi hG
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  set l : Filter ℝ := atTop ⊓ 𝓟 {E | transientNormalizedMean X μ E (m+2) ∉ U} with hldef
  have hlne : l.NeBot := Filter.frequently_iff_neBot.mp hcon
  set budget : ℝ → ℝ := fun E => max E stationaryScaleThreshold with hbdef
  have hbudget : ∀ E, stationaryScaleThreshold ≤ budget E := fun E => le_max_right _ _
  have hbudget_top : Tendsto budget l atTop :=
    (tendsto_atTop_mono (fun E => le_max_left E _) tendsto_id).mono_left inf_le_left
  obtain ⟨ν, hν⟩ := exists_clusterPt_nativeTransientMarginProb hX hi hG (l := l) hbudget
  set u : ℝ → ProbabilityMeasure ℝ := fun E => nativeTransientMarginProb μ hX (budget E) 1 with hudef
  set l' : Filter ℝ := comap u (𝓝 ν) ⊓ l with hl'def
  have hl'ne : l'.NeBot := by
    have h1 : (𝓝 ν ⊓ map u l).NeBot := hν
    rw [← Filter.push_pull'] at h1
    exact (map_neBot_iff u).mp h1
  have hl'cg : l'.IsCountablyGenerated := inferInstance
  have hl'le : l' ≤ l := inf_le_right
  have hu : Tendsto u l' (𝓝 ν) := tendsto_comap.mono_left inf_le_left
  have hbudget_top' : Tendsto budget l' atTop := hbudget_top.mono_left hl'le
  -- the first moment of the cluster point
  have hνabs := limit_integral_le_of_forall_integral_le (g := fun x : ℝ => |x|) hu continuous_abs
    (fun x => abs_nonneg x)
    (fun E => (nativeTransientMarginLaw_abs_le hX hi hG (hbudget E) 0).1)
    (fun E => (nativeTransientMarginLaw_abs_le hX hi hG (hbudget E) 0).2)
  -- the `(m+2)`-nd margin laws converge to `νK^{m+1}`
  have hweak := nativeTransientMarginProb_tendsto hX hi hG hbudget hbudget_top' hu (m+1)
  -- the second moment of the limit, hence integrability of `v`
  have hsq := limit_integral_le_of_forall_integral_le (g := fun x : ℝ => |x|^2) hweak
    (continuous_abs.pow 2) (fun x => by positivity)
    (fun E => (nativeTransientMarginLaw_abs_pow_le hX hi hG (hbudget E) (m+1) (k := 2)
      (by norm_num)).1)
    (fun E => (nativeTransientMarginLaw_abs_pow_le hX hi hG (hbudget E) (m+1) (k := 2)
      (by norm_num)).2)
  have hvint : Integrable (marginLeadingReward X μ)
      (compProbIter (swingMarginKernel X μ) (m+1) ν : Measure ℝ) :=
    integrable_of_le_linear (marginLeadingReward_measurable_actual hX hi hG).aestronglyMeasurable
      (fun r => marginLeadingReward_nonneg hX hi hG) transientRewardGrowthConstant_nonneg
      (marginLeadingReward_le_growth hX hi hG) hsq.1
  -- the mean passage
  have hmean := nativeRecordingDurationNat_normalizedMean_tendsto hX hi hG hbudget hbudget_top' hu m
  have hlim : (∫ r, marginLeadingReward X μ r ∂
      (compProbIter (swingMarginKernel X μ) (m+1) ν : Measure ℝ)) ∈ U := by
    rw [compProbIter_coe]
    rw [compProbIter_coe] at hvint
    exact hΛ ν hνabs.1 hνabs.2 hvint
  have hev : ∀ᶠ E in l', transientNormalizedMean X μ (budget E) (m+2) ∈ U :=
    hmean.eventually (hU.mem_nhds hlim)
  have hev2 : ∀ᶠ E in l', budget E = E := by
    have hl'atTop : l' ≤ atTop := hl'le.trans inf_le_left
    have hthr : ∀ᶠ E in l', stationaryScaleThreshold ≤ E :=
      hl'atTop (eventually_ge_atTop stationaryScaleThreshold)
    filter_upwards [hthr] with E hE
    exact max_eq_left hE
  have hnot : ∀ᶠ E in l', transientNormalizedMean X μ E (m+2) ∉ U := by
    have hlP : l ≤ 𝓟 {E | transientNormalizedMean X μ E (m+2) ∉ U} := inf_le_right
    exact (hl'le.trans hlP) (mem_principal_self _)
  have hfalse : ∀ᶠ _E in l', False := by
    filter_upwards [hev, hev2, hnot] with E h1 h2 h3
    rw [h2] at h1
    exact h3 h1
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

/-! ### Theorem 4.4 -/

/-- The constant `B` of `eq:transient-mainbound`:
`B = L_h (∫ b dλ + C₁ + E G)`, where `λ = ν_∞𝖠`, `C₁` is the uniform first moment
of the first-restart margins and `E G` the mean Gaussian envelope. -/
def transientGeometricConstant (X : ℕ → Ω → ℝ) (μ : Measure Ω) (ν : Measure ℝ) : ℝ :=
  slopeRewardLipschitz * ((∫ b, b ∂slopeStationaryLaw X μ ν) +
    (transientMarginMomentBound 0 1 + ∫ ω, nativeGaussianEnvelope X ω ∂μ))

/-- **Theorem 4.4 (`thm:transientconvergence`) for the actual stream.**  With
`γ_Swing = stationaryLeadingCoefficient X μ ν_∞` the Theorem 4.3 constant, for every
fixed `m` (segment `m+2` in the Lean indexing, `k = m+3` in the paper's):

* `E L_{k,E} = Θ_k(E log E)`: the normalised means are eventually bounded below by a
  positive constant and above by a finite constant;
* `limsup_{E→∞} |E L_{k,E}/(E log E) - γ_Swing| ≤ B (3/4)^{k-3}` with
  `B = transientGeometricConstant`, independent of `k`. -/
theorem theorem_4_4_swing_gaussian [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) :
    ∃ ν : ProbabilityMeasure ℝ,
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
      (∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
        (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ)) ∧
      Tendsto (fun E : ℝ => nativeStationarySegmentMean X μ E / (E * Real.log E)) atTop
        (𝓝 (stationaryLeadingCoefficient X μ (ν : Measure ℝ))) ∧
      0 ≤ transientGeometricConstant X μ (ν : Measure ℝ) ∧
      ∀ m : ℕ,
        (∃ c : ℝ, 0 < c ∧ ∀ᶠ E in atTop, c ≤ transientNormalizedMean X μ E (m+2)) ∧
        (∃ C : ℝ, ∀ᶠ E in atTop, transientNormalizedMean X μ E (m+2) ≤ C) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ E in atTop,
          |transientNormalizedMean X μ E (m+2) - stationaryLeadingCoefficient X μ (ν : Measure ℝ)| <
            transientGeometricConstant X μ (ν : Measure ℝ) * (3 / 4 : ℝ) ^ m + ε) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  -- Theorem 4.3 along `E → ∞`
  set budget : ℝ → ℝ := fun E => max E stationaryScaleThreshold with hbdef
  have hbudget : ∀ E, stationaryScaleThreshold ≤ budget E := fun E => le_max_right _ _
  have hbudget_top : Tendsto budget atTop atTop :=
    tendsto_atTop_mono (fun E => le_max_left E _) tendsto_id
  obtain ⟨ν, hinv, huniq, _, _, hweak, hmean43, _, _, _, _⟩ :=
    theorem_4_3_swing_gaussian hX hi hG hbudget hbudget_top
  have hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ (ν : Measure ℝ)) :=
    slopeStationaryLaw_first_moment_of_weak_limit hX hi hG hbudget hweak
  have hlamP : IsProbabilityMeasure (slopeStationaryLaw X μ (ν : Measure ℝ)) :=
    slopeStationaryLaw_isProbability hX _
  have hlamsupp : slopeStationaryLaw X μ (ν : Measure ℝ) (Ioi 0)ᶜ = 0 := by
    rw [compl_Ioi]; exact slopeStationaryLaw_Iic_zero hX hi hG _
  have hlam_nonneg : 0 ≤ ∫ b, b ∂slopeStationaryLaw X μ (ν : Measure ℝ) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_mem_of_compl_eq_zero hlamsupp] with b hb
    exact le_of_lt hb
  have hB : 0 ≤ transientGeometricConstant X μ (ν : Measure ℝ) := by
    unfold transientGeometricConstant
    have h1 := transientMarginMomentBound_nonneg 0 1
    have h2 : 0 ≤ ∫ ω, nativeGaussianEnvelope X ω ∂μ :=
      integral_nonneg fun ω => nativeGaussianEnvelope_nonneg X ω
    positivity
  refine ⟨ν, hinv, huniq, ?_, hB, fun m => ⟨?_, ?_, ?_⟩⟩
  · -- the Theorem 4.3 limit along the identity budget
    refine hmean43.congr' ?_
    filter_upwards [eventually_ge_atTop stationaryScaleThreshold] with E hE
    simp only [hbdef, max_eq_left hE]
  · -- the positive lower bound
    obtain ⟨c, hc, hlow⟩ := exists_transient_coefficient_lower_bound hX hi hG
      (transientMarginMomentBound_nonneg 0 1) m
    refine ⟨c / 2, by positivity, ?_⟩
    have hev := transient_eventually_mem_of_limits hX hi hG m (U := Ioi (c / 2)) isOpen_Ioi
      (fun ρ hρabs hρM hρint => ?_)
    · filter_upwards [hev] with E hE
      exact le_of_lt hE
    · have := hlow (ρ : Measure ℝ) inferInstance hρabs hρM hρint
      show c / 2 < _
      linarith
  · -- the upper bound
    refine ⟨transientRewardGrowthConstant * (1 + transientMarginMomentBound (m+1) 1), ?_⟩
    filter_upwards [eventually_ge_atTop stationaryScaleThreshold] with E hE
    exact transientNormalizedMean_le hX hi hG hE (m+1)
  · -- the geometric bound
    intro ε hε
    have hev := transient_eventually_mem_of_limits hX hi hG m
      (U := {x : ℝ | |x - stationaryLeadingCoefficient X μ (ν : Measure ℝ)| <
        transientGeometricConstant X μ (ν : Measure ℝ) * (3 / 4 : ℝ) ^ m + ε})
      (isOpen_lt (continuous_id.sub continuous_const).abs continuous_const)
      (fun ρ hρabs hρM _ => ?_)
    · exact hev
    · rw [Set.mem_ofPred_eq]
      have hgeo := transient_coefficient_geometric_bound hX hi hG hinv hmom hρabs hρM m
      have heq : (3 / 4 : ℝ) ^ m * slopeRewardLipschitz *
          ((∫ b, b ∂slopeStationaryLaw X μ (ν : Measure ℝ)) +
            (transientMarginMomentBound 0 1 + ∫ ω, nativeGaussianEnvelope X ω ∂μ)) =
          transientGeometricConstant X μ (ν : Measure ℝ) * (3 / 4 : ℝ) ^ m := by
        unfold transientGeometricConstant
        ring
      rw [heq] at hgeo
      linarith

end SwingRepair
