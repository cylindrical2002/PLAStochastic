import PLAStochastic.Brownian.Markov.ExponentialMartingale
import PLAStochastic.Brownian.Hitting.GridStopping
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Brownian restart at a stopping time

Countable-valued stopping times are handled by their measurable fibers. General
finite stopping times are approached from above by actual ceiling-grid stopping
times. Only countably many fixed-time modification identities enter the limit.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem measurable_countable_time_selection {β : Type*} [MeasurableSpace β]
    {Y : ℝ≥0 → Ω → β} (hY : ∀ t, Measurable (Y t)) {τ : Ω → ℝ≥0}
    (hτ : Measurable τ) (hcount : (Set.range τ).Countable) :
    Measurable (fun ω => Y (τ ω) ω) := by
  let S := Set.range τ
  let : Countable S := hcount.to_subtype
  have h : Measurable (fun p : Ω × S => Y p.2.1 p.1) :=
    measurable_from_prod_countable_left (fun t => hY t.1)
  exact h.comp (measurable_id.prodMk (hτ.subtype_mk (h := Set.mem_range_self)))

theorem measure_eq_tsum_countable_time {τ : Ω → ℝ≥0} (hτ : Measurable τ)
    (hcount : (Set.range τ).Countable) {A : Set Ω} (hA : MeasurableSet A) :
    μ A = ∑' t : Set.range τ, μ (A ∩ {ω | τ ω = t.1}) := by
  let : Countable (Set.range τ) := hcount.to_subtype
  have hu : (⋃ t : Set.range τ, A ∩ {ω | τ ω = t.1}) = A := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨⟨τ ω, Set.mem_range_self ω⟩, h, rfl⟩⟩
  calc
    μ A = μ (⋃ t : Set.range τ, A ∩ {ω | τ ω = t.1}) := congrArg μ hu.symm
    _ = _ := ?_
  apply measure_iUnion
  · intro t s hts
    apply Set.disjoint_left.mpr
    rintro ω ⟨_, ht⟩ ⟨_, hs⟩
    exact hts (Subtype.ext (ht.symm.trans hs))
  · intro t
    exact hA.inter (hτ (measurableSet_singleton t.1))

/-- The conditional restart law at a countable-valued stopping time follows
from deterministic-time independence and identical deterministic future laws. -/
theorem countableStoppedSelection_inter_measure {β : Type*} [MeasurableSpace β]
    {ℱ : Filtration ℝ≥0 mΩ} {Y : ℝ≥0 → Ω → β} {ν : Measure β}
    (hY : ∀ t, Measurable (Y t))
    (hi : ∀ t, Indep (MeasurableSpace.comap (Y t) inferInstance) (ℱ t) μ)
    (hlaw : ∀ t, HasLaw (Y t) ν μ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hcount : (Set.range τ).Countable) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) {D : Set β} (hD : MeasurableSet D) :
    μ (A ∩ (fun ω => Y (τ ω) ω) ⁻¹' D) = μ A * ν D := by
  have hτm : Measurable τ := by simpa using! hτ.measurable'.untopD 0
  have hAm := hτ.measurableSpace_le _ hA
  have hm := measurable_countable_time_selection hY hτm hcount
  rw [measure_eq_tsum_countable_time hτm hcount (hAm.inter (hm hD))]
  calc
    _ = ∑' t : Set.range τ, μ (A ∩ {ω | τ ω = t.1}) * ν D := by
      apply tsum_congr
      intro t
      have heq : (A ∩ (fun ω => Y (τ ω) ω) ⁻¹' D) ∩ {ω | τ ω = t.1} =
          Y t.1 ⁻¹' D ∩ (A ∩ {ω | τ ω = t.1}) := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨ha, hd⟩, ht⟩
          exact ⟨by simpa only [ht] using hd, ha, ht⟩
        · rintro ⟨hd, ha, ht⟩
          exact ⟨⟨ha, by simpa only [ht] using hd⟩, ht⟩
      have hs : MeasurableSet[ℱ t.1] (A ∩ {ω | τ ω = t.1}) := by
        simpa only [WithTop.coe_eq_coe] using
          (hτ.measurableSet_inter_eq_iff A t.1).mp (hA.inter (hτ.measurableSet_eq' t.1))
      rw [heq, (Indep_iff _ _ μ).mp (hi t.1) _ _ ⟨D, hD, rfl⟩ hs]
      have hval : μ (Y t.1 ⁻¹' D) = ν D := by
        rw [← (hlaw t.1).map_eq, Measure.map_apply (hY t.1) hD]
      rw [hval, mul_comm]
    _ = _ := by
      rw [ENNReal.tsum_mul_right, ← measure_eq_tsum_countable_time hτm hcount hAm]

/-- A fixed finite law is preserved by almost-sure convergence. The proof uses
bounded continuous tests and dominated convergence, not an assumed limit law. -/
theorem map_eq_of_ae_tendsto_constant_law {E : Type*} [MeasurableSpace E]
    [PseudoMetricSpace E] [BorelSpace E] [SecondCountableTopology E]
    [IsFiniteMeasure μ] {ν : Measure E} [IsFiniteMeasure ν]
    {X : ℕ → Ω → E} {Z : Ω → E} (hX : ∀ n, AEMeasurable (X n) μ)
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω)))
    (hlaw : ∀ n, μ.map (X n) = ν) : μ.map Z = ν := by
  have hZ := aemeasurable_of_tendsto_metrizable_ae atTop hX hconv
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hZ f.continuous.measurable.aestronglyMeasurable]
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Ω => ‖f‖)
    (fun n => (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall (fun ω => f.norm_coe_le_norm (X n ω)))
    (hconv.mono (fun ω hω => (f.continuous.tendsto (Z ω)).comp hω))
  have hconst : (fun n => ∫ ω, f (X n ω) ∂μ) = fun _ : ℕ => ∫ x, f x ∂ν := by
    funext n
    rw [← hlaw n, integral_map (hX n) f.continuous.measurable.aestronglyMeasurable]
  simp only [Function.comp_def] at ht
  rw [hconst] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- Ceiling-grid approximation is a stopping time in the original filtration;
no right-continuity or completion of the filtration is assumed. -/
theorem upperGridTime_isStoppingTime {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) (n : ℕ) :
    IsStoppingTime ℱ (fun ω => (upperGridTime n (τ ω) : WithTop ℝ≥0)) := by
  intro t
  let k := ⌊t / reciprocalMesh n⌋₊
  have hk : reciprocalMesh n * (k : ℝ≥0) ≤ t := by
    have hf := Nat.floor_le (show (0 : ℝ≥0) ≤ t / reciprocalMesh n from bot_le)
    exact (by simpa only [mul_comm] using (le_div_iff₀ (reciprocalMesh_pos n)).mp hf)
  have hm := ℱ.mono hk _ (hτ (reciprocalMesh n * k))
  convert hm using 1
  ext ω
  simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe, upperGridTime, upperGridIndex]
  rw [mul_comm, ← le_div_iff₀ (reciprocalMesh_pos n),
    ← Nat.le_floor_iff (show (0 : ℝ≥0) ≤ t / reciprocalMesh n from bot_le), Nat.ceil_le,
    div_le_iff₀ (reciprocalMesh_pos n), mul_comm]

omit mΩ in
theorem upperGridTime_countable_range (τ : Ω → ℝ≥0) (n : ℕ) :
    (Set.range (fun ω => upperGridTime n (τ ω))).Countable := by
  apply (Set.countable_range (fun k : ℕ => reciprocalMesh n * (k : ℝ≥0))).mono
  intro x hx
  obtain ⟨ω, rfl⟩ := hx
  exact ⟨upperGridIndex n (τ ω), rfl⟩

variable {B : ℝ≥0 → Ω → ℝ}

/-- The actual future increments, evaluated on the original continuous path. -/
def brownianRestart (B : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  B (τ ω + t) ω - B (τ ω) ω

def measurableBrownianFuture (hB : IsPreBrownianReal B μ) (I : Finset ℝ≥0)
    (s : ℝ≥0) (ω : Ω) : I → ℝ := fun t =>
  measurableBrownian hB (s + t.1) ω - measurableBrownian hB s ω

theorem measurable_measurableBrownianFuture (hB : IsPreBrownianReal B μ)
    (I : Finset ℝ≥0) (s : ℝ≥0) : Measurable (measurableBrownianFuture hB I s) :=
  measurable_pi_lambda _ (fun t =>
    (measurable_measurableBrownian hB (s + t.1)).sub (measurable_measurableBrownian hB s))

theorem measurableBrownianFuture_hasLaw (hB : IsPreBrownianReal B μ)
    (I : Finset ℝ≥0) (s : ℝ≥0) :
    HasLaw (measurableBrownianFuture hB I s) (BrownianReal.projectiveFamily I) μ :=
  ((isPreBrownianReal_measurableBrownian hB).shift s).hasLaw I

theorem measurableBrownianFuture_indep (hB : IsPreBrownianReal B μ)
    (I : Finset ℝ≥0) (s : ℝ≥0) :
    Indep (MeasurableSpace.comap (measurableBrownianFuture hB I s) inferInstance)
      (brownianNaturalFiltration hB s) μ := by
  have h := ((isPreBrownianReal_measurableBrownian hB).indepFun_shift s).comp
    (measurable_pi_lambda _ (fun t : I => measurable_pi_apply t.1)) measurable_id
  rw [brownianNaturalFiltration, Filtration.natural_eq_comap]
  simpa only [measurableBrownianFuture, Function.comp_def, id_eq] using! h

theorem measurableBrownianFuture_map_restrict_countable (hB : IsPreBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hcount : (Set.range τ).Countable) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    (μ.restrict A).map (fun ω => measurableBrownianFuture hB I (τ ω) ω) =
      μ A • BrownianReal.projectiveFamily I := by
  have hτm : Measurable τ := by simpa using! hτ.measurable'.untopD 0
  have hm := measurable_countable_time_selection
    (measurable_measurableBrownianFuture hB I) hτm hcount
  apply Measure.ext
  intro D hD
  rw [Measure.map_apply hm hD, Measure.restrict_apply (hm hD), Measure.smul_apply,
    smul_eq_mul, Set.inter_comm]
  exact countableStoppedSelection_inter_measure (measurable_measurableBrownianFuture hB I)
    (measurableBrownianFuture_indep hB I) (measurableBrownianFuture_hasLaw hB I) hτ hcount hA hD

/-- Only a countable family of fixed-time modification identities is used,
including both the stopping time and each future time translated by it. -/
theorem measurableBrownianFuture_countable_ae_eq_actual (hB : IsPreBrownianReal B μ)
    (I : Finset ℝ≥0) (τ : Ω → ℝ≥0) (hcount : (Set.range τ).Countable) :
    (fun ω => measurableBrownianFuture hB I (τ ω) ω) =ᵐ[μ]
      (fun ω (t : I) => brownianRestart B τ t.1 ω) := by
  let S := Set.range τ
  let : Countable S := hcount.to_subtype
  filter_upwards [measurableBrownian_countable_ae_eq hB (fun s : S => s.1),
    measurableBrownian_countable_ae_eq hB (fun p : S × I => p.1.1 + p.2.1)] with ω h0 h1
  funext t
  exact congrArg₂ (· - ·) (h1 (⟨τ ω, Set.mem_range_self ω⟩, t))
    (h0 ⟨τ ω, Set.mem_range_self ω⟩)

/-- Ceiling-grid increments converge to the actual random-time increments.
The common full-measure event is formed before evaluating at any random time. -/
theorem measurableBrownianFuture_grid_ae_tendsto (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) (τ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => measurableBrownianFuture hB.toIsPreBrownianReal I
      (upperGridTime n (τ ω)) ω) atTop (𝓝 (fun t : I => brownianRestart B τ t.1 ω)) := by
  have heq : ∀ᵐ ω ∂μ, ∀ n,
      measurableBrownianFuture hB.toIsPreBrownianReal I (upperGridTime n (τ ω)) ω =
        fun t : I => brownianRestart B (fun ω => upperGridTime n (τ ω)) t.1 ω :=
    ae_all_iff.mpr (fun n => measurableBrownianFuture_countable_ae_eq_actual
      hB.toIsPreBrownianReal I _ (upperGridTime_countable_range τ n))
  filter_upwards [hB.cont, heq] with ω hc heqω
  have hconv : Tendsto (fun n (t : I) =>
      brownianRestart B (fun ω => upperGridTime n (τ ω)) t.1 ω) atTop
      (𝓝 (fun t : I => brownianRestart B τ t.1 ω)) := by
    apply tendsto_pi_nhds.mpr
    intro t
    exact ((hc.tendsto (τ ω + t.1)).comp ((upperGridTime_tendsto (τ ω)).add_const t.1)).sub
      ((hc.tendsto (τ ω)).comp (upperGridTime_tendsto (τ ω)))
  exact hconv.congr (fun n => (heqω n).symm)

theorem brownianRestart_finite_aemeasurable (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    AEMeasurable (fun ω (t : I) => brownianRestart B τ t.1 ω) μ := by
  apply aemeasurable_of_tendsto_metrizable_ae atTop _
    (measurableBrownianFuture_grid_ae_tendsto hB I τ)
  intro n
  have hg := upperGridTime_isStoppingTime hτ n
  have hm : Measurable (fun ω => upperGridTime n (τ ω)) := by
    simpa using! hg.measurable'.untopD 0
  exact (measurable_countable_time_selection
    (measurable_measurableBrownianFuture hB.toIsPreBrownianReal I) hm
    (upperGridTime_countable_range τ n)).aemeasurable

/-- Conditional Brownian finite-dimensional law after an everywhere finite
stopping time. Boundedness is not needed because the tests are bounded. -/
theorem brownianRestart_map_restrict (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    (μ.restrict A).map (fun ω (t : I) => brownianRestart B τ t.1 ω) =
      μ A • BrownianReal.projectiveFamily I := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have : IsFiniteMeasure (μ A • BrownianReal.projectiveFamily I) := by
    constructor
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact measure_lt_top μ A
  apply map_eq_of_ae_tendsto_constant_law (X := fun n ω =>
    measurableBrownianFuture hB.toIsPreBrownianReal I (upperGridTime n (τ ω)) ω)
  · intro n
    have hg := upperGridTime_isStoppingTime hτ n
    have hm : Measurable (fun ω => upperGridTime n (τ ω)) := by
      simpa using! hg.measurable'.untopD 0
    exact (measurable_countable_time_selection
      (measurable_measurableBrownianFuture hB.toIsPreBrownianReal I) hm
      (upperGridTime_countable_range τ n)).aemeasurable
  · exact ae_restrict_of_ae (measurableBrownianFuture_grid_ae_tendsto hB I τ)
  · intro n
    have hg := upperGridTime_isStoppingTime hτ n
    apply measurableBrownianFuture_map_restrict_countable hB.toIsPreBrownianReal I hg
      (upperGridTime_countable_range τ n)
    exact hτ.measurableSpace_mono hg
      (fun ω => WithTop.coe_le_coe.mpr (le_upperGridTime n (τ ω))) _ hA

theorem brownianRestart_hasLaw (hB : IsBrownianReal B μ) (I : Finset ℝ≥0) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    HasLaw (fun ω (t : I) => brownianRestart B τ t.1 ω) (BrownianReal.projectiveFamily I) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact ⟨brownianRestart_finite_aemeasurable hB I hτ,
    by simpa using brownianRestart_map_restrict hB I hτ MeasurableSet.univ⟩

/-- The actual original process restarted at the finite stopping time is Brownian. -/
theorem isBrownianReal_brownianRestart (hB : IsBrownianReal B μ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) : IsBrownianReal (brownianRestart B τ) μ where
  hasLaw I := brownianRestart_hasLaw hB I hτ
  cont := hB.cont.mono (fun _ hω => (hω.comp (continuous_const.add continuous_id)).sub continuous_const)

theorem brownianRestart_finite_indep_stopped (hB : IsBrownianReal B μ)
    (I : Finset ℝ≥0) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Indep (MeasurableSpace.comap (fun ω (t : I) => brownianRestart B τ t.1 ω) inferInstance)
      hτ.measurableSpace μ := by
  apply (Indep_iff _ _ μ).mpr
  intro C A hC hA
  obtain ⟨D, hD, rfl⟩ := hC
  have hm := brownianRestart_finite_aemeasurable hB I hτ
  have hmap := congrArg (fun ν : Measure (I → ℝ) => ν D) (brownianRestart_map_restrict hB I hτ hA)
  rw [Measure.map_apply_of_aemeasurable hm.restrict hD,
    Measure.restrict_apply' (hτ.measurableSpace_le _ hA), Measure.smul_apply, smul_eq_mul] at hmap
  have hval : μ ((fun ω (t : I) => brownianRestart B τ t.1 ω) ⁻¹' D) =
      BrownianReal.projectiveFamily I D := by
    rw [← (brownianRestart_hasLaw hB I hτ).map_eq, Measure.map_apply_of_aemeasurable hm hD]
  rw [hmap, hval, mul_comm]

/-- Strong Markov independence holds for the whole future process with its
coordinate sigma-algebra, not merely for one future increment. -/
theorem brownianRestart_indep_stopped (hB : IsBrownianReal B μ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Indep (MeasurableSpace.comap (fun ω t => brownianRestart B τ t ω) inferInstance)
      hτ.measurableSpace μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hm : @Measurable Ω Ω mΩ hτ.measurableSpace id :=
    fun A hA => hτ.measurableSpace_le A hA
  have hi := @IndepFun.process_indepFun₀ ℝ≥0 Ω mΩ μ (fun _ => ℝ) Ω
    (fun _ => inferInstance) hτ.measurableSpace (brownianRestart B τ) id
    (fun t => (isBrownianReal_brownianRestart hB hτ).aemeasurable t)
    (show @AEMeasurable Ω Ω hτ.measurableSpace mΩ id μ from ⟨id, hm, EventuallyEq.rfl⟩)
    (fun I => show @IndepFun Ω (I → ℝ) Ω mΩ inferInstance hτ.measurableSpace
        (fun ω t => brownianRestart B τ t.1 ω) id μ from by
      change Indep _ (MeasurableSpace.comap id hτ.measurableSpace) μ
      simpa only [MeasurableSpace.comap_id] using brownianRestart_finite_indep_stopped hB I hτ)
    inferInstance
  change Indep _ (MeasurableSpace.comap id hτ.measurableSpace) μ at hi
  simpa only [MeasurableSpace.comap_id] using hi

end BrownianAffine
