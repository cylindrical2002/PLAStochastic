import PLAStochastic.Swing.DenseSampling.Segments.FixedIndexLimits
import PLAStochastic.Swing.DenseSampling.Empirical.SymmetricCoordinate
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # A measurable choice of the actual native limiting boundary sign -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def signApproxMesh (n : ℕ) : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹

def nativeSignApprox (ε : ℝ) (n : ℕ) (f : C(ℝ, ℝ)) : ℝ :=
  let h := signApproxMesh n
  let seg := nativeSegmentAt (nativeStream (fun j => (j : ℝ) * h)
    (fun j => f ((j : ℝ) * h)) ε ((n + 1) ^ 2)) 0
  (nativeSegmentEndpoint (fun j => (j : ℝ) * h) seg - f ((seg.finish : ℝ) * h)) / ε

/-- A Borel functional built from finite native outputs; it agrees with the
unique true boundary sign on Brownian paths by the proved first-segment limit. -/
def nativeBoundarySign (ε : ℝ) (f : C(ℝ, ℝ)) : ℝ :=
  limsup (fun n => nativeSignApprox ε n f) atTop

theorem signApproxMesh_pos (n : ℕ) : 0 < signApproxMesh n := by
  unfold signApproxMesh
  positivity

theorem tendsto_signApproxMesh : Tendsto (fun n => (signApproxMesh n : ℝ)) atTop (𝓝 0) := by
  simpa only [signApproxMesh, NNReal.coe_inv, NNReal.coe_add, NNReal.coe_natCast,
    NNReal.coe_one, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem measurable_nativeSignApprox (ε : ℝ) (n : ℕ) : Measurable (nativeSignApprox ε n) := by
  let h := signApproxMesh n
  let seg : C(ℝ, ℝ) → NativeSegment := fun f => nativeSegmentAt
    (nativeStream (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ε ((n + 1) ^ 2)) 0
  have hcode := measurable_nativeStream_output (fun j => (j : ℝ) * h)
    (strictMono_mesh_times (signApproxMesh_pos n))
    (fun j (f : C(ℝ, ℝ)) => f ((j : ℝ) * h)) ε ((n + 1) ^ 2)
    (fun j _ => (continuous_eval_const _).measurable)
  have hc : Measurable (fun f => nativeSegmentCode (seg f)) := by
    simpa only [nativeOutputCode, List.getD_eq_getElem?_getD, seg, nativeSegmentAt] using
      (hcode.snd.eval (a := 0))
  have hs : Measurable (fun f => (seg f).start) := hc.fst
  have he : Measurable (fun f => (seg f).finish) := hc.snd.fst
  have hq : Measurable (fun f => (seg f).anchorValue) := hc.snd.snd.fst
  have hm : Measurable (fun f => (seg f).slope) := hc.snd.snd.snd
  have hcast : Measurable (fun n : ℕ => (n : ℝ)) := measurable_of_countable _
  have htime := (hcast.comp he).mul_const (h : ℝ)
  have hval : Measurable (fun f : C(ℝ, ℝ) => f (((seg f).finish : ℝ) * h)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk htime)
  exact ((hq.add (hm.mul (htime.sub ((hcast.comp hs).mul_const (h : ℝ))))).sub hval).div_const ε

theorem measurable_nativeBoundarySign (ε : ℝ) : Measurable (nativeBoundarySign ε) :=
  Measurable.limsup (measurable_nativeSignApprox ε)

/-- The expanding observation horizon exposes the true first rejection along
the concrete sequence used to define the measurable sign. -/
theorem eventually_nativeSignApprox_eq_first (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    {ε : ℝ} (hε : 0 ≤ ε) (hfinite : anchoredLifetime f ε ≠ ∞) :
    ∀ᶠ n in atTop, nativeSignApprox ε n f = nativeFirstNormalizedOffset
      (fun j => (j : ℝ) * signApproxMesh n)
      (fun j => f ((j : ℝ) * signApproxMesh n)) ε := by
  have hh (n : ℕ) : signApproxMesh n ≠ 0 := (signApproxMesh_pos n).ne'
  have hp (n : ℕ) : 0 < (signApproxMesh n : ℝ) := signApproxMesh_pos n
  have htime := tendsto_nativeFirstRecording_mesh f hf hε hfinite hh tendsto_signApproxMesh
  have hlife := tendsto_finiteMeshAnchoredLifetime f ε hp tendsto_signApproxMesh
  have hfin := hlife.eventually_lt_const (lt_top_iff_ne_top.mpr hfinite)
  have hhorizon (n : ℕ) : (((n + 1) ^ 2 : ℕ) : ℝ) * signApproxMesh n = (n : ℝ) + 1 := by
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, signApproxMesh, NNReal.coe_inv,
      NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    field_simp
  have hn : ∀ᶠ n : ℕ in atTop, (anchoredLifetime f ε).toReal + 1 < (n : ℝ) + 1 :=
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_gt_atTop (anchoredLifetime f ε).toReal)).mono (fun n hn => by linarith)
  filter_upwards [hfin, htime.eventually_lt_const (show (anchoredLifetime f ε).toReal <
    (anchoredLifetime f ε).toReal + 1 by linarith), hn] with n hnfin hrec hN
  obtain ⟨K, hK, hcone⟩ := exists_nativeGrid_threshold f hf (signApproxMesh n) (hh n) hε hnfin.ne
  have hc : ∀ j, nativePrefixFeasible (fun i => (i : ℝ) * signApproxMesh n)
      (fun i => f ((i : ℝ) * signApproxMesh n)) ε 0 j
      (f ((0 : ℕ) * signApproxMesh n)) ↔ j < K := by
    simpa only [Nat.cast_zero, zero_mul] using hcone
  rw [nativeFirstRecording_eq_threshold _ _ ε hK hc] at hrec
  have hKN : K ≤ (n + 1) ^ 2 := by
    have hx := hhorizon n
    have hh' := hp n
    have hc : ((K - 1 : ℕ) : ℝ) < (((n + 1) ^ 2 : ℕ) : ℝ) := by nlinarith
    have hc' : K - 1 < (n + 1) ^ 2 := by exact_mod_cast hc
    omega
  have ho := (nativeStream_first_eq_threshold _ _ ε hK hc hKN).2.1
  dsimp only [nativeSignApprox]
  rw [ho]
  rfl

theorem nativeBoundarySign_eq_terminal (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    {ε : ℝ} (hε : 0 < ε) {σ : ℝ≥0} (hσ : anchoredLifetime f ε = σ)
    {a : ℝ} (ha : ∀ t : Icc (0 : ℝ) (σ : ℝ), |f t - a * (t : ℝ)| ≤ ε) :
    nativeBoundarySign ε f = (a * (σ : ℝ) - f σ) / ε := by
  have hfinite : anchoredLifetime f ε ≠ ∞ := by rw [hσ]; exact ENNReal.coe_ne_top
  have ht := tendsto_nativeFirstNormalizedOffset_mesh f hf hε hσ ha
    (fun n => (signApproxMesh_pos n).ne') tendsto_signApproxMesh
  have hc : Tendsto (fun n => nativeSignApprox ε n f) atTop
      (𝓝 ((a * (σ : ℝ) - f σ) / ε)) := by
    apply ht.congr'
    filter_upwards [eventually_nativeSignApprox_eq_first f hf hε.le hfinite] with n hn
    exact hn.symm
  exact hc.limsup_eq

/-- The full continuous-path lifetime functional is Borel measurable. -/
theorem measurable_anchoredLifetime_full (ε : ℝ) :
    Measurable (fun f : C(ℝ, ℝ) => anchoredLifetime f ε) :=
  measurable_firstExceedance
    (fun t => ((continuous_anchoredError 1).comp (continuous_unitPath_in_path t)).measurable)
    (fun f => (continuous_anchoredTimeError f).comp continuous_subtype_val) ε

theorem anchoredLifetime_neg (f : C(ℝ, ℝ)) (ε : ℝ) :
    anchoredLifetime (-f) ε = anchoredLifetime f ε := by
  unfold anchoredLifetime
  congr 1
  funext t
  rw [← neg_one_smul ℝ f, anchoredTimeError_smul]
  simp only [abs_neg, abs_one, one_mul]

/-- Uniqueness at the pinch makes the limiting sign odd under reflection;
no symmetry premise is imposed on the finite-mesh selection rule. -/
theorem nativeBoundarySign_neg_of_finite (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    {ε : ℝ} (hε : 0 < ε) {σ : ℝ≥0} (hσ : anchoredLifetime f ε = σ) :
    nativeBoundarySign ε (-f) = -nativeBoundarySign ε f := by
  have hzero : |f 0| < ε := by rw [hf, abs_zero]; exact hε
  obtain ⟨a, ha, _⟩ := existsUnique_anchored_fit_at_lifetime f hzero hσ
  have hneg : anchoredLifetime (-f) ε = σ := (anchoredLifetime_neg f ε).trans hσ
  have hfit : ∀ t : Icc (0 : ℝ) (σ : ℝ), |(-f) t - (-a) * (t : ℝ)| ≤ ε := by
    intro t
    simpa only [ContinuousMap.neg_apply, neg_mul, neg_sub_neg, abs_sub_comm] using ha t
  rw [nativeBoundarySign_eq_terminal f hf hε hσ ha,
    nativeBoundarySign_eq_terminal (-f) (by simp only [ContinuousMap.neg_apply, hf, neg_zero]) hε hneg hfit]
  simp only [ContinuousMap.neg_apply]
  ring

def brownianNativeBoundarySign {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ε : ℝ) (ω : Ω) : ℝ :=
  nativeBoundarySign ε (processPath B ω)

theorem aemeasurable_brownianNativeBoundarySign {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) (ε : ℝ) :
    AEMeasurable (brownianNativeBoundarySign B ε) μ :=
  (measurable_nativeBoundarySign ε).comp_aemeasurable (aemeasurable_processPath hB)

theorem brownianNativeBoundarySign_values_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, brownianNativeBoundarySign B ε ω = 1 ∨ brownianNativeBoundarySign B ε ω = -1 := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
    anchoredProcessLifetime_tolerance_ae_ne_top hB hε] with ω hc hz hf
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hσ' : anchoredLifetime (processPath B ω) ε = (σ : ℝ≥0∞) := hσ.symm
  have hzero : processPath B ω 0 = 0 := (processPath_apply_of_continuous hc 0).trans hz
  have hzero' : |processPath B ω 0| < ε := by rw [hzero, abs_zero]; exact hε
  obtain ⟨a, ha, _⟩ := existsUnique_anchored_fit_at_lifetime (processPath B ω) hzero' hσ'
  change nativeBoundarySign ε (processPath B ω) = 1 ∨ nativeBoundarySign ε (processPath B ω) = -1
  rw [nativeBoundarySign_eq_terminal (processPath B ω) hzero hε hσ' ha]
  exact nativeFirst_limit_offset_sign (processPath B ω) hzero hε hσ' ha

/-- The real extension equals the original nonnegative-time coordinate. -/
theorem processPath_apply_real_of_continuous {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hc : Continuous (fun t => B t ω)) (t : ℝ) :
    processPath B ω t = B t.toNNReal ω := by
  exact ContinuousMap.mkD_apply_of_continuous (hc.comp continuous_real_toNNReal)

/-- Brownian finite-dimensional laws determine the entire Borel continuous-path
law. The proof uses a globally measurable continuous version and a countable
measurable embedding, not an assumed Wiener-law representation. -/
theorem identDistrib_processPath_of_Brownian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B C : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B μ) (hC : IsBrownianReal C μ) :
    IdentDistrib (processPath B) (processPath C) μ μ := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let F := continuousBrownianPath hB
  let G := continuousBrownianPath hC
  have hmF : Measurable (fun ω (t : ℝ≥0) => F ω t) :=
    measurable_pi_lambda _ (fun t => (continuous_eval_const (t : ℝ)).measurable.comp
      (measurable_continuousBrownianPath hB))
  have hmG : Measurable (fun ω (t : ℝ≥0) => G ω t) :=
    measurable_pi_lambda _ (fun t => (continuous_eval_const (t : ℝ)).measurable.comp
      (measurable_continuousBrownianPath hC))
  have hpreF : IsPreBrownianReal (fun t ω => F ω t) μ :=
    hB.toIsPreBrownianReal.congr (fun t => by
      filter_upwards [continuousBrownianPath_all_times_ae_eq hB] with ω hω
      exact (hω t).symm)
  have hpreG : IsPreBrownianReal (fun t ω => G ω t) μ :=
    hC.toIsPreBrownianReal.congr (fun t => by
      filter_upwards [continuousBrownianPath_all_times_ae_eq hC] with ω hω
      exact (hω t).symm)
  have hd : IdentDistrib (fun ω (t : ℝ≥0) => F ω t) (fun ω (t : ℝ≥0) => G ω t) μ μ :=
    (identDistrib_iff_forall_finset_identDistrib hmF.aemeasurable hmG.aemeasurable).mpr
      (fun I => (hpreF.hasLaw I).identDistrib (hpreG.hasLaw I))
  have hobs := hd.comp (measurable_pi_lambda (fun p : ℝ≥0 → ℝ => fun q : ℚ => p (q : ℝ).toNNReal)
    (fun q => measurable_pi_apply _))
  have hFeq : (fun ω => fun q : ℚ => F ω (q : ℝ).toNNReal) =ᵐ[μ]
      (fun ω => fullPathObservations (processPath B ω)) := by
    filter_upwards [continuousBrownianPath_all_times_ae_eq hB, hB.cont] with ω hf hc
    funext q
    rw [hf]
    exact (processPath_apply_real_of_continuous hc (q : ℝ)).symm
  have hGeq : (fun ω => fun q : ℚ => G ω (q : ℝ).toNNReal) =ᵐ[μ]
      (fun ω => fullPathObservations (processPath C ω)) := by
    filter_upwards [continuousBrownianPath_all_times_ae_eq hC, hC.cont] with ω hg hc
    funext q
    rw [hg]
    exact (processPath_apply_real_of_continuous hc (q : ℝ)).symm
  have hobs' : IdentDistrib (fun ω => fullPathObservations (processPath B ω))
      (fun ω => fullPathObservations (processPath C ω)) μ μ :=
    ((IdentDistrib.of_ae_eq hobs.aemeasurable_fst hFeq).symm.trans hobs).trans
      (IdentDistrib.of_ae_eq hobs.aemeasurable_snd hGeq)
  refine ⟨aemeasurable_processPath hB, aemeasurable_processPath hC, ?_⟩
  apply measurableEmbedding_fullPathObservations.map_injective
  rw [AEMeasurable.map_map_of_aemeasurable
    measurableEmbedding_fullPathObservations.measurable.aemeasurable (aemeasurable_processPath hB),
    AEMeasurable.map_map_of_aemeasurable
      measurableEmbedding_fullPathObservations.measurable.aemeasurable (aemeasurable_processPath hC)]
  exact hobs'.map_eq

theorem processPath_neg_of_continuous {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hc : Continuous (fun t => B t ω)) : processPath (-B) ω = -processPath B ω := by
  ext t
  rw [processPath_apply_real_of_continuous hc.neg, ContinuousMap.neg_apply,
    processPath_apply_real_of_continuous hc]
  rfl

/-- Actual Brownian reflection preserves the lifetime and reverses the
measurably constructed terminal sign, jointly in distribution. -/
theorem identDistrib_lifetime_boundarySign_reflection {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    IdentDistrib (fun ω => ((anchoredProcessLifetime B ε ω).toReal, brownianNativeBoundarySign B ε ω))
      (fun ω => ((anchoredProcessLifetime B ε ω).toReal, -brownianNativeBoundarySign B ε ω)) μ μ := by
  have hd := (identDistrib_processPath_of_Brownian hB hB.neg).comp
    (((measurable_anchoredLifetime_full ε).ennreal_toReal).prodMk (measurable_nativeBoundarySign ε))
  have he : (fun ω => ((anchoredLifetime (processPath (-B) ω) ε).toReal,
      nativeBoundarySign ε (processPath (-B) ω))) =ᵐ[μ]
      (fun ω => ((anchoredProcessLifetime B ε ω).toReal, -brownianNativeBoundarySign B ε ω)) := by
    filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
      anchoredProcessLifetime_tolerance_ae_ne_top hB hε] with ω hc hz hf
    obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
    have hzero : processPath B ω 0 = 0 := (processPath_apply_of_continuous hc 0).trans hz
    dsimp only [anchoredProcessLifetime, brownianNativeBoundarySign]
    rw [processPath_neg_of_continuous hc, anchoredLifetime_neg,
      nativeBoundarySign_neg_of_finite (processPath B ω) hzero hε hσ.symm]
  exact hd.trans (IdentDistrib.of_ae_eq hd.aemeasurable_snd he)

/-- The measurable sign is the sign appearing in every fixed-index native
limit, for every positive mesh tending to zero on the same actual path. -/
theorem brownian_native_offsets_tendsto_named_boundarySign_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0}
    (hh : ∀ i, h i ≠ 0) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ H : ℝ, (anchoredProcessLifetime B ε ω).toReal < H → ∀ k : ℕ,
      Tendsto (fun i => brownianNativeMeshEndpointOffset B ε H (h i) k ω) l
        (𝓝 ((-1 : ℝ) ^ k * brownianNativeBoundarySign B ε ω)) := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
    anchoredProcessLifetime_tolerance_ae_ne_top hB hε,
    brownian_boundary_no_extension_real_ae hB hε] with ω hc hz hf hno
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hσ' : anchoredLifetime (processPath B ω) ε = (σ : ℝ≥0∞) := hσ.symm
  have hr : (anchoredProcessLifetime B ε ω).toReal = (σ : ℝ) := by rw [← hσ]; rfl
  have hzero : processPath B ω 0 = 0 := (processPath_apply_of_continuous hc 0).trans hz
  have hzero' : |processPath B ω 0| < ε := by rw [hzero, abs_zero]; exact hε
  obtain ⟨a, ha, _⟩ := existsUnique_anchored_fit_at_lifetime (processPath B ω) hzero' hσ'
  intro H hH k
  have hk := nativeMesh_fixed_index_degeneracy (processPath B ω) hzero hε hσ'
    (by simpa only [hr] using hH) ha (by simpa only [hr] using hno) hh hconv k
  have ho := hk.2.2.div_const ε
  simpa only [brownianNativeMeshEndpointOffset_eq_processPath hc, mul_div_assoc,
    brownianNativeBoundarySign, nativeBoundarySign_eq_terminal (processPath B ω) hzero hε hσ' ha] using ho

/-- The actual limiting sign is fair, with both probabilities exactly one half. -/
theorem brownianNativeBoundarySign_fair {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | brownianNativeBoundarySign B ε ω = 1} = 1 / 2 ∧
      μ {ω | brownianNativeBoundarySign B ε ω = -1} = 1 / 2 := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact symmetric_binary_fair (brownianNativeBoundarySign_values_ae hB hε)
    (identDistrib_lifetime_boundarySign_reflection hB hε)

/-- Independence of the actual measurable limiting sign and actual pinch time. -/
theorem brownianNativeBoundarySign_indep_lifetime {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    IndepFun (brownianNativeBoundarySign B ε)
      (fun ω => (anchoredProcessLifetime B ε ω).toReal) μ := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact (symmetric_binary_indep (brownianNativeBoundarySign_values_ae hB hε)
    (identDistrib_lifetime_boundarySign_reflection hB hε)).symm

/-- Every measurable pinch-time event is divided exactly equally between the
positive and negative signs, preserving the full independence quantifier. -/
theorem brownianNativeBoundarySign_joint_half {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {A : Set ℝ} (hA : MeasurableSet A) :
    μ {ω | (anchoredProcessLifetime B ε ω).toReal ∈ A ∧ brownianNativeBoundarySign B ε ω = 1} =
        μ {ω | (anchoredProcessLifetime B ε ω).toReal ∈ A} / 2 ∧
    μ {ω | (anchoredProcessLifetime B ε ω).toReal ∈ A ∧ brownianNativeBoundarySign B ε ω = -1} =
        μ {ω | (anchoredProcessLifetime B ε ω).toReal ∈ A} / 2 :=
  symmetric_binary_joint_half (brownianNativeBoundarySign_values_ae hB hε)
    (identDistrib_lifetime_boundarySign_reflection hB hε) hA

/-- The paper's finite-vector joint limit, with the same measurable fair sign
for every coordinate. Pair convergence includes both recording times and offsets. -/
theorem brownian_native_joint_fixed_vector_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0}
    (hh : ∀ i, h i ≠ 0) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ H : ℝ, (anchoredProcessLifetime B ε ω).toReal < H → ∀ K : ℕ,
      Tendsto (fun i => fun k : Fin K =>
        (brownianNativeMeshEndpointTime B ε H (h i) k ω,
          brownianNativeMeshEndpointOffset B ε H (h i) k ω)) l
        (𝓝 (fun k : Fin K => ((anchoredProcessLifetime B ε ω).toReal,
          (-1 : ℝ) ^ (k : ℕ) * brownianNativeBoundarySign B ε ω))) := by
  filter_upwards [brownian_native_fixed_index_degeneracy_ae hB hε hh hconv,
    brownian_native_offsets_tendsto_named_boundarySign_ae hB hε hh hconv] with ω ht ho
  obtain ⟨S, _, hs⟩ := ht
  intro H hH K
  apply tendsto_pi_nhds.mpr
  intro k
  exact (hs H hH k).2.1.prodMk_nhds (ho H hH k)

end SwingRepair
