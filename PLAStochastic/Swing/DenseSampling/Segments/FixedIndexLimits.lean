import PLAStochastic.Swing.DenseSampling.Segments.ChainDegeneration
import PLAStochastic.Swing.DenseSampling.Segments.FirstEndpointBoundary
import PLAStochastic.Swing.DenseSampling.Segments.RecordingCount

/-! # Actual native fixed-index dense limits and count divergence -/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def nativeMeshStream (f : C(ℝ, ℝ)) (ε H h : ℝ) : List NativeSegment :=
  nativeStream (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ε ⌊H / h⌋₊

def nativeMeshSegment (f : C(ℝ, ℝ)) (ε H h : ℝ) (k : ℕ) : NativeSegment :=
  nativeSegmentAt (nativeMeshStream f ε H h) k

def nativeMeshEndpointTime (f : C(ℝ, ℝ)) (ε H h : ℝ) (k : ℕ) : ℝ :=
  ((nativeMeshSegment f ε H h k).finish : ℝ) * h

def nativeMeshEndpointOffset (f : C(ℝ, ℝ)) (ε H h : ℝ) (k : ℕ) : ℝ :=
  nativeSegmentEndpoint (fun j => (j : ℝ) * h) (nativeMeshSegment f ε H h k) -
    f (nativeMeshEndpointTime f ε H h k)

/-- Observing past a true first rejection exposes exactly the same selected
first segment, irrespective of how much further the stream is run. -/
theorem nativeStream_first_eq_threshold (t y : ℕ → ℝ) (ε : ℝ) {K N : ℕ}
    (hK : 1 < K) (hcone : ∀ j, nativePrefixFeasible t y ε 0 j (y 0) ↔ j < K)
    (hKN : K ≤ N) :
    0 < (nativeStream t y ε N).length ∧
      nativeSegmentAt (nativeStream t y ε N) 0 = nativeFirstObservedSegment t y ε ∧
      (nativeFirstObservedSegment t y ε).finish = nativeFirstRecording t y ε := by
  have hstream : nativeStream t y ε N = scanNative t y ε (N - 1) 0 1 (y 0) (by omega) := by
    cases N with
    | zero => omega
    | succ n => rfl
  have hhead := scanNative_head_segment_threshold t y ε K hK hcone (N - 1) 1
    (by omega) hK (by omega)
  rw [← hstream] at hhead
  have hobs := nativeFirstObservedSegment_eq_threshold t y ε hK hcone
  have hrec := nativeFirstRecording_eq_threshold t y ε hK hcone
  have hfinish : (nativeFirstObservedSegment t y ε).finish = nativeFirstRecording t y ε := by
    rw [hobs, hrec]
    rfl
  refine ⟨?_, ?_, hfinish⟩
  · cases he : nativeStream t y ε N with
    | nil => simp only [he, List.head?_nil, reduceCtorEq] at hhead
    | cons a as => simp only [List.length_cons]; omega
  · rw [nativeSegmentAt, ← List.head?_eq_getElem?, hhead, Option.getD_some, hobs]

/-- On a horizon beyond the finite pinch the actual output's first entry is
eventually the independently observed first native recording and SSE line. -/
theorem eventually_nativeMesh_first (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    {ε H : ℝ} (hε : 0 ≤ ε) (hfinite : anchoredLifetime f ε ≠ ∞)
    (hH : (anchoredLifetime f ε).toReal < H)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0} (hh : ∀ i, h i ≠ 0)
    (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    ∀ᶠ i in l, 0 < (nativeMeshStream f ε H (h i)).length ∧
      nativeMeshSegment f ε H (h i) 0 = nativeFirstObservedSegment
        (fun j => (j : ℝ) * h i) (fun j => f ((j : ℝ) * h i)) ε ∧
      (nativeMeshSegment f ε H (h i) 0).finish = nativeFirstRecording
        (fun j => (j : ℝ) * h i) (fun j => f ((j : ℝ) * h i)) ε := by
  have hp (i : ι) : 0 < (h i : ℝ) := by exact_mod_cast (pos_of_ne_zero (hh i))
  have hlife := tendsto_finiteMeshAnchoredLifetime f ε hp hconv
  have hfin : ∀ᶠ i in l, finiteMeshAnchoredLifetime f (h i) ε ≠ ∞ :=
    (hlife.eventually_lt_const (lt_top_iff_ne_top.mpr hfinite)).mono (fun _ hi => hi.ne)
  have hrec := tendsto_nativeFirstRecording_mesh f hf hε hfinite hh hconv
  have hlast := tendsto_mesh_floor_time hp hconv
    (show 0 ≤ H from ENNReal.toReal_nonneg.trans hH.le)
  filter_upwards [hfin,
    hrec.eventually_lt_const (show (anchoredLifetime f ε).toReal <
      ((anchoredLifetime f ε).toReal + H) / 2 by linarith),
    hlast.eventually_const_lt (show ((anchoredLifetime f ε).toReal + H) / 2 < H by linarith)]
      with i hi hr hN
  have hgap : nativeFirstRecording (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε < ⌊H / (h i : ℝ)⌋₊ := by
    have hmul : (nativeFirstRecording (fun j => (j : ℝ) * h i)
        (fun j => f ((j : ℝ) * h i)) ε : ℝ) < (⌊H / (h i : ℝ)⌋₊ : ℝ) := by
      have := hp i
      nlinarith
    exact_mod_cast hmul
  obtain ⟨K, hK, hcone⟩ := exists_nativeGrid_threshold f hf (h i) (hh i) hε hi
  have hc : ∀ j, nativePrefixFeasible (fun n => (n : ℝ) * h i)
      (fun n => f ((n : ℝ) * h i)) ε 0 j (f ((0 : ℕ) * h i)) ↔ j < K := by
    simpa only [Nat.cast_zero, zero_mul] using hcone
  rw [nativeFirstRecording_eq_threshold _ _ ε hK hc] at hgap
  have hm := nativeStream_first_eq_threshold _ _ ε hK hc (show K ≤ ⌊H / (h i : ℝ)⌋₊ by omega)
  exact ⟨hm.1, hm.2.1, (congrArg NativeSegment.finish hm.2.1).trans hm.2.2⟩

/-- For the actual constrained-SSE native stream, every fixed recording
collapses to the finite continuous pinch and the terminal errors alternate. -/
theorem nativeMesh_fixed_index_degeneracy (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    {ε H : ℝ} (hε : 0 < ε) {σ : ℝ≥0} (hσ : anchoredLifetime f ε = σ)
    (hH : (σ : ℝ) < H) {a : ℝ}
    (ha : ∀ t : Icc (0 : ℝ) (σ : ℝ), |f t - a * (t : ℝ)| ≤ ε)
    (hno : ∀ q : ℝ, |f σ - q| = ε → ∀ T : ℝ, 0 < T → ¬ ∃ b,
      continuousSlopeFeasible (fun t => f ((σ : ℝ) + t)) q ε T b)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0} (hh : ∀ i, h i ≠ 0)
    (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    ∀ k : ℕ,
      (∀ᶠ i in l, k + 1 < (nativeMeshStream f ε H (h i)).length) ∧
      Tendsto (fun i => nativeMeshEndpointTime f ε H (h i) k) l (𝓝 (σ : ℝ)) ∧
      Tendsto (fun i => nativeMeshEndpointOffset f ε H (h i) k)
        l (𝓝 ((-1 : ℝ) ^ k * (a * (σ : ℝ) - f σ))) := by
  have hp (i : ι) : 0 < (h i : ℝ) := by exact_mod_cast (pos_of_ne_zero (hh i))
  have hfinite : anchoredLifetime f ε ≠ ∞ := by rw [hσ]; exact ENNReal.coe_ne_top
  have hη : |a * (σ : ℝ) - f σ| = ε := by
    rw [abs_sub_comm]
    exact anchored_fit_terminal_boundary f (by simp only [hf, abs_zero]; exact hε.le) hσ ha
  have hfirst := eventually_nativeMesh_first f hf hε.le hfinite
    (by simpa only [hσ, ENNReal.coe_toReal] using hH) hh hconv
  have ht : Tendsto (fun i => nativeMeshEndpointTime f ε H (h i) 0) l (𝓝 (σ : ℝ)) := by
    have ht0 := tendsto_nativeFirstRecording_mesh f hf hε.le hfinite hh hconv
    simp only [hσ, ENNReal.coe_toReal] at ht0
    apply ht0.congr'
    filter_upwards [hfirst] with i hi
    dsimp only [nativeMeshEndpointTime]
    rw [hi.2.2, mul_comm]
  have ho : Tendsto (fun i => nativeMeshEndpointOffset f ε H (h i) 0)
      l (𝓝 (a * (σ : ℝ) - f σ)) := by
    have ho0 := (tendsto_nativeFirstNormalizedOffset_mesh f hf hε hσ ha hh hconv).mul_const ε
    simp only [div_mul_cancel₀ _ hε.ne'] at ho0
    apply ho0.congr'
    filter_upwards [hfirst] with i hi
    dsimp only [nativeMeshEndpointOffset, nativeMeshEndpointTime]
    rw [hi.2.1]
    exact div_mul_cancel₀ _ hε.ne'
  exact nativeChain_fixed_index_degeneracy f hε σ.property hH hη hno hp hconv
    (Eventually.of_forall (fun i => by
      simpa only [nativeMeshStream, Nat.cast_zero, zero_mul] using nativeStream_spec (fun j => (j : ℝ) * h i)
        (fun j => f ((j : ℝ) * h i)) (strictMono_mesh_times (hp i)) hε.le ⌊H / (h i : ℝ)⌋₊))
    (tendsto_mesh_floor_time hp hconv (σ.property.trans hH.le))
    (hfirst.mono (fun _ hi => hi.1)) ht ho

/-- The number of actual non-EOF recordings diverges on every horizon beyond
the pinch. This is a pathwise consequence of existence of all fixed indices. -/
theorem tendsto_nativeCompletedCount_atTop (f : C(ℝ, ℝ)) (hf : f 0 = 0)
    {ε H : ℝ} (hε : 0 < ε) {σ : ℝ≥0} (hσ : anchoredLifetime f ε = σ)
    (hH : (σ : ℝ) < H) {a : ℝ}
    (ha : ∀ t : Icc (0 : ℝ) (σ : ℝ), |f t - a * (t : ℝ)| ≤ ε)
    (hno : ∀ q : ℝ, |f σ - q| = ε → ∀ T : ℝ, 0 < T → ¬ ∃ b,
      continuousSlopeFeasible (fun t => f ((σ : ℝ) + t)) q ε T b)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0} (hh : ∀ i, h i ≠ 0)
    (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    Tendsto (fun i => nativeCompletedCount (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε ⌊H / (h i : ℝ)⌋₊) l atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(nativeMesh_fixed_index_degeneracy f hf hε hσ hH ha hno hh hconv b).1] with i hi
  change b ≤ (nativeMeshStream f ε H (h i)).length - 1
  omega

def brownianNativeMeshStream {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (ε H : ℝ) (h : ℝ≥0) (ω : Ω) : List NativeSegment :=
  nativeStream (fun j => (j : ℝ) * h) (fun j => B ((j : ℝ≥0) * h) ω) ε ⌊H / (h : ℝ)⌋₊

def brownianNativeMeshSegment {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (ε H : ℝ) (h : ℝ≥0) (k : ℕ) (ω : Ω) : NativeSegment :=
  nativeSegmentAt (brownianNativeMeshStream B ε H h ω) k

def brownianNativeMeshEndpointTime {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (ε H : ℝ) (h : ℝ≥0) (k : ℕ) (ω : Ω) : ℝ :=
  ((brownianNativeMeshSegment B ε H h k ω).finish : ℝ) * h

/-- Normalized fitted-minus-observed endpoint error, with the manuscript sign. -/
def brownianNativeMeshEndpointOffset {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (ε H : ℝ) (h : ℝ≥0) (k : ℕ) (ω : Ω) : ℝ :=
  (nativeSegmentEndpoint (fun j => (j : ℝ) * h) (brownianNativeMeshSegment B ε H h k ω) -
    B (((brownianNativeMeshSegment B ε H h k ω).finish : ℝ≥0) * h) ω) / ε

theorem brownianNativeMeshStream_eq_processPath {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hc : Continuous (fun t => B t ω)) (ε H : ℝ) (h : ℝ≥0) :
    brownianNativeMeshStream B ε H h ω = nativeMeshStream (processPath B ω) ε H h := by
  unfold brownianNativeMeshStream nativeMeshStream
  congr 1
  funext j
  simpa only [NNReal.coe_mul, NNReal.coe_natCast] using!
    (processPath_apply_of_continuous hc ((j : ℝ≥0) * h)).symm

theorem brownianNativeMeshEndpointTime_eq_processPath {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hc : Continuous (fun t => B t ω)) (ε H : ℝ) (h : ℝ≥0) (k : ℕ) :
    brownianNativeMeshEndpointTime B ε H h k ω = nativeMeshEndpointTime (processPath B ω) ε H h k := by
  simp only [brownianNativeMeshEndpointTime, brownianNativeMeshSegment,
    brownianNativeMeshStream_eq_processPath hc, nativeMeshEndpointTime, nativeMeshSegment]

theorem brownianNativeMeshEndpointOffset_eq_processPath {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hc : Continuous (fun t => B t ω)) (ε H : ℝ) (h : ℝ≥0) (k : ℕ) :
    brownianNativeMeshEndpointOffset B ε H h k ω =
      nativeMeshEndpointOffset (processPath B ω) ε H h k / ε := by
  simp only [brownianNativeMeshEndpointOffset, brownianNativeMeshSegment,
    brownianNativeMeshStream_eq_processPath hc, nativeMeshEndpointOffset,
    nativeMeshEndpointTime, nativeMeshSegment]
  congr 2
  simpa only [NNReal.coe_mul, NNReal.coe_natCast] using!
    (processPath_apply_of_continuous hc
      (((nativeSegmentAt (nativeMeshStream (processPath B ω) ε H h) k).finish : ℝ≥0) * h)).symm

/-- Actual Brownian samples and actual selected native lines, simultaneously
at every fixed index and every horizon strictly past the first pinch. The
existence and alternation of the sign do not assert its fairness or independence. -/
theorem brownian_native_fixed_index_degeneracy_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0}
    (hh : ∀ i, h i ≠ 0) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∃ S : ℝ, (S = 1 ∨ S = -1) ∧
      ∀ H : ℝ, (anchoredProcessLifetime B ε ω).toReal < H → ∀ k : ℕ,
        (∀ᶠ i in l, k + 1 < (brownianNativeMeshStream B ε H (h i) ω).length) ∧
        Tendsto (fun i => brownianNativeMeshEndpointTime B ε H (h i) k ω) l
          (𝓝 (anchoredProcessLifetime B ε ω).toReal) ∧
        Tendsto (fun i => brownianNativeMeshEndpointOffset B ε H (h i) k ω) l
          (𝓝 ((-1 : ℝ) ^ k * S)) := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
    anchoredProcessLifetime_tolerance_ae_ne_top hB hε,
    brownian_boundary_no_extension_real_ae hB hε] with ω hc hz hf hno
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hσ' : anchoredLifetime (processPath B ω) ε = (σ : ℝ≥0∞) := hσ.symm
  have hr : (anchoredProcessLifetime B ε ω).toReal = (σ : ℝ) := by rw [← hσ]; rfl
  have hzero : processPath B ω 0 = 0 := (processPath_apply_of_continuous hc 0).trans hz
  have hzero' : |processPath B ω 0| < ε := by rw [hzero, abs_zero]; exact hε
  obtain ⟨a, ha, _⟩ := existsUnique_anchored_fit_at_lifetime (processPath B ω) hzero' hσ'
  refine ⟨(a * (σ : ℝ) - processPath B ω σ) / ε,
    nativeFirst_limit_offset_sign (processPath B ω) hzero hε hσ' ha, ?_⟩
  intro H hH k
  have hk := nativeMesh_fixed_index_degeneracy (processPath B ω) hzero hε hσ'
    (by simpa only [hr] using hH) ha (by simpa only [hr] using hno) hh hconv k
  refine ⟨?_, ?_, ?_⟩
  · simpa only [brownianNativeMeshStream_eq_processPath hc] using hk.1
  · simpa only [brownianNativeMeshEndpointTime_eq_processPath hc, hr] using hk.2.1
  · have ho := hk.2.2.div_const ε
    simpa only [brownianNativeMeshEndpointOffset_eq_processPath hc, mul_div_assoc] using ho

/-- Theorem 2.2 count-divergence branch, using the actual finite native stream. -/
theorem brownian_nativeCompletedCount_atTop_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0}
    (hh : ∀ i, h i ≠ 0) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ H : ℝ, (anchoredProcessLifetime B ε ω).toReal < H →
      Tendsto (fun i => nativeCompletedCount (fun j => (j : ℝ) * h i)
        (fun j => B ((j : ℝ≥0) * h i) ω) ε ⌊H / (h i : ℝ)⌋₊) l atTop := by
  filter_upwards [brownian_native_fixed_index_degeneracy_ae hB hε hh hconv] with ω hω
  obtain ⟨S, _, hS⟩ := hω
  intro H hH
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(hS H hH b).1] with i hi
  change b ≤ (brownianNativeMeshStream B ε H (h i) ω).length - 1
  omega

def brownianNativeMeshDuration {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (ε H : ℝ) (h : ℝ≥0) (k : ℕ) (ω : Ω) : ℝ :=
  ((brownianNativeMeshSegment B ε H h k ω).finish : ℝ) * h -
    ((brownianNativeMeshSegment B ε H h k ω).start : ℝ) * h

/-- The actual first duration tends to the pinch lifetime; every subsequent
fixed duration tends to zero. The output chain supplies the true junctions. -/
theorem brownian_native_duration_limits_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0}
    (hh : ∀ i, h i ≠ 0) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ H : ℝ, (anchoredProcessLifetime B ε ω).toReal < H →
      Tendsto (fun i => brownianNativeMeshDuration B ε H (h i) 0 ω) l
        (𝓝 (anchoredProcessLifetime B ε ω).toReal) ∧
      ∀ k : ℕ, Tendsto (fun i => brownianNativeMeshDuration B ε H (h i) (k + 1) ω) l (𝓝 0) := by
  filter_upwards [brownian_native_fixed_index_degeneracy_ae hB hε hh hconv] with ω hω
  obtain ⟨S, _, hS⟩ := hω
  intro H hH
  have hc (i : ι) := nativeStream_spec (fun j => (j : ℝ) * h i)
    (fun j => B ((j : ℝ≥0) * h i) ω)
    (strictMono_mesh_times (show (0 : ℝ≥0) < h i from pos_iff_ne_zero.mpr (hh i)))
    hε.le ⌊H / (h i : ℝ)⌋₊
  constructor
  · apply (hS H hH 0).2.1.congr'
    filter_upwards [(hS H hH 0).1] with i hi
    have hi' : 0 < (brownianNativeMeshStream B ε H (h i) ω).length := by omega
    have hz := (hc i).getElem_zero hi'
    dsimp only [brownianNativeMeshEndpointTime, brownianNativeMeshDuration,
      brownianNativeMeshSegment]
    rw [nativeSegmentAt_eq_getElem hi']
    simp only [brownianNativeMeshStream, hz.1, Nat.cast_zero, zero_mul, sub_zero]
  · intro k
    have ht := (hS H hH (k + 1)).2.1.sub (hS H hH k).2.1
    simp only [sub_self] at ht
    apply ht.congr'
    filter_upwards [(hS H hH k).1] with i hi
    have hj := (hc i).getElem_succ hi
    dsimp only [brownianNativeMeshEndpointTime, brownianNativeMeshDuration,
      brownianNativeMeshSegment]
    rw [nativeSegmentAt_eq_getElem hi,
      nativeSegmentAt_eq_getElem (show k < (brownianNativeMeshStream B ε H (h i) ω).length by omega)]
    simp only [brownianNativeMeshStream, hj.1]

/-- Every fixed completed native segment nevertheless accepts arbitrarily
many new samples as the mesh vanishes. -/
theorem brownian_native_accepted_count_atTop_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) {ι : Type*} {l : Filter ι} {h : ι → ℝ≥0}
    (hh : ∀ i, h i ≠ 0) (hconv : Tendsto (fun i => (h i : ℝ)) l (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ H : ℝ, (anchoredProcessLifetime B ε ω).toReal < H → ∀ k : ℕ,
      Tendsto (fun i => (brownianNativeMeshSegment B ε H (h i) k ω).finish -
        (brownianNativeMeshSegment B ε H (h i) k ω).start) l atTop := by
  filter_upwards [hB.cont, brownian_native_fixed_index_degeneracy_ae hB hε hh hconv] with ω hc hω
  obtain ⟨S, _, hS⟩ := hω
  intro H hH k
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg.trans hH.le
  have hp (i : ι) : 0 < (h i : ℝ) := by exact_mod_cast (pos_of_ne_zero (hh i))
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [(hS H hH k).1,
    eventually_native_completed_spans_ge (processPath B ω) hH0 hε hp hconv n] with i hi hu
  rw [brownianNativeMeshStream_eq_processPath hc] at hi
  have hn := nativeStream_spec (fun j => (j : ℝ) * h i)
    (fun j => processPath B ω ((j : ℝ) * h i)) (strictMono_mesh_times (hp i)) hε.le
    ⌊H / (h i : ℝ)⌋₊
  have hk : k < (nativeMeshStream (processPath B ω) ε H (h i)).length := by omega
  have hb := hn.getElem_bounds hk
  have hq := hn.getElem_anchor_error (by simp only [sub_self, abs_zero]; exact hε.le) hk
  have hr := hn.getElem_reject hi
  simp only [brownianNativeMeshSegment, brownianNativeMeshStream_eq_processPath hc,
    nativeSegmentAt_eq_getElem hk]
  apply hu _ _ hb.2.2 _ _ hq hr
  have hsN := hb.2.2.le.trans hb.2.1
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hsN) (hp i).le).trans
    (meshFloor_mul_le hH0 (hp i))

end SwingRepair
