import PLAStochastic.Swing.Restart.Chain.ClockFiniteness

/-! The actual native recording states have the iterated constrained-SSE kernel
law, with the observed rejection retained at every transition. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set Filter
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem nativeRecordingTime_mono_index {Ω : Type*} (X : ℕ → Ω → ℝ)
    (E : ℝ) (ω : Ω) {k l : ℕ} (hkl : k ≤ l) :
    nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E k ω ≤
      nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E l ω := by
  cases ht : nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E l ω using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    apply (nativeRecordingTime_le_iff _ _ _ k n ω).mpr
    have hh := (nativeRecordingTime_le_iff (fun j => (j : ℝ)) (cumulativeSamples X) E l n ω).mp ht.le
    omega

/-- At consecutive finite true recording clocks, the observable state update
is exactly the kernel's deterministic constrained-SSE map. -/
theorem nativeRestartRecordingState_succ_pathwise {Ω : Type*} (X : ℕ → Ω → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (ω : Ω) (k s e : ℕ)
    (hs : nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E k ω = (s : WithTop ℕ))
    (he : nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E (k+1) ω = (e : WithTop ℕ)) :
    nativeRestartRecordingState X E (k+1) ω =
      nativeRestartNext (fun j => X (s+1+j)) E (nativeRestartRecordingState X E k ω) ω ∧
    nativeRestartLength (fun j => X (s+1+j)) E (nativeRestartRecordingState X E k ω) ω =
      ((e-s : ℕ) : WithTop ℕ) := by
  let t : ℕ → ℝ := fun j => j
  let y : ℕ → ℝ := fun j => cumulativeSamples X j ω
  let segs := nativeStream t y E (e+1)
  have ht : StrictMono t := fun i j hij => by change (i : ℝ) < (j : ℝ); exact_mod_cast hij
  have hse : s ≤ e := by
    have hh := nativeRecordingTime_mono_index X E ω (show k ≤ k+1 by omega)
    rw [hs, he] at hh
    exact WithTop.coe_le_coe.mp hh
  obtain ⟨hk, hstart, hanchor⟩ := nativeStream_after_recording X hE ω hs (H := e+1) (by omega)
  have hkn : k+1 < segs.length := (nativeRecordingTime_le_iff t (cumulativeSamples X) E (k+1) e ω).mp he.le
  have hfinish : (nativeSegmentAt segs k).finish = e := by
    simpa only [Nat.add_sub_cancel] using
      nativeRecordingTime_eq_native_finish t ht (cumulativeSamples X) hE
        (k := k+1) (r := e) (N := e+1) (by omega) le_rfl ω he
  have hc := nativeStream_spec t y ht hE (e+1)
  have hv : NativeSegmentValid t y E (nativeSegmentAt segs k) := by
    rw [nativeSegmentAt_eq_getElem hk]
    exact hc.getElem_valid hk
  have hr : ¬ nativePrefixFeasible t y E (nativeSegmentAt segs k).start
      ((nativeSegmentAt segs k).finish+1) (nativeSegmentAt segs k).anchorValue := by
    rw [nativeSegmentAt_eq_getElem hk]
    exact hc.getElem_reject hkn
  have hnext := nativeRestartNext_eq_of_segment X E ω (nativeSegmentAt segs k) hv hr
  have hlength := nativeRestartLength_eq_of_segment X E ω (nativeSegmentAt segs k) hv hr
  change (nativeSegmentAt segs k).start = s at hstart
  change (nativeSegmentAt segs k).anchorValue = nativeCarryAnchor t y E s at hanchor
  rw [hstart, hanchor, hfinish] at hlength
  rw [hstart, hanchor, hfinish] at hnext
  obtain ⟨_, hlenOld, hdrop⟩ := nativeStream_at_recordingTime t (cumulativeSamples X) E
    (k := k+1) (by omega) ω he
  have hsegEq : nativeSegmentAt segs k = nativeSegmentAt (nativeStream t y E e) k := by
    rw [← hdrop, nativeSegmentAt_dropLast hkn]
  have hend : nativeCarryAnchor t y E e = nativeSegmentEndpoint t (nativeSegmentAt segs k) := by
    unfold nativeCarryAnchor
    rw [hlenOld, Nat.add_sub_cancel, ← hsegEq]
  rw [nativeRestartRecordingState_eq_at X E k s ω hs,
    nativeRestartRecordingState_eq_at X E (k+1) e ω he]
  constructor
  · change cumulativeSamples X (e+1) ω-nativeCarryAnchor t y E e = _
    rw [hend]
    exact hnext.symm
  · exact hlength

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- Exact state recursion on one full-measure set for every segment index. -/
theorem nativeRestartRecordingState_succ_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (k : ℕ) :
    ∀ᵐ ω ∂μ, nativeRestartRecordingState X E (k+1) ω =
      nativeRestartNext nativeIncrementCoordinates E (nativeRestartRecordingState X E k ω)
        (fun j => X ((nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E k ω).untopD 0+1+j) ω) := by
  filter_upwards [nativeRecordingTime_ae_all_finite hX hi hG hE] with ω hω
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (hω k)
  obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp (hω (k+1))
  rw [← hs]
  exact (nativeRestartRecordingState_succ_pathwise X hE.le ω k s e hs.symm he.symm).1

/-- The true state law satisfies μ_(k+1) = μ_k P_E. -/
theorem nativeRestartRecordingState_law_succ
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (k : ℕ) :
    μ.map (nativeRestartRecordingState X E (k+1)) =
      nativeRestartKernel X μ E ∘ₘ μ.map (nativeRestartRecordingState X E k) := by
  rw [Measure.map_congr (nativeRestartRecordingState_succ_ae hX hi hG hE k)]
  exact nativeRestart_stopped_next_law hX hi
    (fun n => ⟨(hX n).aemeasurable, (hX 0).aemeasurable, (hG n).trans (hG 0).symm⟩)
    (nativeRecordingTime_isStoppingTime_increment X hX E k)
    ((nativeRecordingTime_ae_all_finite hX hi hG hE).mono (fun _ h => h k))
    (nativeRestartRecordingState_measurable_stopped hX E k) E

/-- The law of every actual native carried state is the k-fold iterate of the
measurable restart kernel, starting from the actual initial Gaussian increment. -/
theorem nativeRestartRecordingState_law_iterate
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (k : ℕ) :
    μ.map (nativeRestartRecordingState X E k) =
      (fun ν : Measure ℝ => nativeRestartKernel X μ E ∘ₘ ν)^[k] (gaussianReal 0 1) := by
  induction k with
  | zero => simpa only [Function.iterate_zero, id_eq] using nativeRestartRecordingState_initial_law hG E
  | succ k ih =>
    rw [nativeRestartRecordingState_law_succ hX hi hG hE k, ih, Function.iterate_succ_apply']

/-- The duration between two consecutive actual permanent recordings. -/
def nativeRecordingDurationNat (X : ℕ → Ω → ℝ) (E : ℝ) (k : ℕ) (ω : Ω) : ℕ :=
  (nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E (k+1) ω).untopD 0-
    (nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E k ω).untopD 0

/-- The actual clock increment agrees with the maximal-prefix duration at its
observed state and its own post-stopping increment sequence. -/
theorem nativeRecordingDurationNat_eq_restart_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (k : ℕ) :
    ∀ᵐ ω ∂μ, nativeRecordingDurationNat X E k ω =
      nativeRestartLengthNat nativeIncrementCoordinates E (nativeRestartRecordingState X E k ω)
        (fun j => X ((nativeRecordingTime (fun j => (j : ℝ)) (cumulativeSamples X) E k ω).untopD 0+1+j) ω) := by
  filter_upwards [nativeRecordingTime_ae_all_finite hX hi hG hE] with ω hω
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (hω k)
  obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp (hω (k+1))
  have hlen := (nativeRestartRecordingState_succ_pathwise X hE.le ω k s e hs.symm he.symm).2
  have hnat := congrArg (fun a : WithTop ℕ => a.untopD 0) hlen
  rw [nativeRecordingDurationNat, ← hs, ← he]
  exact hnat.symm

/-- Every actual segment duration has finite expectation. -/
theorem nativeRecordingDurationNat_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (k : ℕ) :
    Integrable (fun ω => (nativeRecordingDurationNat X E k ω : ℝ)) μ := by
  have hh := nativeRestart_stopped_length_integrable hX hi hG
    (nativeRecordingTime_isStoppingTime_increment X hX E k)
    ((nativeRecordingTime_ae_all_finite hX hi hG hE).mono (fun _ h => h k))
    (nativeRestartRecordingState_measurable_stopped hX E k) hE
  exact hh.congr ((nativeRecordingDurationNat_eq_restart_ae hX hi hG hE k).mono
    (fun _ h => congrArg (fun n : ℕ => (n : ℝ)) h.symm))

/-- Segment mean recursion for the actual online stream. -/
theorem nativeRecordingDurationNat_mean
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (k : ℕ) :
    (∫ ω, (nativeRecordingDurationNat X E k ω : ℝ) ∂μ) =
      ∫ x, nativeRestartMean X μ E x ∂μ.map (nativeRestartRecordingState X E k) := by
  rw [integral_congr_ae ((nativeRecordingDurationNat_eq_restart_ae hX hi hG hE k).mono
    (fun _ h => congrArg (fun n : ℕ => (n : ℝ)) h))]
  exact nativeRestart_stopped_mean hX hi hG
    (nativeRecordingTime_isStoppingTime_increment X hX E k)
    ((nativeRecordingTime_ae_all_finite hX hi hG hE).mono (fun _ h => h k))
    (nativeRestartRecordingState_measurable_stopped hX E k) hE

/-- E[N_(k+1)] = ∫ h_E(x) (μ₀ P_E^k)(dx), for every actual native segment. -/
theorem nativeRecordingDurationNat_mean_iterate
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (k : ℕ) :
    (∫ ω, (nativeRecordingDurationNat X E k ω : ℝ) ∂μ) =
      ∫ x, nativeRestartMean X μ E x
        ∂((fun ν : Measure ℝ => nativeRestartKernel X μ E ∘ₘ ν)^[k] (gaussianReal 0 1)) := by
  rw [nativeRecordingDurationNat_mean hX hi hG hE k,
    nativeRestartRecordingState_law_iterate hX hi hG hE k]

end SwingRepair
