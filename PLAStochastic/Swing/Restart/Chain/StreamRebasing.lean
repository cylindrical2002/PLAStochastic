import PLAStochastic.Swing.Restart.Chain.StoppingRecursion
import PLAStochastic.Swing.DenseSampling.Segments.Permanence

/-! Exact pathwise rebasing of every constrained-SSE segment.  The inherited
state is the already observed first sample minus the fitted recording. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set Finset
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem feasibleSlope_native_rebase (y D : ℕ → ℝ) (E q m : ℝ) (s n : ℕ)
    (hD : ∀ j, 1 ≤ j → D j = y (s+j)-q) :
    feasibleSlope (Finset.Icc (s+1) (s+n)) (fun j => (j : ℝ)) y (s : ℝ) q E m ↔
      feasibleSlope (Finset.Icc 1 n) (fun j => (j : ℝ)) D 0 0 E m := by
  constructor
  · intro h j hj
    have hj' := Finset.mem_Icc.mp hj
    have hh := h (s+j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [hD j hj'.1]
    simp only [Nat.cast_add, add_sub_cancel_left, sub_zero, zero_add] at hh ⊢
    convert hh using 1; congr 1; ring
  · intro h j hj
    have hj' := Finset.mem_Icc.mp hj
    have hh := h (j-s) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [hD (j-s) (by omega), show s+(j-s) = j by omega] at hh
    dsimp only at hh ⊢
    rw [Nat.cast_sub (by omega : s ≤ j)] at hh
    simpa only [sub_zero, zero_add, sub_sub] using hh

theorem nativePrefixFeasible_rebase (y D : ℕ → ℝ) (E q : ℝ) (s n : ℕ)
    (hD : ∀ j, 1 ≤ j → D j = y (s+j)-q) :
    nativePrefixFeasible (fun j => (j : ℝ)) y E s (s+n) q ↔
      nativePrefixFeasible (fun j => (j : ℝ)) D E 0 n 0 := by
  exact exists_congr fun m => by
    simpa only [Nat.cast_zero, Nat.zero_add] using feasibleSlope_native_rebase y D E q m s n hD

theorem nativeSSE_rebase (y D : ℕ → ℝ) (q m : ℝ) (s n : ℕ)
    (hD : ∀ j, 1 ≤ j → D j = y (s+j)-q) :
    nativeSSE (Finset.Icc (s+1) (s+n)) (fun j => (j : ℝ)) y (s : ℝ) q m =
      nativeSSE (Finset.Icc 1 n) (fun j => (j : ℝ)) D 0 0 m := by
  symm
  apply Finset.sum_bij (fun j _ => s+j)
  · intro j hj
    have := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j _ k _ h
    omega
  · intro j hj
    have := Finset.mem_Icc.mp hj
    exact ⟨j-s, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    rw [hD j hj'.1]
    push_cast
    ring

theorem nativeSelectedSlope_rebase (y D : ℕ → ℝ) (E q : ℝ) (s n : ℕ)
    (hn : 0 < n) (hD : ∀ j, 1 ≤ j → D j = y (s+j)-q)
    (hfeas : nativePrefixFeasible (fun j => (j : ℝ)) y E s (s+n) q) :
    nativeSelectedSlope (Finset.Icc (s+1) (s+n))
        (Finset.nonempty_Icc.mpr (by omega)) (fun j => (j : ℝ)) y (s : ℝ) q E =
      nativeSelectedSlope (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn)
        (fun j => (j : ℝ)) D 0 0 E := by
  have ht : ∀ j ∈ Finset.Icc (s+1) (s+n), (s : ℝ) < j := by
    intro j hj
    exact_mod_cast (show s < j by have := Finset.mem_Icc.mp hj; omega)
  have ht' : ∀ j ∈ Finset.Icc 1 n, (0 : ℝ) < j := by
    intro j hj
    exact_mod_cast (show 0 < j by have := Finset.mem_Icc.mp hj; omega)
  have hf := (nativePrefixFeasible_rebase y D E q s n hD).mp hfeas
  simp only [nativePrefixFeasible, Nat.zero_add, Nat.cast_zero] at hf
  apply nativeSelectedSlope_unique _ _ _ _ 0 0 E _ ht'
  · exact (feasibleSlope_native_rebase y D E q _ s n hD).mp
      (nativeSelectedSlope_feasible _ _ _ _ _ _ _ ht hfeas)
  · rw [← nativeSSE_rebase y D q _ s n hD, ← nativeSSE_rebase y D q _ s n hD]
    apply nativeSelectedSlope_minimal _ _ _ _ _ _ _ _ ht
    exact (feasibleSlope_native_rebase y D E q _ s n hD).mpr
      (nativeSelectedSlope_feasible _ _ _ _ _ _ _ ht' hf)

/-- The local carried samples are exactly the original samples minus the anchor. -/
theorem nativeRestart_samples_rebase {Ω : Type*} (X : ℕ → Ω → ℝ)
    (s j : ℕ) (q : ℝ) (ω : Ω) (hj : 1 ≤ j) :
    nativeCarriedSamples (fun k => X (s+1+k))
      (fun _ => cumulativeSamples X (s+1) ω-q) j ω = cumulativeSamples X (s+j) ω-q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [nativeCarriedSamples_succ]
  rw [show s+Nat.succ k = (s+1)+k by omega, cumulativeSamples_add_shift X (s+1) k ω]
  ring

/-- Native length at any fitted anchor is the exact length of its rebased state. -/
theorem nativeRestart_feasible_iff {Ω : Type*} (X : ℕ → Ω → ℝ)
    (s n : ℕ) (E q : ℝ) (ω : Ω) :
    nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E s (s+n) q ↔
      (n : WithTop ℕ) ≤ nativeRestartLength (fun k => X (s+1+k)) E
        (cumulativeSamples X (s+1) ω-q) ω := by
  rw [nativeRestartLength, le_nativePrefixLength_iff]
  exact nativePrefixFeasible_rebase _ _ E q s n (fun j hj => nativeRestart_samples_rebase X s j q ω hj)

/-- A valid completed segment has exactly the maximal rebased restart length. -/
theorem nativeRestartLength_eq_of_segment {Ω : Type*} (X : ℕ → Ω → ℝ)
    (E : ℝ) (ω : Ω) (seg : NativeSegment)
    (hv : NativeSegmentValid (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E seg)
    (hr : ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω)
      E seg.start (seg.finish+1) seg.anchorValue) :
    nativeRestartLength (fun j => X (seg.start+1+j)) E
        (cumulativeSamples X (seg.start+1) ω-seg.anchorValue) ω =
      ((seg.finish-seg.start : ℕ) : WithTop ℕ) := by
  let n := seg.finish-seg.start
  have hsn : seg.start+n = seg.finish := by dsimp [n]; have := hv.positive; omega
  have hlo : (n : WithTop ℕ) ≤ nativeRestartLength (fun j => X (seg.start+1+j)) E
      (cumulativeSamples X (seg.start+1) ω-seg.anchorValue) ω := by
    apply (nativeRestart_feasible_iff X seg.start n E seg.anchorValue ω).mp
    rw [hsn]
    exact ⟨seg.slope, hv.feasible⟩
  have hhi : ¬ ((n+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength (fun j => X (seg.start+1+j)) E
      (cumulativeSamples X (seg.start+1) ω-seg.anchorValue) ω := by
    intro h
    apply hr
    have hh := (nativeRestart_feasible_iff X seg.start (n+1) E seg.anchorValue ω).mpr h
    simpa only [← Nat.add_assoc, hsn] using hh
  cases hN : nativeRestartLength (fun j => X (seg.start+1+j)) E
      (cumulativeSamples X (seg.start+1) ω-seg.anchorValue) ω using WithTop.recTopCoe with
  | top => simp [hN] at hhi
  | coe k =>
    rw [hN] at hlo hhi
    have h1 : n ≤ k := WithTop.coe_le_coe.mp hlo
    have h2 : ¬ n+1 ≤ k := fun h => hhi (WithTop.coe_le_coe.mpr h)
    congr 1
    change k = n
    omega

/-- SSE uniqueness identifies the slope of a completed output segment with the
actual local update used by the restart kernel. -/
theorem nativeRestartSlope_eq_of_segment {Ω : Type*} (X : ℕ → Ω → ℝ)
    (E : ℝ) (ω : Ω) (seg : NativeSegment)
    (hv : NativeSegmentValid (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E seg)
    (hr : ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω)
      E seg.start (seg.finish+1) seg.anchorValue) :
    nativeRestartSlope (fun j => X (seg.start+1+j)) E
        (cumulativeSamples X (seg.start+1) ω-seg.anchorValue) ω = seg.slope := by
  let n := seg.finish-seg.start
  have hn : 0 < n := by dsimp [n]; have := hv.positive; omega
  have hsn : seg.start+n = seg.finish := by dsimp [n]; have := hv.positive; omega
  have hlen : nativeRestartLengthNat (fun j => X (seg.start+1+j)) E
      (cumulativeSamples X (seg.start+1) ω-seg.anchorValue) ω = n := by
    change (nativeRestartLength _ _ _ _).untopD 0 = n
    rw [nativeRestartLength_eq_of_segment X E ω seg hv hr]
    rfl
  rw [nativeRestartSlope, hlen, nativeRestartSlopeAt, dif_pos hn]
  have heq := nativeSelectedSlope_rebase (fun j => cumulativeSamples X j ω)
    (fun j => nativeCarriedSamples (fun j => X (seg.start+1+j))
      (fun _ => cumulativeSamples X (seg.start+1) ω-seg.anchorValue) j ω)
    E seg.anchorValue seg.start n hn
    (fun j hj => nativeRestart_samples_rebase X seg.start j seg.anchorValue ω hj)
    (by rw [hsn]; exact ⟨seg.slope, hv.feasible⟩)
  simp only [hsn] at heq
  rw [← heq]
  symm
  have ht : ∀ j ∈ Finset.Icc (seg.start+1) seg.finish, (seg.start : ℝ) < (j : ℝ) := by
    intro j hj
    exact_mod_cast (show seg.start < j by have := Finset.mem_Icc.mp hj; omega)
  exact nativeSelectedSlope_unique _ _ _ _ _ _ _ _ ht hv.feasible
    (hv.optimal _ (nativeSelectedSlope_feasible _ _ _ _ _ _ _ ht ⟨seg.slope, hv.feasible⟩))

/-- The next state is the rejected sample minus the actual selected endpoint. -/
theorem nativeRestartNext_eq_of_segment {Ω : Type*} (X : ℕ → Ω → ℝ)
    (E : ℝ) (ω : Ω) (seg : NativeSegment)
    (hv : NativeSegmentValid (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E seg)
    (hr : ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω)
      E seg.start (seg.finish+1) seg.anchorValue) :
    nativeRestartNext (fun j => X (seg.start+1+j)) E
        (cumulativeSamples X (seg.start+1) ω-seg.anchorValue) ω =
      cumulativeSamples X (seg.finish+1) ω-nativeSegmentEndpoint (fun j => (j : ℝ)) seg := by
  let n := seg.finish-seg.start
  have hsn : seg.start+1+n = seg.finish+1 := by dsimp [n]; have := hv.positive; omega
  have hlen : nativeRestartLengthNat (fun j => X (seg.start+1+j)) E
      (cumulativeSamples X (seg.start+1) ω-seg.anchorValue) ω = n := by
    change (nativeRestartLength _ _ _ _).untopD 0 = n
    rw [nativeRestartLength_eq_of_segment X E ω seg hv hr]
    rfl
  rw [nativeRestartNext, hlen, nativeRestartSlope_eq_of_segment X E ω seg hv hr]
  have hsum := cumulativeSamples_add_shift X (seg.start+1) n ω
  rw [hsn] at hsum
  rw [hsum]
  dsimp [nativeSegmentEndpoint, n]
  rw [Nat.cast_sub hv.positive.le]
  ring

/-- Every completed segment of the actual finite stream realizes the duration
and state update defining `nativeRestartKernel`. -/
theorem nativeStream_completed_restart {Ω : Type*} (X : ℕ → Ω → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (ω : Ω) (last k : ℕ)
    (hk : k+1 < (nativeStream (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E last).length) :
    let seg := (nativeStream (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω) E last)[k]'(by omega)
    nativeRestartLength (fun j => X (seg.start+1+j)) E
        (cumulativeSamples X (seg.start+1) ω-seg.anchorValue) ω =
      ((seg.finish-seg.start : ℕ) : WithTop ℕ) ∧
    nativeRestartNext (fun j => X (seg.start+1+j)) E
        (cumulativeSamples X (seg.start+1) ω-seg.anchorValue) ω =
      cumulativeSamples X (seg.finish+1) ω-nativeSegmentEndpoint (fun j => (j : ℝ)) seg := by
  have hc := nativeStream_spec (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω)
    (fun i j hij => by change (i : ℝ) < (j : ℝ); exact_mod_cast hij) hE last
  exact ⟨nativeRestartLength_eq_of_segment X E ω _ (hc.getElem_valid (by omega)) (hc.getElem_reject hk),
    nativeRestartNext_eq_of_segment X E ω _ (hc.getElem_valid (by omega)) (hc.getElem_reject hk)⟩

end SwingRepair
