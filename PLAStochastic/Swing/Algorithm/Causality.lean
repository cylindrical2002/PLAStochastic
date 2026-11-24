import PLAStochastic.Swing.Algorithm.Stream

/-!
# Finite-observation causality of the native fitted recursion

The actual constrained least-squares selection and every accept/reject branch
depend only on observations through the supplied final index. These statements
allow both the timestamps and sample values beyond that index to change.
-/

namespace SwingRepair

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false

theorem nativeSelectedSlope_congr {ι : Type*} (samples : Finset ι)
    (hne : samples.Nonempty) {t t' y y' : ι → ℝ} (a q ε : ℝ)
    (ht : ∀ i ∈ samples, t i = t' i) (hy : ∀ i ∈ samples, y i = y' i) :
    nativeSelectedSlope samples hne t y a q ε =
      nativeSelectedSlope samples hne t' y' a q ε := by
  have hL : nativeConeLower samples hne t y a q ε =
      nativeConeLower samples hne t' y' a q ε := by
    apply Finset.sup'_congr hne rfl
    intro i hi
    rw [ht i hi, hy i hi]
  have hU : nativeConeUpper samples hne t y a q ε =
      nativeConeUpper samples hne t' y' a q ε := by
    apply Finset.inf'_congr hne rfl
    intro i hi
    rw [ht i hi, hy i hi]
  have hC : nativeSSECross samples t y a q = nativeSSECross samples t' y' a q := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ht i hi, hy i hi]
  have hD : nativeSSETimeSquare samples t a = nativeSSETimeSquare samples t' a := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ht i hi]
  simp only [nativeSelectedSlope, hL, hU, nativeLeastSquares, hC, hD]

theorem nativePrefixFeasible_prefix_congr {t t' y y' : ℕ → ℝ}
    (ε : ℝ) {s e N : ℕ} (q : ℝ) (hs : s ≤ N) (he : e ≤ N)
    (ht : ∀ i ≤ N, t i = t' i) (hy : ∀ i ≤ N, y i = y' i) :
    nativePrefixFeasible t y ε s e q ↔ nativePrefixFeasible t' y' ε s e q := by
  unfold nativePrefixFeasible feasibleSlope
  have heq : ∀ i ∈ Finset.Icc (s + 1) e,
      y i = y' i ∧ t i = t' i := by
    intro i hi
    exact ⟨hy i ((Finset.mem_Icc.mp hi).2.trans he),
      ht i ((Finset.mem_Icc.mp hi).2.trans he)⟩
  simp only [ht s hs]
  constructor <;> rintro ⟨m, hm⟩ <;> refine ⟨m, fun i hi => ?_⟩
  · simpa only [(heq i hi).1, (heq i hi).2] using hm i hi
  · simpa only [(heq i hi).1, (heq i hi).2] using hm i hi

theorem nativeOutputSegment_prefix_congr {t t' y y' : ℕ → ℝ}
    (ε : ℝ) {s e N : ℕ} (q : ℝ) (hse : s < e) (he : e ≤ N)
    (ht : ∀ i ≤ N, t i = t' i) (hy : ∀ i ≤ N, y i = y' i) :
    nativeOutputSegment t y ε s e q hse = nativeOutputSegment t' y' ε s e q hse := by
  unfold nativeOutputSegment
  have hanchor := ht s (hse.le.trans he)
  rw [hanchor]
  congr 1
  apply nativeSelectedSlope_congr
  · intro i hi
    exact ht i ((Finset.mem_Icc.mp hi).2.trans he)
  · intro i hi
    exact hy i ((Finset.mem_Icc.mp hi).2.trans he)

theorem nativeSegmentEndpoint_prefix_congr {t t' : ℕ → ℝ}
    (seg : NativeSegment) {N : ℕ} (hs : seg.start ≤ N) (he : seg.finish ≤ N)
    (ht : ∀ i ≤ N, t i = t' i) :
    nativeSegmentEndpoint t seg = nativeSegmentEndpoint t' seg := by
  simp only [nativeSegmentEndpoint, ht seg.start hs, ht seg.finish he]

/-- Changing unobserved data leaves the full fitted recursion unchanged. -/
theorem scanNative_prefix_congr {t t' y y' : ℕ → ℝ} (ε : ℝ)
    (fuel s e : ℕ) (q : ℝ) (hse : s < e) {N : ℕ} (hN : e + fuel ≤ N)
    (ht : ∀ i ≤ N, t i = t' i) (hy : ∀ i ≤ N, y i = y' i) :
    scanNative t y ε fuel s e q hse = scanNative t' y' ε fuel s e q hse := by
  induction fuel generalizing s e q with
  | zero =>
      simp only [scanNative]
      rw [nativeOutputSegment_prefix_congr ε q hse (by omega) ht hy]
  | succ fuel ih =>
      have hc := nativePrefixFeasible_prefix_congr ε q (by omega : s ≤ N)
        (by omega : e + 1 ≤ N) ht hy
      by_cases ha : nativePrefixFeasible t y ε s (e + 1) q
      · simp only [scanNative, if_pos ha, if_pos (hc.mp ha)]
        exact ih s (e + 1) q (hse.trans (Nat.lt_succ_self e)) (by omega)
      · have ha' : ¬nativePrefixFeasible t' y' ε s (e + 1) q := fun h => ha (hc.mpr h)
        simp only [scanNative, if_neg ha, if_neg ha']
        have hseg := nativeOutputSegment_prefix_congr ε q hse (by omega : e ≤ N) ht hy
        rw [hseg]
        congr 1
        have hend := nativeSegmentEndpoint_prefix_congr
          (nativeOutputSegment t' y' ε s e q hse) (by exact hse.le.trans (by omega))
          (by exact (show e ≤ N by omega)) ht
        rw [hend]
        exact ih e (e + 1) _ (Nat.lt_succ_self e) (by omega)

/-- Native output is determined by samples and timestamps `0,...,last`. -/
theorem nativeStream_prefix_congr {t t' y y' : ℕ → ℝ} (ε : ℝ) (last : ℕ)
    (ht : ∀ i ≤ last, t i = t' i) (hy : ∀ i ≤ last, y i = y' i) :
    nativeStream t y ε last = nativeStream t' y' ε last := by
  cases last with
  | zero => rfl
  | succ n =>
      simp only [nativeStream, hy 0 (Nat.zero_le _)]
      exact scanNative_prefix_congr ε n 0 1 (y' 0) (by omega) (by omega) ht hy

end

end SwingRepair
