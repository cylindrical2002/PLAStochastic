import PLAStochastic.Swing.Algorithm.Stream
import PLAStochastic.Swing.Repair.CycleCount

/-!
# The first actual native recording

The first duration is defined from the output of the existing nativeStream:
it is the least n for which processing samples 0,...,n+1 has emitted a first
recording and retained a terminal remainder. Thus the terminal EOF segment
alone does not count as a recording. The proof follows the actual scan branches.
-/

noncomputable section
open Classical
namespace SwingRepair

/-- A true-anchor native prefix at tolerance E is exactly the repair cone at final budget 2E. -/
theorem nativePrefix_trueAnchor_iff (t y : ℕ → ℝ) (ht : StrictMono t)
    (E : ℝ) (s e : ℕ) :
    nativePrefixFeasible t y E s e (y s) ↔ (prefixCone t y s e (2 * E)).Nonempty := by
  unfold nativePrefixFeasible feasibleSlope prefixCone
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j hj => ?_⟩
    have htj : t s < t j := ht (by have := (Finset.mem_Icc.mp hj).1; omega)
    simpa only [Set.mem_Icc, mul_div_cancel_left₀ E (by norm_num : (2 : ℝ) ≠ 0)] using
      (sample_error_iff_bounds htj).mp (hm j hj)
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j hj => ?_⟩
    have htj : t s < t j := ht (by have := (Finset.mem_Icc.mp hj).1; omega)
    apply (sample_error_iff_bounds htj).mpr
    simpa only [Set.mem_Icc, mul_div_cancel_left₀ E (by norm_num : (2 : ℝ) ≠ 0)] using hm j hj

/-- Every initialized scan retains at least its terminal segment. -/
theorem scanNative_nonempty (t y : ℕ → ℝ) (E : ℝ) (fuel s e : ℕ) (q : ℝ) (hse : s < e) :
    scanNative t y E fuel s e q hse ≠ [] := by
  induction fuel generalizing s e q with
  | zero => simp [scanNative]
  | succ fuel ih =>
    simp only [scanNative]
    split_ifs
    · exact ih _ _ _ _
    · exact List.cons_ne_nil _ _

/-- Before the first rejection, the actual scan contains only its terminal prefix. -/
theorem scanNative_length_one_iff_threshold (t y : ℕ → ℝ) (E : ℝ) (K : ℕ)
    (hcone : ∀ j, nativePrefixFeasible t y E 0 j (y 0) ↔ j < K)
    (fuel e : ℕ) (he : 0 < e) (heK : e < K) :
    (scanNative t y E fuel 0 e (y 0) he).length = 1 ↔ e + fuel < K := by
  induction fuel generalizing e with
  | zero => simp [scanNative, heK]
  | succ fuel ih =>
    by_cases haccept : nativePrefixFeasible t y E 0 (e + 1) (y 0)
    · have hn := ih (e + 1) (by omega) ((hcone _).mp haccept)
      simpa only [scanNative, if_pos haccept, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
    · have hK : K ≤ e + 1 := Nat.le_of_not_gt ((hcone _).not.mp haccept)
      have hnonempty := scanNative_nonempty t y E fuel e (e + 1)
        (nativeSegmentEndpoint t (nativeOutputSegment t y E 0 e (y 0) he)) (Nat.lt_succ_self e)
      have hlength : 0 < (scanNative t y E fuel e (e + 1)
        (nativeSegmentEndpoint t (nativeOutputSegment t y E 0 e (y 0) he))
          (Nat.lt_succ_self e)).length := List.length_pos_iff.mpr hnonempty
      simp only [scanNative, if_neg haccept, List.length_cons]
      omega

/-- The first segment's actual finish is the last accepted index, truncated only by EOF. -/
theorem scanNative_head_finish_threshold (t y : ℕ → ℝ) (E : ℝ) (K : ℕ)
    (hcone : ∀ j, nativePrefixFeasible t y E 0 j (y 0) ↔ j < K)
    (fuel e : ℕ) (he : 0 < e) (heK : e < K) :
    ((scanNative t y E fuel 0 e (y 0) he).head?.map NativeSegment.finish) =
      some (min (e + fuel) (K - 1)) := by
  induction fuel generalizing e with
  | zero =>
    simp only [scanNative, List.head?_cons, Option.map_some, nativeOutputSegment, Nat.add_zero]
    congr 1
    omega
  | succ fuel ih =>
    by_cases haccept : nativePrefixFeasible t y E 0 (e + 1) (y 0)
    · have hn := ih (e + 1) (by omega) ((hcone _).mp haccept)
      simpa only [scanNative, if_pos haccept, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
    · have hK : K ≤ e + 1 := Nat.le_of_not_gt ((hcone _).not.mp haccept)
      simp only [scanNative, if_neg haccept, List.head?_cons, Option.map_some, nativeOutputSegment]
      congr 1
      omega

/-- This definition observes the actual native output; it does not define the duration from a repair span. -/
def nativeFirstRecording (t y : ℕ → ℝ) (E : ℝ) : ℕ :=
  sInf {n : ℕ | 1 < (nativeStream t y E (n + 1)).length}

/-- For an actual finite feasibility threshold, the first recording precedes rejection by one sample. -/
theorem nativeFirstRecording_eq_threshold (t y : ℕ → ℝ) (E : ℝ) {K : ℕ} (hK : 1 < K)
    (hcone : ∀ j, nativePrefixFeasible t y E 0 j (y 0) ↔ j < K) :
    nativeFirstRecording t y E = K - 1 := by
  have hlength (n : ℕ) : 1 < (nativeStream t y E (n + 1)).length ↔ K ≤ n + 1 := by
    have heq := scanNative_length_one_iff_threshold t y E K hcone n 1 (by omega) hK
    have hpos := List.length_pos_iff.mpr (scanNative_nonempty t y E n 0 1 (y 0) (by omega))
    simp only [nativeStream]
    omega
  apply IsLeast.csInf_eq
  refine ⟨?_, ?_⟩
  · exact (hlength _).mpr (by omega)
  · intro n hn
    have := (hlength n).mp hn
    omega

/-- The existing native stream's first output segment has the proved first-recording duration. -/
theorem nativeStream_head_finish_threshold (t y : ℕ → ℝ) (E : ℝ) {K : ℕ} (hK : 1 < K)
    (hcone : ∀ j, nativePrefixFeasible t y E 0 j (y 0) ↔ j < K)
    {last : ℕ} (hlast : K ≤ last) :
    ((nativeStream t y E last).head?.map NativeSegment.finish) = some (K - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show last ≠ 0 by omega)
  have h := scanNative_head_finish_threshold t y E K hcone n 1 (by omega) hK
  simpa only [nativeStream, Nat.add_comm, min_eq_right (show K - 1 ≤ n + 1 by omega)] using h

/-- Exact deterministic link from a finite original rejection to the actual native first recording. -/
theorem nativeFirstRecording_eq_firstRepairSpan_sub_one {Ω : Type*}
    (X : ℕ → Ω → ℝ) (E : ℝ) (hE : 0 ≤ E) (ω : Ω)
    (hfinite : firstRepairReject X (2 * E) ω ≠ ⊤) :
    nativeFirstRecording (fun n => (n : ℝ)) (fun n => cumulativeSamples X n ω) E =
      firstRepairSpan X (2 * E) ω - 1 := by
  have ht : StrictMono (fun n : ℕ => (n : ℝ)) := by
    intro a b hab
    change (a : ℝ) < b
    exact_mod_cast hab
  have hcone (j : ℕ) : nativePrefixFeasible (fun n => (n : ℝ))
      (fun n => cumulativeSamples X n ω) E 0 j (cumulativeSamples X 0 ω) ↔
        j < firstRepairSpan X (2 * E) ω :=
    (nativePrefix_trueAnchor_iff _ _ ht E 0 j).trans
      (prefixCone_iff_lt_firstRepairSpan X (2 * E) ω hfinite j)
  have hK : 1 < firstRepairSpan X (2 * E) ω := (hcone 1).mp
    (nativePrefix_singleton _ _ ht hE 0 _)
  exact nativeFirstRecording_eq_threshold _ _ E hK hcone

/-- With no rejection, the true native scan emits only its terminal EOF segment. -/
theorem scanNative_length_one_of_always_feasible (t y : ℕ → ℝ) (E : ℝ)
    (hcone : ∀ j, nativePrefixFeasible t y E 0 j (y 0))
    (fuel e : ℕ) (he : 0 < e) :
    (scanNative t y E fuel 0 e (y 0) he).length = 1 := by
  induction fuel generalizing e with
  | zero => simp [scanNative]
  | succ fuel ih =>
    simpa only [scanNative, if_pos (hcone _)] using ih (e + 1) (by omega)

/-- The null/no-rejection convention agrees on both sides: no native recording has duration zero. -/
theorem nativeFirstRecording_eq_firstRepairSpan_sub_one_all {Ω : Type*}
    (X : ℕ → Ω → ℝ) (E : ℝ) (hE : 0 ≤ E) (ω : Ω) :
    nativeFirstRecording (fun n => (n : ℝ)) (fun n => cumulativeSamples X n ω) E =
      firstRepairSpan X (2 * E) ω - 1 := by
  by_cases hfinite : firstRepairReject X (2 * E) ω ≠ ⊤
  · exact nativeFirstRecording_eq_firstRepairSpan_sub_one X E hE ω hfinite
  have htop : firstRepairReject X (2 * E) ω = ⊤ := not_ne_iff.mp hfinite
  have hnever := (firstRepairReject_eq_top_iff X (2 * E) ω).mp htop
  have ht : StrictMono (fun n : ℕ => (n : ℝ)) := by
    intro a b hab
    change (a : ℝ) < b
    exact_mod_cast hab
  have hcone (j : ℕ) : nativePrefixFeasible (fun n => (n : ℝ))
      (fun n => cumulativeSamples X n ω) E 0 j (cumulativeSamples X 0 ω) := by
    apply (nativePrefix_trueAnchor_iff _ _ ht E 0 j).mpr
    cases j with
    | zero => exact prefixCone_self_nonempty _ _ _ _
    | succ n => exact not_not.mp (hnever n)
  have hlength (n : ℕ) : (nativeStream (fun j => (j : ℝ))
      (fun j => cumulativeSamples X j ω) E (n + 1)).length = 1 := by
    exact scanNative_length_one_of_always_feasible _ _ E hcone n 1 (by omega)
  have hempty : {n : ℕ | 1 < (nativeStream (fun j => (j : ℝ))
      (fun j => cumulativeSamples X j ω) E (n + 1)).length} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, hlength, lt_self_iff_false, Set.mem_empty_iff_false]
  simp only [nativeFirstRecording, hempty, Nat.sInf_empty, firstRepairSpan, htop,
    WithTop.untopD_top, Nat.zero_add, Nat.sub_self]

/-- The actual first native recording for the unit-time cumulative input sequence. -/
def nativeFirstDuration {Ω : Type*} (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℕ :=
  nativeFirstRecording (fun n => (n : ℝ)) (fun n => cumulativeSamples X n ω) E

/-- The equality includes the no-rejection convention, so it holds for every input path. -/
theorem nativeFirstDuration_eq_span_sub_one {Ω : Type*}
    (X : ℕ → Ω → ℝ) (E : ℝ) (hE : 0 ≤ E) (ω : Ω) :
    nativeFirstDuration X E ω = firstRepairSpan X (2 * E) ω - 1 :=
  nativeFirstRecording_eq_firstRepairSpan_sub_one_all X E hE ω

/-- Once the first rejection has been observed, the true output head ends at the first duration. -/
theorem nativeStream_head_finish_firstDuration {Ω : Type*}
    (X : ℕ → Ω → ℝ) (E : ℝ) (hE : 0 ≤ E) (ω : Ω)
    (hfinite : firstRepairReject X (2 * E) ω ≠ ⊤)
    {last : ℕ} (hlast : firstRepairSpan X (2 * E) ω ≤ last) :
    ((nativeStream (fun n => (n : ℝ)) (fun n => cumulativeSamples X n ω) E last).head?.map
      NativeSegment.finish) = some (nativeFirstDuration X E ω) := by
  have ht : StrictMono (fun n : ℕ => (n : ℝ)) := by
    intro a b hab
    change (a : ℝ) < b
    exact_mod_cast hab
  have hcone (j : ℕ) : nativePrefixFeasible (fun n => (n : ℝ))
      (fun n => cumulativeSamples X n ω) E 0 j (cumulativeSamples X 0 ω) ↔
        j < firstRepairSpan X (2 * E) ω :=
    (nativePrefix_trueAnchor_iff _ _ ht E 0 j).trans
      (prefixCone_iff_lt_firstRepairSpan X (2 * E) ω hfinite j)
  have hK : 1 < firstRepairSpan X (2 * E) ω := (hcone 1).mp
    (nativePrefix_singleton _ _ ht hE 0 _)
  rw [nativeFirstDuration_eq_span_sub_one X E hE ω]
  exact nativeStream_head_finish_threshold _ _ E hK hcone hlast

end SwingRepair
