import PLAStochastic.Swing.DenseSampling.CarriedPrefix.DurationCharge
import PLAStochastic.Swing.DenseSampling.Rejection.GridTimes

/-! # The sum of all actual carried continuations has a deterministic time budget -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- At each observed rejection, charge the true capped feasible continuation
from the inherited fitted anchor. -/
def nativeRejectionDuration (y : ℕ → ℝ) (ε : ℝ) (h H : ℝ≥0) (b : ℕ) : ℝ :=
  let q := nativeCarryAnchor (fun j => (j : ℝ)*(h : ℝ)) y ε b
  nativeCarriedTruncatedDuration (nativeCarriedFuture y q b)
    (nativeCarriedState y ε q b) ε h H

/-- Rejections at distinct grid times enter distinct actual output segments. -/
theorem nativeRejectionAt_index_injective (t y : ℕ → ℝ) (ht : StrictMono t)
    {ε : ℝ} (hε : 0 ≤ ε) {n last : ℕ} (hn : n+1 ≤ last) :
    Set.InjOn (fun b => (nativeStream t y ε b).length)
      {b | b ≤ n ∧ nativeRejectionAt t y ε b} := by
  intro b hb c hc he
  change b ≤ n ∧ nativeRejectionAt t y ε b at hb
  change c ≤ n ∧ nativeRejectionAt t y ε c at hc
  have hb' := nativeRejectionAt_next t y ht hε hb.2 (by omega : b+1 ≤ last)
  have hc' := nativeRejectionAt_next t y ht hε hc.2 (by omega : c+1 ≤ last)
  exact hb'.2.2.1.symm.trans ((congrArg (fun k =>
    (nativeSegmentAt (nativeStream t y ε last) k).start) he).trans hc'.2.2.1)

/-- Sum over deterministic possible rejection observations. Each local term is
charged once to a different true segment of the extended stream, including EOF. -/
theorem sum_nativeRejectionDuration_le_horizon (y : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    {h H : ℝ≥0} (hh : 0 < h) {n last : ℕ} (hn : n+1 ≤ last) {T : ℝ}
    (hnT : (n : ℝ)*(h : ℝ) ≤ T) (horizon : T+(H : ℝ) ≤ (last : ℝ)*(h : ℝ)) :
    (∑ b ∈ Finset.range (n+1),
      if nativeRejectionAt (fun j => (j : ℝ)*(h : ℝ)) y ε b
      then nativeRejectionDuration y ε h H b else 0) ≤ (last : ℝ)*(h : ℝ) := by
  let t : ℕ → ℝ := fun j => (j : ℝ)*(h : ℝ)
  let segs := nativeStream t y ε last
  let S := (Finset.range (n+1)).filter (nativeRejectionAt t y ε)
  let k : ℕ → ℕ := fun b => (nativeStream t y ε b).length
  have ht : StrictMono t := strictMono_mesh_times (by exact_mod_cast hh)
  have hc : NativeChain t y ε 0 (y 0) last segs := nativeStream_spec t y ht hε last
  have hmem : ∀ b ∈ S, b ≤ n ∧ nativeRejectionAt t y ε b := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    exact ⟨by have := Finset.mem_range.mp hb'.1; omega, hb'.2⟩
  have hnext : ∀ b ∈ S, k b < segs.length ∧
      (nativeSegmentAt segs (k b)).start = b ∧
      (nativeSegmentAt segs (k b)).anchorValue = nativeCarryAnchor t y ε b := by
    intro b hb
    have hm := hmem b hb
    exact (nativeRejectionAt_next t y ht hε hm.2 (by omega : b+1 ≤ last)).2
  have hcharge : ∀ b ∈ S, nativeRejectionDuration y ε h H b ≤ nativeDurationAt t segs (k b) := by
    intro b hb
    have hx := hnext b hb
    have hsT : ((nativeSegmentAt segs (k b)).start : ℝ)*(h : ℝ) ≤ T := by
      rw [hx.2.1]
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast (hmem b hb).1) h.coe_nonneg).trans hnT
    have hbound := hc.carried_duration_le_elapsed hx.1
      (by simpa only [nativeSegmentAt_eq_getElem hx.1] using hsT) horizon
    simpa only [nativeRejectionDuration, ← nativeSegmentAt_eq_getElem hx.1,
      hx.2.1, hx.2.2, nativeDurationAt, t] using hbound
  have hinj : Set.InjOn k (↑S : Set ℕ) := by
    intro b hb c hcc he
    exact nativeRejectionAt_index_injective t y ht hε hn (hmem b hb) (hmem c hcc) he
  have hsub : S.image k ⊆ Finset.range segs.length := by
    intro i hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (hnext b hb).1
  calc
    _ = ∑ b ∈ S, nativeRejectionDuration y ε h H b := by
      symm
      exact Finset.sum_filter _ _
    _ ≤ ∑ b ∈ S, nativeDurationAt t segs (k b) := Finset.sum_le_sum hcharge
    _ = ∑ i ∈ S.image k, nativeDurationAt t segs i := (Finset.sum_image hinj).symm
    _ ≤ ∑ i ∈ Finset.range segs.length, nativeDurationAt t segs i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hc.durationAt_nonneg ht.monotone i)
    _ = (last : ℝ)*(h : ℝ) := by rw [sum_nativeDurationAt, hc.sum_elapsedTime]; simp only [t, Nat.cast_zero, zero_mul, sub_zero]

end SwingRepair
