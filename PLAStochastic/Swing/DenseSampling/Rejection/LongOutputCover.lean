import PLAStochastic.Swing.DenseSampling.Rejection.StreamProbabilityBudget
import PLAStochastic.Swing.DenseSampling.Rejection.BoundaryLayer

/-! # Every long post-first output is covered by an actual rejection event -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem NativeChain.getElem_start_lt {t y : ℕ → ℝ} {ε q : ℝ} {s last : ℕ}
    {segs : List NativeSegment} (hc : NativeChain t y ε s q last segs)
    {k l : ℕ} (hkl : k < l) (hl : l < segs.length) : segs[k].start < segs[l].start := by
  have hk : k < segs.length := hkl.trans hl
  have hpos := (hc.getElem_bounds hk).2.2
  have hprev := (hc.getElem_succ (k := l-1) (by omega : l-1+1 < segs.length)).1
  have heq : segs[l].start = segs[l-1].finish := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ l)] using hprev
  rw [heq]
  by_cases he : k = l-1
  · subst k
    exact hpos
  · exact hpos.trans (hc.getElem_finish_lt (by omega) (by omega : l-1 < segs.length))

/-- The carry anchor obtained from the observed past is the actual anchor of
any later output segment starting at this recording index. -/
theorem nativeStream_postFirst_carryAnchor (t y : ℕ → ℝ) (ht : StrictMono t)
    {ε : ℝ} (hε : 0 ≤ ε) {last k : ℕ} (hk : 1 ≤ k)
    (hkN : k < (nativeStream t y ε last).length) :
    nativeCarryAnchor t y ε (nativeSegmentAt (nativeStream t y ε last) k).start =
      (nativeSegmentAt (nativeStream t y ε last) k).anchorValue := by
  let segs := nativeStream t y ε last
  let b := (nativeSegmentAt segs k).start
  have hc : NativeChain t y ε 0 (y 0) last segs := nativeStream_spec t y ht hε last
  have hb := nativeStream_postFirst_rejection t y ht hε hk hkN
  have hbN : b+1 ≤ last := by
    have hh := hc.getElem_bounds hkN
    dsimp only [b]
    rw [nativeSegmentAt_eq_getElem hkN]
    exact Nat.succ_le_of_lt (hh.2.2.trans_le hh.2.1)
  have hn := nativeRejectionAt_next t y ht hε hb hbN
  let l := (nativeStream t y ε b).length
  have hl : l < segs.length := hn.2.1
  have heq : (nativeSegmentAt segs l).start = (nativeSegmentAt segs k).start := hn.2.2.1
  have hlk : l = k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hs := hc.getElem_start_lt hlt hkN
      rw [← nativeSegmentAt_eq_getElem hl, ← nativeSegmentAt_eq_getElem hkN, heq] at hs
      exact lt_irrefl _ hs
    · have hs := hc.getElem_start_lt hgt hl
      rw [← nativeSegmentAt_eq_getElem hl, ← nativeSegmentAt_eq_getElem hkN, heq] at hs
      exact lt_irrefl _ hs
  have ha := hn.2.2.2
  change (nativeSegmentAt segs l).anchorValue = nativeCarryAnchor t y ε b at ha
  rw [hlk] at ha
  exact ha.symm

/-- A long feasible line on a bounded-height path has a uniformly bounded
slope. Only feasibility and endpoint errors are needed. -/
theorem native_feasible_long_slope_bound (y : ℕ → ℝ) {h ε q m a K : ℝ}
    (hh : 0 < h) (ha : 0 < a) {s e : ℕ} (hse : s < e)
    (hq : |q-y s| ≤ ε) (hs : |y s| ≤ K) (he : |y e| ≤ K)
    (hfit : feasibleSlope (Finset.Icc (s+1) e) (fun j => (j : ℝ)*h) y ((s : ℝ)*h) q ε m)
    (hlong : a ≤ ((e : ℝ)-(s : ℝ))*h) : |m| ≤ (2*K+2*ε)/a := by
  have hd : 0 < ((e-s : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hse
  have hb := (le_div_iff₀ hd).mp (native_slope_step_bound y hh hse hq hfit)
  have hosc : |y e-y s| ≤ 2*K := (abs_sub _ _).trans (by linarith)
  rw [Nat.cast_sub hse.le] at hb
  have hm := mul_le_mul_of_nonneg_left hlong (abs_nonneg m)
  apply (le_div_iff₀ ha).mpr
  nlinarith

/-- Any bounded chosen feasible line supplies the reflected carried event. -/
theorem nativeBoundedCarriedFit_of_feasible (y : ℕ → ℝ) {ε q m h M : ℝ} {b e N : ℕ}
    (hm : |m| ≤ M) (hN : (b+1)+N ≤ e)
    (hf : feasibleSlope (Finset.Icc (b+1) e) (fun j => (j : ℝ)*h) y ((b : ℝ)*h) q ε m) :
    nativeBoundedCarriedFit (nativeCarriedFuture y q b) (nativeCarriedState y ε q b) ε M h N := by
  refine ⟨nativePolarity (q-y b)*m, ?_, ?_⟩
  · simpa only [abs_mul, nativePolarity_abs, one_mul] using hm
  · intro j hj
    have hc := (nativeCarriedState_constraint_iff y ε q m h b j).mpr
      (hf ((b+1)+j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    simpa only [mul_assoc] using hc

/-- The first accepted carried observation forces the necessary lower state
restriction; no independent assumption about the carry is introduced. -/
theorem nativeBoundedCarriedFit_state_lower (y : ℕ → ℝ) {ε q M h : ℝ}
    (hh : 0 ≤ h) {b N : ℕ}
    (hf : nativeBoundedCarriedFit (nativeCarriedFuture y q b) (nativeCarriedState y ε q b) ε M h N) :
    -M*h ≤ nativeCarriedState y ε q b := by
  obtain ⟨m, hm, hf⟩ := hf
  have hz := (hf 0 (Nat.zero_le _)).1
  have hd : nativeCarriedFuture y q b 0 = 0 := by simp only [nativeCarriedFuture, add_zero, sub_self, mul_zero]
  rw [hd, Nat.cast_zero, zero_add, mul_one, add_zero] at hz
  have hm' := mul_le_mul_of_nonneg_right (abs_le.mp hm).1 hh
  linarith

/-- A macroscopic true post-first maximum activates one of the actual observed
rejection costs, including a terminal segment clipped at the supplied horizon. -/
theorem nativePostFirstMaximum_long_le_rejection_sum (y : ℕ → ℝ)
    {h : ℝ≥0} (hh : 0 < h) {a K M γ : ℝ} (ha : 0 < a) {last N : ℕ}
    (hheight : ∀ j ≤ last, |y j| ≤ K) (hM : (2*K+2)/a ≤ M)
    (hN : ((N : ℝ)+1)*(h : ℝ) ≤ a)
    (hstate : ∀ b ≤ last, nativeRejectionAt (fun j => (j : ℝ)*(h : ℝ)) y 1 b →
      nativeRejectionState (fun j => (j : ℝ)*(h : ℝ)) y 1 b ≤ 2*γ)
    (hlong : a ≤ nativePostFirstMaximum (fun j => (j : ℝ)*(h : ℝ))
      (nativeStream (fun j => (j : ℝ)*(h : ℝ)) y 1 last)) :
    1 ≤ ∑ b ∈ Finset.range (last+1), nativeRejectionLongCost y M γ h N b := by
  let t : ℕ → ℝ := fun j => (j : ℝ)*(h : ℝ)
  let segs := nativeStream t y 1 last
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have ht : StrictMono t := strictMono_mesh_times hhR
  obtain ⟨k, hk, hkN, hlong⟩ := (le_nativePostFirstMaximum_iff ha).mp hlong
  have hc : NativeChain t y 1 0 (y 0) last segs := nativeStream_spec t y ht (by norm_num) last
  let seg := nativeSegmentAt segs k
  let b := seg.start
  have hbounds := hc.getElem_bounds hkN
  have hvalid := hc.getElem_valid hkN
  have hq := hc.getElem_anchor_error (by simp : |y 0-y 0| ≤ (1 : ℝ)) hkN
  rw [← nativeSegmentAt_eq_getElem hkN] at hbounds hvalid hq
  have hb : b ≤ last := hbounds.2.2.le.trans hbounds.2.1
  have hr : nativeRejectionAt t y 1 b := nativeStream_postFirst_rejection t y ht (by norm_num) hk hkN
  have hanchor : nativeCarryAnchor t y 1 b = seg.anchorValue :=
    nativeStream_postFirst_carryAnchor t y ht (by norm_num) hk hkN
  have hl : a ≤ ((seg.finish : ℝ)-(b : ℝ))*(h : ℝ) := by
    dsimp only [nativeDurationAt, nativeElapsedTime, t] at hlong
    dsimp only [seg, b]
    nlinarith [hlong]
  have hm : |seg.slope| ≤ M := by
    have hx := native_feasible_long_slope_bound y hhR ha hbounds.2.2 hq
      (hheight _ hb) (hheight _ hbounds.2.1) hvalid.feasible hl
    norm_num only [mul_one] at hx
    exact hx.trans hM
  have hindex : (b+1)+N ≤ seg.finish := by
    have hm := hN.trans hl
    have hx : (N : ℝ)+1 ≤ (seg.finish : ℝ)-(b : ℝ) :=
      (mul_le_mul_iff_of_pos_right hhR).mp hm
    have he : ((b+1+N : ℕ) : ℝ) ≤ (seg.finish : ℝ) := by
      push_cast
      linarith
    exact_mod_cast he
  have hf := nativeBoundedCarriedFit_of_feasible y hm hindex hvalid.feasible
  have hw := nativeBoundedCarriedFit_state_lower y h.coe_nonneg hf
  have hguard : nativeRejectionGuard t y M h γ b := by
    refine ⟨hr, ?_, hstate b hb hr⟩
    simpa only [nativeRejectionState, hanchor] using hw
  have hcost : nativeRejectionLongCost y M γ h N b = 1 := by
    dsimp only [nativeRejectionLongCost]
    rw [if_pos hguard]
    unfold nativeCarriedLongIndicator
    rw [if_pos]
    change nativeBoundedCarriedFit (nativeCarriedFuture y (nativeCarryAnchor t y 1 b) b)
      (nativeCarriedState y 1 (nativeCarryAnchor t y 1 b) b) 1 M h N
    rw [hanchor]
    exact hf
  have hs := Finset.single_le_sum (f := fun b => nativeRejectionLongCost y M γ h N b)
    (fun b _ => (nativeRejectionLongCost_bounds y M γ h N b).1)
    (Finset.mem_range.mpr (by omega : b < last+1))
  rwa [hcost] at hs

end SwingRepair
