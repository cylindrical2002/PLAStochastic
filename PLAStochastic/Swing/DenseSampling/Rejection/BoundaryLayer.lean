import PLAStochastic.Swing.DenseSampling.Rejection.GuardMeasurability

/-! # All actual rejection states enter a uniformly small boundary layer -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The output just before an observed rejection is a feasible old segment,
and the rejected observation makes its entire old anchored cone empty. -/
theorem nativeRejectionAt_previous_spec (t y : ℕ → ℝ) (ht : StrictMono t)
    {ε : ℝ} (hε : 0 ≤ ε) {b : ℕ} (hb : nativeRejectionAt t y ε b) :
    let old := nativeStream t y ε b
    let seg := nativeSegmentAt old (old.length-1)
    seg.start < seg.finish ∧ seg.finish = b ∧ |seg.anchorValue-y seg.start| ≤ ε ∧
      feasibleSlope (Finset.Icc (seg.start+1) seg.finish) t y (t seg.start) seg.anchorValue ε seg.slope ∧
      ¬ nativePrefixFeasible t y ε seg.start (seg.finish+1) seg.anchorValue := by
  let old := nativeStream t y ε b
  let now := nativeStream t y ε (b+1)
  let k := old.length-1
  have hp : 0 < old.length := nativeStream_length_pos_of_pos t y ε hb.1
  have hk : k < old.length := by dsimp only [k]; omega
  have hdrop : now.dropLast = old := nativeRejectionAt_dropLast t y ε hb
  have hkn : k+1 < now.length := by
    have hl := congrArg List.length hdrop
    simp only [List.length_dropLast] at hl
    dsimp only [k]
    omega
  have heq : nativeSegmentAt now k = nativeSegmentAt old k := by
    have hd : k < now.dropLast.length := by rw [hdrop]; exact hk
    calc
      _ = nativeSegmentAt now.dropLast k := by
        simp only [nativeSegmentAt_eq_getElem (by omega : k < now.length),
          nativeSegmentAt_eq_getElem hd, List.getElem_dropLast]
      _ = _ := congrArg (fun l => nativeSegmentAt l k) hdrop
  have hco : NativeChain t y ε 0 (y 0) b old := nativeStream_spec t y ht hε b
  have hcn : NativeChain t y ε 0 (y 0) (b+1) now := nativeStream_spec t y ht hε (b+1)
  have hv := hco.getElem_valid hk
  have he := hco.getElem_last_finish hk (by dsimp only [k]; omega)
  have ha := hco.getElem_anchor_error (by simpa only [sub_self, abs_zero] using hε) hk
  have hr := hcn.getElem_reject hkn
  rw [← nativeSegmentAt_eq_getElem (by omega : k < now.length), heq,
    nativeSegmentAt_eq_getElem hk] at hr
  change (nativeSegmentAt old k).start < (nativeSegmentAt old k).finish ∧
    (nativeSegmentAt old k).finish = b ∧ _
  rw [nativeSegmentAt_eq_getElem hk]
  exact ⟨hv.positive, he, ha, hv.feasible, hr⟩

/-- Uniform boundary control and path continuity apply simultaneously to every
observed rejection in a compact horizon. -/
theorem exists_uniform_nativeRejectionState (f : C(ℝ, ℝ)) {T ε γ : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hγ : 0 < γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ b : ℕ, (b : ℝ)*h ≤ T →
      nativeRejectionAt (fun j => (j : ℝ)*h) (fun j => f ((j : ℝ)*h)) ε b →
      nativeRejectionState (fun j => (j : ℝ)*h) (fun j => f ((j : ℝ)*h)) ε b < 2*γ := by
  obtain ⟨δ₁, hδ₁, hc⟩ := exists_uniform_native_boundary_control f hT hε hγ
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous (f := f) f.continuous.continuousOn
    (s := Icc (0 : ℝ) (T+1))
  obtain ⟨δ₂, hδ₂, hm⟩ := Metric.uniformContinuousOn_iff.mp hu γ hγ
  refine ⟨min δ₁ (min 1 δ₂), lt_min hδ₁ (lt_min zero_lt_one hδ₂), ?_⟩
  intro h hh hhδ b hbT hb
  have hh₁ : h < δ₁ := hhδ.trans_le (min_le_left _ _)
  have hh1 : h < 1 := hhδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hh₂ : h < δ₂ := hhδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let t : ℕ → ℝ := fun j => (j : ℝ)*h
  let y : ℕ → ℝ := fun j => f ((j : ℝ)*h)
  let seg := nativeSegmentAt (nativeStream t y ε b) ((nativeStream t y ε b).length-1)
  have hs := nativeRejectionAt_previous_spec t y (strictMono_mesh_times hh) hε.le hb
  change seg.start < seg.finish ∧ seg.finish = b ∧ |seg.anchorValue-y seg.start| ≤ ε ∧
      feasibleSlope (Finset.Icc (seg.start+1) seg.finish) t y (t seg.start) seg.anchorValue ε seg.slope ∧
      ¬ nativePrefixFeasible t y ε seg.start (seg.finish+1) seg.anchorValue at hs
  have hbd := hc h hh hh₁ seg.start seg.finish hs.1 (by rw [hs.2.1]; exact hbT)
    seg.anchorValue seg.slope hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  have he : (b : ℝ)*h ∈ Icc (0 : ℝ) (T+1) := ⟨by positivity, by linarith⟩
  have hn : ((b+1 : ℕ) : ℝ)*h ∈ Icc (0 : ℝ) (T+1) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact ⟨by positivity, by nlinarith⟩
  have hd : dist (((b+1 : ℕ) : ℝ)*h) ((b : ℝ)*h) < δ₂ := by
    rw [Real.dist_eq, Nat.cast_add, Nat.cast_one]
    have : ((b : ℝ)+1)*h-(b : ℝ)*h = h := by ring
    rw [this, abs_of_pos hh]
    exact hh₂
  have hz : |y (b+1)-y b| < γ := by
    simpa only [Real.dist_eq, y] using hm _ hn _ he hd
  have habs : |nativePolarity (nativeCarryAnchor t y ε b-y b)*(y (b+1)-y b)| = |y (b+1)-y b| := by
    rw [abs_mul, nativePolarity_abs, one_mul]
  have hsign := le_abs_self (nativePolarity (nativeCarryAnchor t y ε b-y b)*(y (b+1)-y b))
  rw [habs] at hsign
  have hdef : ε-|nativeCarryAnchor t y ε b-y b| < γ := by
    simpa only [nativeCarryAnchor, nativeSegmentEndpoint, seg, t, y, hs.2.1] using hbd.2.2
  change ε-|nativeCarryAnchor t y ε b-y b|+
    nativePolarity (nativeCarryAnchor t y ε b-y b)*(y (b+1)-y b) < 2*γ
  linarith

end SwingRepair
