import PLAStochastic.Swing.Ladder.ZeroDrift.AgeResidual

/-!
# Crossing functionals of a real path

The level-crossing functionals `levelCrossing`, `levelOvershoot`, `levelUndershoot` of a path
(first strict crossing, overshoot and undershoot, `0` when there is no crossing) describe both
the local crossing quantities of the entrance law at the cut width and the zero-drift pair
`(U_D, O_D)` of (E14). This file adds drifted walks:

* `driftPath x b j = ∑_{i<j} x i - b j` is the walk with increments `x` and drift `-b`;
  `crossingPair D b x` is its (undershoot, overshoot) pair at level `D`;
* window locality: paths that agree up to `q` have the same crossing functionals as soon as
  one of them crosses by time `q`;
* joint measurability in the level, the drift and the increments.
-/

namespace SwingRepair

noncomputable section

open MeasureTheory Set

/-! ## Definitions -/

/-- The walk `j ↦ ∑_{i<j} x i - b j` with increments `x` and drift `-b`. -/
def driftPath (x : ℕ → ℝ) (b : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, x i - b * j

/-- The (undershoot, overshoot) pair of the walk with increments `x` and drift `-b` at `D`. -/
def crossingPair (D b : ℝ) (x : ℕ → ℝ) : ℝ × ℝ :=
  (levelUndershoot (driftPath x b) D, levelOvershoot (driftPath x b) D)

variable {Ω : Type*}

theorem zeroDriftCrossing_eq (X : ℕ → Ω → ℝ) (D : ℝ) (ω : Ω) :
    zeroDriftCrossing X D ω = levelCrossing (fun j => cumulativeSamples X j ω) D := rfl

theorem zeroDriftOvershoot_eq (X : ℕ → Ω → ℝ) (D : ℝ) (ω : Ω) :
    zeroDriftOvershoot X D ω = levelOvershoot (fun j => cumulativeSamples X j ω) D := rfl

theorem zeroDriftUndershoot_eq (X : ℕ → Ω → ℝ) (D : ℝ) (ω : Ω) :
    zeroDriftUndershoot X D ω = levelUndershoot (fun j => cumulativeSamples X j ω) D := rfl

theorem driftPath_zero_cumulative (X : ℕ → Ω → ℝ) (ω : Ω) :
    driftPath (fun i => X i ω) 0 = fun j => cumulativeSamples X j ω := by
  funext j
  simp [driftPath, cumulativeSamples]

/-- The zero-drift pair is the crossing pair of the increments with drift `0`. -/
theorem crossingPair_zero_eq (X : ℕ → Ω → ℝ) (D : ℝ) (ω : Ω) :
    crossingPair D 0 (fun i => X i ω) = (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω) := by
  simp only [crossingPair, driftPath_zero_cumulative, zeroDriftUndershoot_eq,
    zeroDriftOvershoot_eq]

/-- A drift is absorbed into the increments. -/
theorem driftPath_sub (x : ℕ → ℝ) (b : ℝ) :
    driftPath x b = driftPath (fun i => x i - b) 0 := by
  funext j
  simp [driftPath, Finset.sum_sub_distrib, mul_comm]

theorem crossingPair_sub (D b : ℝ) (x : ℕ → ℝ) :
    crossingPair D b x = crossingPair D 0 (fun i => x i - b) := by
  simp only [crossingPair, ← driftPath_sub]

/-! ## Characterizations of the crossing time -/

theorem lt_levelCrossing_iff (w : ℕ → ℝ) (D : ℝ) (q : ℕ) :
    (q : ℕ∞) < levelCrossing w D ↔ ∀ j, 1 ≤ j → j ≤ q → w j ≤ D := by
  classical
  unfold levelCrossing
  split_ifs with h
  · rw [Nat.cast_lt, Nat.lt_find_iff]
    constructor
    · intro hm j hj hjq
      exact le_of_not_gt fun hlt => hm j hjq ⟨hj, hlt⟩
    · intro hall j hjq ⟨hj, hlt⟩
      exact (hall j hj hjq).not_gt hlt
  · simp only [ENat.natCast_lt_top, true_iff]
    intro j hj _
    exact le_of_not_gt fun hlt => h ⟨j, hj, hlt⟩

theorem levelCrossing_le_iff (w : ℕ → ℝ) (D : ℝ) (q : ℕ) :
    levelCrossing w D ≤ (q : ℕ∞) ↔ ∃ j, 1 ≤ j ∧ j ≤ q ∧ D < w j := by
  rw [← not_lt, lt_levelCrossing_iff]
  push Not
  exact Iff.rfl

/-! ## Window locality -/

/-- Paths agreeing up to `q` cross by time `q` together. -/
theorem levelCrossing_le_congr {w w' : ℕ → ℝ} {q : ℕ} (hww : ∀ j ≤ q, w j = w' j) (D : ℝ) :
    levelCrossing w D ≤ (q : ℕ∞) ↔ levelCrossing w' D ≤ (q : ℕ∞) := by
  rw [levelCrossing_le_iff, levelCrossing_le_iff]
  constructor
  · rintro ⟨j, hj, hjq, hlt⟩
    exact ⟨j, hj, hjq, (hww j hjq) ▸ hlt⟩
  · rintro ⟨j, hj, hjq, hlt⟩
    exact ⟨j, hj, hjq, (hww j hjq).symm ▸ hlt⟩

/-- If one of two paths agreeing up to `q` crosses by `q`, the crossing times agree. -/
theorem levelCrossing_eq_of_window {w w' : ℕ → ℝ} {q : ℕ} (hww : ∀ j ≤ q, w j = w' j)
    {D : ℝ} {T : ℕ} (hT : levelCrossing w D = (T : ℕ∞)) (hTq : T ≤ q) :
    levelCrossing w' D = (T : ℕ∞) := by
  rw [levelCrossing_eq_coe_iff] at hT ⊢
  obtain ⟨h1, h2, h3⟩ := hT
  refine ⟨h1, (hww T hTq) ▸ h2, fun j hj hjT => ?_⟩
  rw [← hww j (by omega)]
  exact h3 j hj hjT

/-- Window locality of the overshoot and undershoot. -/
theorem crossing_functionals_eq_of_window {w w' : ℕ → ℝ} {q : ℕ}
    (hww : ∀ j ≤ q, w j = w' j) {D : ℝ} (hq : levelCrossing w D ≤ (q : ℕ∞)) :
    levelOvershoot w' D = levelOvershoot w D ∧
      levelUndershoot w' D = levelUndershoot w D := by
  have hne : levelCrossing w D ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top q) hq
  obtain ⟨T, hT⟩ := ENat.ne_top_iff_exists.mp hne
  have hT' := hT.symm
  have hTq : T ≤ q := by exact_mod_cast hT ▸ hq
  have hT'' := levelCrossing_eq_of_window hww hT' hTq
  have hT1 : 0 < T := ((levelCrossing_eq_coe_iff w D T).mp hT').1
  refine ⟨?_, ?_⟩
  · rw [levelOvershoot_of_eq hT', levelOvershoot_of_eq hT'', hww T hTq]
  · rw [levelUndershoot_of_eq hT' hT1, levelUndershoot_of_eq hT'' hT1]
    congr 1
    exact Finset.sup'_congr _ rfl fun j hj => (hww j (by have := Finset.mem_range.mp hj; omega)).symm

theorem driftPath_eq_of_window {x x' : ℕ → ℝ} {q : ℕ} (hxx : ∀ i < q, x i = x' i) (b : ℝ) :
    ∀ j ≤ q, driftPath x b j = driftPath x' b j := by
  intro j hj
  unfold driftPath
  congr 1
  exact Finset.sum_congr rfl fun i hi => hxx i (by have := Finset.mem_range.mp hi; omega)

/-! ## Measurability -/

variable {P : Type*} [MeasurableSpace P]

theorem measurable_levelCrossing {w : P → ℕ → ℝ} {D : P → ℝ}
    (hw : ∀ j, Measurable fun p => w p j) (hD : Measurable D) :
    Measurable fun p => levelCrossing (w p) (D p) := by
  apply measurable_to_countable'
  intro t
  induction t using ENat.recTopCoe with
  | top =>
    have heq : (fun p => levelCrossing (w p) (D p)) ⁻¹' {⊤} =
        {p | ∀ j : ℕ, 1 ≤ j → w p j ≤ D p} := by
      ext p
      simp only [mem_preimage, mem_singleton_iff, levelCrossing_eq_top_iff, mem_ofPred_eq]
    rw [heq]
    refine measurableSet_setOfPred.mpr (Measurable.forall fun j => ?_)
    exact measurable_const.imp (measurableSet_setOfPred.mp (measurableSet_le (hw j) hD))
  | coe T =>
    have heq : (fun p => levelCrossing (w p) (D p)) ⁻¹' {(T : ℕ∞)} =
        {p | 1 ≤ T ∧ D p < w p T ∧ ∀ j : ℕ, 1 ≤ j → j < T → w p j ≤ D p} := by
      ext p
      simp only [mem_preimage, mem_singleton_iff, levelCrossing_eq_coe_iff, mem_ofPred_eq]
    rw [heq]
    refine measurableSet_setOfPred.mpr (measurable_const.and
      ((measurableSet_setOfPred.mp (measurableSet_lt hD (hw T))).and
        (Measurable.forall fun j => measurable_const.imp (measurable_const.imp ?_))))
    exact measurableSet_setOfPred.mp (measurableSet_le (hw j) hD)

theorem measurable_levelOvershoot {w : P → ℕ → ℝ} {D : P → ℝ}
    (hw : ∀ j, Measurable fun p => w p j) (hD : Measurable D) :
    Measurable fun p => levelOvershoot (w p) (D p) := by
  let G : P × ℕ∞ → ℝ := fun r => match r.2 with
    | ⊤ => 0
    | (T : ℕ) => w r.1 T - D r.1
  have hG : Measurable G := by
    apply measurable_from_prod_countable_left
    intro t
    induction t using ENat.recTopCoe with
    | top => exact measurable_const
    | coe T => exact (hw T).sub hD
  have h := hG.comp (measurable_id.prodMk (measurable_levelCrossing hw hD))
  convert h using 1
  funext p
  rfl

theorem measurable_levelUndershoot {w : P → ℕ → ℝ} {D : P → ℝ}
    (hw : ∀ j, Measurable fun p => w p j) (hD : Measurable D) :
    Measurable fun p => levelUndershoot (w p) (D p) := by
  let G : P × ℕ∞ → ℝ := fun r => match r.2 with
    | ⊤ => 0
    | (T : ℕ) =>
      if hT : 0 < T then
        D r.1 - (Finset.range T).sup' (Finset.nonempty_range_iff.mpr hT.ne') (w r.1)
      else 0
  have hG : Measurable G := by
    apply measurable_from_prod_countable_left
    intro t
    induction t using ENat.recTopCoe with
    | top => exact measurable_const
    | coe T =>
      by_cases hT : 0 < T
      · simp only [G, dif_pos hT]
        refine hD.sub ?_
        have hs := Finset.measurable_sup' (Finset.nonempty_range_iff.mpr hT.ne')
          (f := fun j p => w p j) (fun j _ => hw j)
        convert hs using 1
        funext p
        simp only [Finset.sup'_apply]
      · simp only [G, dif_neg hT]
        exact measurable_const
  have h := hG.comp (measurable_id.prodMk (measurable_levelCrossing hw hD))
  convert h using 1
  funext p
  rfl

theorem measurable_driftPath_apply {x : P → ℕ → ℝ} {b : P → ℝ}
    (hx : ∀ i, Measurable fun p => x p i) (hb : Measurable b) (j : ℕ) :
    Measurable fun p => driftPath (x p) (b p) j :=
  (Finset.measurable_sum _ fun i _ => hx i).sub (hb.mul_const _)

/-- Joint measurability of the crossing pair in the level, the drift and the increments. -/
theorem measurable_crossingPair :
    Measurable fun r : (ℝ × ℝ) × (ℕ → ℝ) => crossingPair r.1.1 r.1.2 r.2 := by
  have hx : ∀ i, Measurable fun r : (ℝ × ℝ) × (ℕ → ℝ) => r.2 i :=
    fun i => (measurable_pi_apply i).comp measurable_snd
  have hw := measurable_driftPath_apply hx (measurable_snd.comp measurable_fst)
  exact (measurable_levelUndershoot hw (measurable_fst.comp measurable_fst)).prodMk
    (measurable_levelOvershoot hw (measurable_fst.comp measurable_fst))

/-- Joint measurability of the crossing time in the level, the drift and the increments. -/
theorem measurable_levelCrossing_driftPath :
    Measurable fun r : (ℝ × ℝ) × (ℕ → ℝ) => levelCrossing (driftPath r.2 r.1.2) r.1.1 := by
  have hx : ∀ i, Measurable fun r : (ℝ × ℝ) × (ℕ → ℝ) => r.2 i :=
    fun i => (measurable_pi_apply i).comp measurable_snd
  exact measurable_levelCrossing (measurable_driftPath_apply hx (measurable_snd.comp measurable_fst))
    (measurable_fst.comp measurable_fst)

end

end SwingRepair
