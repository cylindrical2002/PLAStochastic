import PLAStochastic.Swing.DenseSampling.Rejection.GridTimes
import PLAStochastic.Brownian.Markov.IndependentState

/-! # Rejection guards and inherited anchors depend measurably on the observed past -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem measurable_nativeCarryAnchor (t : ℕ → ℝ) (ht : StrictMono t) (ε : ℝ) (b : ℕ) :
    Measurable (fun y : ℕ → ℝ => nativeCarryAnchor t y ε b) := by
  let F (c : ℕ × (ℕ → ℕ × ℕ × ℝ × ℝ)) : ℝ :=
    (c.2 (c.1-1)).2.2.1+(c.2 (c.1-1)).2.2.2*(t (c.2 (c.1-1)).2.1-t (c.2 (c.1-1)).1)
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    intro n
    have he : Measurable (fun c : ℕ → ℕ × ℕ × ℝ × ℝ => c (n-1)) := measurable_pi_apply _
    have htm : Measurable t := measurable_of_countable t
    exact he.snd.snd.fst.add (he.snd.snd.snd.mul ((htm.comp he.snd.fst).sub (htm.comp he.fst)))
  have hc := measurable_nativeStream_output t ht (fun j (y : ℕ → ℝ) => y j) ε b
    (fun j _ => measurable_pi_apply j)
  simpa only [Function.comp_def, F, nativeOutputCode, nativeSegmentCode,
    nativeCarryAnchor, nativeSegmentEndpoint, nativeSegmentAt, List.getD_eq_getElem?_getD] using hF.comp hc

theorem measurableSet_nativeRejectionAt (t : ℕ → ℝ) (ht : StrictMono t) (ε : ℝ) (b : ℕ) :
    MeasurableSet {y : ℕ → ℝ | nativeRejectionAt t y ε b} := by
  have hc (n : ℕ) := (measurable_nativeStream_output t ht (fun j (y : ℕ → ℝ) => y j) ε n
    (fun j _ => measurable_pi_apply j)).fst
  change MeasurableSet ({y : ℕ → ℝ | 0 < b} ∩
    {y | (nativeOutputCode (nativeStream t y ε b)).1 <
      (nativeOutputCode (nativeStream t y ε (b+1))).1})
  exact (MeasurableSet.const _).inter (measurableSet_lt (hc b) (hc (b+1)))

theorem nativeCarryAnchor_prefix_congr (t : ℕ → ℝ) (ε : ℝ) {y y' : ℕ → ℝ} {b : ℕ}
    (hy : ∀ j ≤ b, y j = y' j) : nativeCarryAnchor t y ε b = nativeCarryAnchor t y' ε b := by
  unfold nativeCarryAnchor
  rw [nativeStream_prefix_congr ε b (fun _ _ => rfl) hy]

theorem nativeRejectionAt_prefix_congr (t : ℕ → ℝ) (ε : ℝ) {y y' : ℕ → ℝ} {b : ℕ}
    (hy : ∀ j ≤ b+1, y j = y' j) : nativeRejectionAt t y ε b ↔ nativeRejectionAt t y' ε b := by
  unfold nativeRejectionAt
  rw [nativeStream_prefix_congr ε b (fun _ _ => rfl) (fun j hj => hy j (by omega)),
    nativeStream_prefix_congr ε (b+1) (fun _ _ => rfl) hy]

/-- The whole finite Brownian history is a measurable random variable. -/
theorem aemeasurable_brownianGridPast {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) (h : ℝ≥0) (r : ℕ) :
    AEMeasurable (brownianGridPast B h r) μ := by
  apply aemeasurable_pi_lambda
  intro j
  by_cases hj : j ≤ r
  · simpa only [brownianGridPast, if_pos hj] using hB.aemeasurable ((j : ℝ≥0)*h)
  · simpa only [brownianGridPast, if_neg hj] using (aemeasurable_const (b := (0 : ℝ)))

/-- The signed boundary coordinate computed from the actual previous fitted output. -/
def nativeRejectionState (t y : ℕ → ℝ) (ε : ℝ) (b : ℕ) : ℝ :=
  nativeCarriedState y ε (nativeCarryAnchor t y ε b) b

def nativeRejectionSign (t y : ℕ → ℝ) (ε : ℝ) (b : ℕ) : ℝ :=
  nativeCarryAnchor t y ε b-y b

theorem measurable_nativeRejectionState (t : ℕ → ℝ) (ht : StrictMono t) (ε : ℝ) (b : ℕ) :
    Measurable (fun y : ℕ → ℝ => nativeRejectionState t y ε b) :=
  measurable_nativeCarriedState (fun j (y : ℕ → ℝ) => y j)
    (measurable_nativeCarryAnchor t ht ε b) (fun j => measurable_pi_apply j) ε b

theorem measurable_nativeRejectionSign (t : ℕ → ℝ) (ht : StrictMono t) (ε : ℝ) (b : ℕ) :
    Measurable (fun y : ℕ → ℝ => nativeRejectionSign t y ε b) :=
  (measurable_nativeCarryAnchor t ht ε b).sub (measurable_pi_apply b)

theorem nativeRejectionState_prefix_congr (t : ℕ → ℝ) (ε : ℝ) {y y' : ℕ → ℝ} {b : ℕ}
    (hy : ∀ j ≤ b+1, y j = y' j) : nativeRejectionState t y ε b = nativeRejectionState t y' ε b := by
  unfold nativeRejectionState nativeCarriedState
  rw [nativeCarryAnchor_prefix_congr t ε (fun j hj => hy j (by omega)),
    hy b (by omega), hy (b+1) le_rfl]

theorem nativeRejectionSign_prefix_congr (t : ℕ → ℝ) (ε : ℝ) {y y' : ℕ → ℝ} {b : ℕ}
    (hy : ∀ j ≤ b, y j = y' j) : nativeRejectionSign t y ε b = nativeRejectionSign t y' ε b := by
  unfold nativeRejectionSign
  rw [nativeCarryAnchor_prefix_congr t ε hy, hy b le_rfl]

end SwingRepair
