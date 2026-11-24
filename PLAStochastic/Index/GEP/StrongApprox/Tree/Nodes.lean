import PLAStochastic.Index.GEP.StrongApprox.Tree.Leaves

/-! # Node laws and exact split identities inside the shared dyadic construction -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Function
open scoped ENNReal

attribute [local fun_prop] SADensity.measurable_splitQuantile

/-- A node's total together with the uniform innovation used at that node.
At leaves the unused innovation is set to zero. -/
def saTreeNodeWithUniform {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j)) :
    (J d : ℕ) → ℝ → SATreeNoise J → SATreeIndex d → ℝ × ℝ
  | 0, _, a, _, _ => (a, 0)
  | _J + 1, 0, a, z, _ => (a, z.1)
  | J + 1, d + 1, a, z, Sum.inl i =>
    saTreeNodeWithUniform hp J d (saSplitQuantile (hp J) a z.1) z.2.1 i
  | J + 1, d + 1, a, z, Sum.inr i =>
    saTreeNodeWithUniform hp J d (a - saSplitQuantile (hp J) a z.1) z.2.2 i

/-- The total at the selected node. -/
def saTreeNode {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J d : ℕ) (a : ℝ) (z : SATreeNoise J) (i : SATreeIndex d) : ℝ :=
  (saTreeNodeWithUniform hp J d a z i).1

theorem measurable_saTreeNodeWithUniform {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J d : ℕ) (i : SATreeIndex d) :
    Measurable (fun z : ℝ × SATreeNoise J => saTreeNodeWithUniform hp J d z.1 z.2 i) := by
  induction J generalizing d with
  | zero => exact measurable_fst.prodMk measurable_const
  | succ J ih =>
    cases d with
    | zero => exact measurable_fst.prodMk measurable_snd.fst
    | succ d =>
      cases i with
      | inl i =>
        exact (ih d i).comp (f := fun z : ℝ × SATreeNoise (J + 1) =>
          (saSplitQuantile (hp J) z.1 z.2.1, z.2.2.1)) (by fun_prop)
      | inr i =>
        exact (ih d i).comp (f := fun z : ℝ × SATreeNoise (J + 1) =>
          (z.1 - saSplitQuantile (hp J) z.1 z.2.1, z.2.2.2)) (by fun_prop)

theorem measurable_saTreeNode {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J d : ℕ) (i : SATreeIndex d) :
    Measurable (fun z : ℝ × SATreeNoise J => saTreeNode hp J d z.1 z.2 i) :=
  (measurable_saTreeNodeWithUniform hp J d i).fst

/-- Every internal node has the correct sum law and an independent fresh uniform. -/
theorem saTreeNodeWithUniform_law {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J d : ℕ) (hd : d < J) (i : SATreeIndex d) :
    (((hp J).law : Measure ℝ).prod (saTreeNoiseLaw J)).map
      (fun z => saTreeNodeWithUniform hp J d z.1 z.2 i) =
        ((hp (J - d)).law : Measure ℝ).prod saUniform := by
  induction J generalizing d with
  | zero => omega
  | succ J ih =>
    cases d with
    | zero =>
      change (((hp (J + 1)).law : Measure ℝ).prod
        (saUniform.prod ((saTreeNoiseLaw J).prod (saTreeNoiseLaw J)))).map
        (fun z : ℝ × (ℝ × SATreeNoise J × SATreeNoise J) => (z.1, z.2.1)) = _
      have he := map_prod_map ((hp (J + 1)).law : Measure ℝ)
        (saUniform.prod ((saTreeNoiseLaw J).prod (saTreeNoiseLaw J)))
        measurable_id measurable_fst
      rw [Measure.map_id, Measure.map_fst_prod, measure_univ, one_smul] at he
      exact he.symm
    | succ d =>
      have hd' : d < J := by omega
      cases i with
      | inl i =>
        have hedge := (hp J).splitQuantile_subtree_left_law (saTreeNoiseLaw J)
        rw [← hstep J] at hedge
        have he := congrArg (fun μ : Measure (ℝ × SATreeNoise J) => μ.map
          (fun z => saTreeNodeWithUniform hp J d z.1 z.2 i)) hedge
        rw [Measure.map_map (measurable_saTreeNodeWithUniform hp J d i) (by fun_prop),
          ih d hd' i] at he
        convert he using 1 <;> first | rfl | simp only [Nat.add_sub_add_right]
      | inr i =>
        have hedge := (hp J).splitQuantile_subtree_right_law (saTreeNoiseLaw J)
        rw [← hstep J] at hedge
        have he := congrArg (fun μ : Measure (ℝ × SATreeNoise J) => μ.map
          (fun z => saTreeNodeWithUniform hp J d z.1 z.2 i)) hedge
        rw [Measure.map_map (measurable_saTreeNodeWithUniform hp J d i) (by fun_prop),
          ih d hd' i] at he
        convert he using 1 <;> first | rfl | simp only [Nat.add_sub_add_right]

/-- The correct marginal law also holds for the terminal leaves. -/
theorem saTreeNode_law {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J d : ℕ) (hd : d ≤ J) (i : SATreeIndex d) :
    (((hp J).law : Measure ℝ).prod (saTreeNoiseLaw J)).map
      (fun z => saTreeNode hp J d z.1 z.2 i) = (hp (J - d)).law := by
  induction J generalizing d with
  | zero =>
    have : d = 0 := by omega
    subst d
    change (((hp 0).law : Measure ℝ).prod (saTreeNoiseLaw 0)).map Prod.fst = (hp 0).law
    simp
  | succ J ih =>
    cases d with
    | zero =>
      change (((hp (J + 1)).law : Measure ℝ).prod (saTreeNoiseLaw (J + 1))).map Prod.fst =
        (hp (J + 1)).law
      simp
    | succ d =>
      have hd' : d ≤ J := by omega
      cases i with
      | inl i =>
        have hedge := (hp J).splitQuantile_subtree_left_law (saTreeNoiseLaw J)
        rw [← hstep J] at hedge
        have he := congrArg (fun μ : Measure (ℝ × SATreeNoise J) => μ.map
          (fun z => saTreeNode hp J d z.1 z.2 i)) hedge
        rw [Measure.map_map (measurable_saTreeNode hp J d i) (by fun_prop), ih d hd' i] at he
        convert he using 1 <;> first | rfl | simp only [Nat.add_sub_add_right]
      | inr i =>
        have hedge := (hp J).splitQuantile_subtree_right_law (saTreeNoiseLaw J)
        rw [← hstep J] at hedge
        have he := congrArg (fun μ : Measure (ℝ × SATreeNoise J) => μ.map
          (fun z => saTreeNode hp J d z.1 z.2 i)) hedge
        rw [Measure.map_map (measurable_saTreeNode hp J d i) (by fun_prop), ih d hd' i] at he
        convert he using 1 <;> first | rfl | simp only [Nat.add_sub_add_right]

/-- Appending one left or right step to a node address. -/
def saTreeChildIndex : (d : ℕ) → SATreeIndex d → Bool → SATreeIndex (d + 1)
  | 0, _, false => Sum.inl PUnit.unit
  | 0, _, true => Sum.inr PUnit.unit
  | d + 1, Sum.inl i, b => Sum.inl (saTreeChildIndex d i b)
  | d + 1, Sum.inr i, b => Sum.inr (saTreeChildIndex d i b)

theorem saTreeNode_zero {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J : ℕ) (a : ℝ) (z : SATreeNoise J) (i : SATreeIndex 0) : saTreeNode hp J 0 a z i = a := by
  cases J <;> rfl

/-- The actual left child is the conditional quantile with the node's shared innovation. -/
theorem saTreeNode_left {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J d : ℕ) (hd : d < J) (a : ℝ) (z : SATreeNoise J) (i : SATreeIndex d) :
    saTreeNode hp J (d + 1) a z (saTreeChildIndex d i false) =
      saSplitQuantile (hp (J - d - 1)) (saTreeNode hp J d a z i)
        (saTreeNodeWithUniform hp J d a z i).2 := by
  induction J generalizing d a with
  | zero => omega
  | succ J ih =>
    cases d with
    | zero =>
      change saTreeNode hp J 0 (saSplitQuantile (hp J) a z.1) z.2.1 PUnit.unit =
        saSplitQuantile (hp J) a z.1
      exact saTreeNode_zero hp J _ _ _
    | succ d =>
      cases i with
      | inl i =>
        simpa only [saTreeNode, saTreeNodeWithUniform, saTreeChildIndex, Nat.succ_sub_succ_eq_sub]
          using ih d (by omega) (saSplitQuantile (hp J) a z.1) z.2.1 i
      | inr i =>
        simpa only [saTreeNode, saTreeNodeWithUniform, saTreeChildIndex, Nat.succ_sub_succ_eq_sub]
          using ih d (by omega) (a - saSplitQuantile (hp J) a z.1) z.2.2 i

/-- The right child is the remaining parent total, with exact conservation. -/
theorem saTreeNode_right {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J d : ℕ) (hd : d < J) (a : ℝ) (z : SATreeNoise J) (i : SATreeIndex d) :
    saTreeNode hp J (d + 1) a z (saTreeChildIndex d i true) =
      saTreeNode hp J d a z i -
      saSplitQuantile (hp (J - d - 1)) (saTreeNode hp J d a z i)
        (saTreeNodeWithUniform hp J d a z i).2 := by
  induction J generalizing d a with
  | zero => omega
  | succ J ih =>
    cases d with
    | zero =>
      change saTreeNode hp J 0 (a - saSplitQuantile (hp J) a z.1) z.2.2 PUnit.unit =
        a - saSplitQuantile (hp J) a z.1
      exact saTreeNode_zero hp J _ _ _
    | succ d =>
      cases i with
      | inl i =>
        simpa only [saTreeNode, saTreeNodeWithUniform, saTreeChildIndex, Nat.succ_sub_succ_eq_sub]
          using ih d (by omega) (saSplitQuantile (hp J) a z.1) z.2.1 i
      | inr i =>
        simpa only [saTreeNode, saTreeNodeWithUniform, saTreeChildIndex, Nat.succ_sub_succ_eq_sub]
          using ih d (by omega) (a - saSplitQuantile (hp J) a z.1) z.2.2 i

theorem saTreeNode_children_sum {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J d : ℕ) (hd : d < J) (a : ℝ) (z : SATreeNoise J) (i : SATreeIndex d) :
    saTreeNode hp J (d + 1) a z (saTreeChildIndex d i false) +
      saTreeNode hp J (d + 1) a z (saTreeChildIndex d i true) = saTreeNode hp J d a z i := by
  rw [saTreeNode_left hp J d hd, saTreeNode_right hp J d hd]
  ring

/-- The innovation at each node depends only on the common noise, never on the chosen law. -/
theorem saTreeNode_uniform_eq {p q : ℕ → ℝ → ℝ}
    (hp : ∀ j, SADensity (p j)) (hq : ∀ j, SADensity (q j))
    (J d : ℕ) (a b : ℝ) (z : SATreeNoise J) (i : SATreeIndex d) :
    (saTreeNodeWithUniform hp J d a z i).2 = (saTreeNodeWithUniform hq J d b z i).2 := by
  induction J generalizing d a b with
  | zero => rfl
  | succ J ih =>
    cases d with
    | zero => rfl
    | succ d =>
      cases i with
      | inl i => exact ih d _ _ z.2.1 i
      | inr i => exact ih d _ _ z.2.2 i

/-- Terminal node values agree pointwise with the constructed leaf vector. -/
theorem saTreeNode_leaf {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J : ℕ) (a : ℝ) (z : SATreeNoise J) (i : SATreeIndex J) :
    saTreeNode hp J J a z i = saTreeFlatten J (saTreeRun hp J a z) i := by
  induction J generalizing a with
  | zero => rfl
  | succ J ih =>
    cases i with
    | inl i => exact ih _ z.2.1 i
    | inr i => exact ih _ z.2.2 i

/-- The node and its uniform in the complete common-seed construction. -/
def saTreeUniformNode {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j)) (J d : ℕ)
    (z : ℝ × SATreeNoise J) (i : SATreeIndex d) : ℝ × ℝ :=
  saTreeNodeWithUniform hp J d (saQuantile (cdf ((hp J).law : Measure ℝ)) z.1) z.2 i

theorem measurable_saTreeUniformNode {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J d : ℕ) (i : SATreeIndex d) : Measurable (fun z => saTreeUniformNode hp J d z i) :=
  (measurable_saTreeNodeWithUniform hp J d i).comp
    (f := fun z : ℝ × SATreeNoise J => (saQuantile (cdf ((hp J).law : Measure ℝ)) z.1, z.2))
    (((hp J).regularCDF.measurable_quantile.comp measurable_fst).prodMk measurable_snd)

/-- Exact internal-node joint marginals on the actual common-seed probability space. -/
theorem saTreeUniformNode_law {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J d : ℕ) (hd : d < J) (i : SATreeIndex d) :
    (saTreeSharedLaw J).map (fun z => saTreeUniformNode hp J d z i) =
      ((hp (J - d)).law : Measure ℝ).prod saUniform := by
  rw [← saTreeNodeWithUniform_law hp hstep J d hd i, ← saTreeRootInput_law hp J,
    Measure.map_map (measurable_saTreeNodeWithUniform hp J d i)
      (show Measurable (fun z : ℝ × SATreeNoise J =>
        (saQuantile (cdf ((hp J).law : Measure ℝ)) z.1, z.2)) from
        ((hp J).regularCDF.measurable_quantile.comp measurable_fst).prodMk measurable_snd)]
  rfl

end

end PGM
