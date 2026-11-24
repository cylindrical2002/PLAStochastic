import PLAStochastic.Index.GEP.StrongApprox.Tree.Nodes
import PLAStochastic.Index.GEP.StrongApprox.Tree.DeterministicPropagation
import PLAStochastic.Index.LocalCount.CyclicTwo

/-! # From local split errors to all finite leaf-prefix errors -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Function Finset
open scoped ENNReal

/-- The recursive left branch occupies the first half of the numeric addresses. -/
theorem saTreeIndexEquivFin_inl_val (d : ℕ) (i : SATreeIndex d) :
    (saTreeIndexEquivFin (d + 1) (Sum.inl i)).val = (saTreeIndexEquivFin d i).val := rfl

/-- The recursive right branch occupies the second half of the numeric addresses. -/
theorem saTreeIndexEquivFin_inr_val (d : ℕ) (i : SATreeIndex d) :
    (saTreeIndexEquivFin (d + 1) (Sum.inr i)).val = 2 ^ d + (saTreeIndexEquivFin d i).val := rfl

/-- Appending one branch has the conventional binary address `2i+b`. -/
theorem saTreeIndexEquivFin_child_val (d : ℕ) (i : SATreeIndex d) (b : Bool) :
    (saTreeIndexEquivFin (d + 1) (saTreeChildIndex d i b)).val =
      2 * (saTreeIndexEquivFin d i).val + if b then 1 else 0 := by
  induction d with
  | zero => cases b <;> rfl
  | succ d ih =>
    cases i with
    | inl i =>
      change (saTreeIndexEquivFin (d + 1 + 1) (Sum.inl (saTreeChildIndex d i b))).val = _
      rw [saTreeIndexEquivFin_inl_val, saTreeIndexEquivFin_inl_val, ih]
    | inr i =>
      change (saTreeIndexEquivFin (d + 1 + 1) (Sum.inr (saTreeChildIndex d i b))).val = _
      rw [saTreeIndexEquivFin_inr_val, saTreeIndexEquivFin_inr_val, ih, pow_succ]
      omega

/-- The node array in the numeric indexing used by the deterministic dyadic estimate. -/
def saTreeNodeNat {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J : ℕ) (a : ℝ) (z : SATreeNoise J) (d i : ℕ) : ℝ :=
  if hi : i < 2 ^ d then saTreeNode hp J d a z ((saTreeIndexEquivFin d).symm ⟨i, hi⟩) else 0

theorem saTreeNodeNat_zero {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J : ℕ) (a : ℝ) (z : SATreeNoise J) : saTreeNodeNat hp J a z 0 0 = a := by
  rw [saTreeNodeNat, dif_pos (by norm_num)]
  exact saTreeNode_zero hp J a z _

theorem saTreeNodeNat_child {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J : ℕ) (a : ℝ) (z : SATreeNoise J) (d i : ℕ) (hi : i < 2 ^ d) (b : Bool) :
    saTreeNodeNat hp J a z (d + 1) (2 * i + if b then 1 else 0) =
      saTreeNode hp J (d + 1) a z
        (saTreeChildIndex d ((saTreeIndexEquivFin d).symm ⟨i, hi⟩) b) := by
  have hchild : 2 * i + (if b then 1 else 0) < 2 ^ (d + 1) := by
    rw [pow_succ]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have he : saTreeIndexEquivFin (d + 1)
      (saTreeChildIndex d ((saTreeIndexEquivFin d).symm ⟨i, hi⟩) b) =
      ⟨2 * i + (if b then 1 else 0), hchild⟩ := by
    apply Fin.ext
    rw [saTreeIndexEquivFin_child_val, Equiv.apply_symm_apply]
  rw [saTreeNodeNat, dif_pos hchild, ← he, Equiv.symm_apply_apply]

theorem saTreeNodeNat_children_sum {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J : ℕ) (a : ℝ) (z : SATreeNoise J) {d i : ℕ} (hd : d < J) (hi : i < 2 ^ d) :
    saTreeNodeNat hp J a z (d + 1) (2 * i) +
      saTreeNodeNat hp J a z (d + 1) (2 * i + 1) = saTreeNodeNat hp J a z d i := by
  have hleft := saTreeNodeNat_child hp J a z d i hi false
  have hright := saTreeNodeNat_child hp J a z d i hi true
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hleft hright
  rw [hleft, hright, saTreeNode_children_sum hp J d hd, saTreeNodeNat, dif_pos hi]

theorem saTreeNodeNat_leaf {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (J : ℕ) (a : ℝ) (z : SATreeNoise J) :
    saTreeNodeNat hp J a z J = vext (saTreeFlattenFin J (saTreeRun hp J a z)) := by
  funext i
  unfold saTreeNodeNat vext
  split_ifs with hi
  · exact saTreeNode_leaf hp J a z _
  · rfl

/-- With conservation, it suffices to control the local defect at the left child. -/
theorem sa_dyadic_coupling_error_of_left {s w : ℕ → ℕ → ℝ} {J : ℕ} {R D : ℝ}
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hroot : |s 0 0 - w 0 0| ≤ R)
    (hs : ∀ j < J, ∀ i < 2 ^ j, s (j + 1) (2 * i) + s (j + 1) (2 * i + 1) = s j i)
    (hw : ∀ j < J, ∀ i < 2 ^ j, w (j + 1) (2 * i) + w (j + 1) (2 * i + 1) = w j i)
    (hleft : ∀ j < J, ∀ i < 2 ^ j,
      |(s (j + 1) (2 * i) - w (j + 1) (2 * i)) - (s j i - w j i) / 2| ≤ D) :
    ∀ k ≤ 2 ^ J, |(∑ i ∈ range k, s J i) - ∑ i ∈ range k, w J i| ≤
      ((J : ℝ) + 1) * (R + 2 * D) := by
  apply sa_dyadic_coupling_error hR hD hroot hs hw
  intro j hj i hi
  have hk : i / 2 < 2 ^ j := by rw [pow_succ] at hi; omega
  have hpar : i = 2 * (i / 2) ∨ i = 2 * (i / 2) + 1 := by omega
  rcases hpar with he | he
  · simpa only [← he] using hleft j hj (i / 2) hk
  · have heq : (s (j + 1) i - w (j + 1) i) - (s j (i / 2) - w j (i / 2)) / 2 =
        -((s (j + 1) (2 * (i / 2)) - w (j + 1) (2 * (i / 2))) -
          (s j (i / 2) - w j (i / 2)) / 2) := by
      have hs' := hs j hj (i / 2) hk
      have hw' := hw j hj (i / 2) hk
      rw [← he] at hs' hw'
      linarith
    rw [heq, abs_neg]
    exact hleft j hj (i / 2) hk

/-- A pointwise leaf-prefix estimate for the actual shared-noise pair of trees. -/
theorem saTree_prefix_error {p q : ℕ → ℝ → ℝ}
    (hp : ∀ j, SADensity (p j)) (hq : ∀ j, SADensity (q j))
    (J : ℕ) (a b : ℝ) (z : SATreeNoise J) {R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hroot : |a - b| ≤ R)
    (hleft : ∀ d < J, ∀ i : SATreeIndex d,
      |(saTreeNode hp J (d + 1) a z (saTreeChildIndex d i false) -
          saTreeNode hq J (d + 1) b z (saTreeChildIndex d i false)) -
        (saTreeNode hp J d a z i - saTreeNode hq J d b z i) / 2| ≤ D) :
    ∀ k ≤ 2 ^ J,
      |vkeys (saTreeFlattenFin J (saTreeRun hp J a z)) k -
        vkeys (saTreeFlattenFin J (saTreeRun hq J b z)) k| ≤
        ((J : ℝ) + 1) * (R + 2 * D) := by
  have hb := sa_dyadic_coupling_error_of_left (s := saTreeNodeNat hp J a z)
    (w := saTreeNodeNat hq J b z) hR hD (by simpa only [saTreeNodeNat_zero] using hroot)
    (fun d hd i hi => saTreeNodeNat_children_sum hp J a z hd hi)
    (fun d hd i hi => saTreeNodeNat_children_sum hq J b z hd hi) ?_
  · intro k hk
    simpa only [saTreeNodeNat_leaf, vkeys, gapKeys] using hb k hk
  · intro d hd i hi
    have hpl := saTreeNodeNat_child hp J a z d i hi false
    have hql := saTreeNodeNat_child hq J b z d i hi false
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hpl hql
    rw [hpl, hql]
    simp only [saTreeNodeNat, dif_pos hi]
    exact hleft d hd _

end

end PGM
