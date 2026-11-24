import PLAStochastic.Index.KEP.ReferenceScale.FiniteGapGeometry

/-!
# A deterministic clean third of every inserted prefix

Three disjoint consecutive blocks have equal length. At most two inserted
coordinates cannot meet all three, so one block is clean. The choice depends
only on the insertion pattern and retains at least one third minus two gaps.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open Finset

theorem kep_three_blocks_clean {n m : ℕ} (H : Finset (Fin n)) (hH : H.card ≤ 2) :
    ∃ b : Fin 3, ∀ i ∈ H, ¬(b.val * m ≤ i.val ∧ i.val < b.val * m + m) := by
  classical
  by_contra hn
  have hex : ∀ b : Fin 3, ∃ i : Fin n, i ∈ H ∧ b.val * m ≤ i.val ∧ i.val < b.val * m + m := by
    intro b
    by_contra hb
    apply hn
    refine ⟨b, ?_⟩
    intro i hi hbi
    exact hb ⟨i, hi, hbi.1, hbi.2⟩
  choose i hi hlow hhigh using hex
  let f : Fin 3 → H := fun b => ⟨i b, hi b⟩
  have hf : Function.Injective f := by
    intro b c hbc
    have hval : (i b).val = (i c).val := congrArg (fun q : H => q.val.val) hbc
    apply Fin.ext
    by_contra hne
    have horder : b.val < c.val ∨ c.val < b.val := lt_or_gt_of_ne hne
    rcases horder with horder | horder
    · have hmul := Nat.mul_le_mul_right m (Nat.succ_le_of_lt horder)
      have hb := hhigh b
      have hc := hlow c
      rw [Nat.succ_mul] at hmul
      omega
    · have hmul := Nat.mul_le_mul_right m (Nat.succ_le_of_lt horder)
      have hc := hhigh c
      have hb := hlow b
      rw [Nat.succ_mul] at hmul
      omega
  have hh := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Fintype.card_coe] at hh
  omega

theorem kep_clean_window_selection {n : ℕ} (H : Finset (Fin n)) (hH : H.card ≤ 2) :
    ∃ a w : ℕ, a + w ≤ n ∧ (n : ℝ) / 3 - 1 ≤ w ∧
      ∀ i ∈ H, ¬(a ≤ i.val ∧ i.val < a + w) := by
  obtain ⟨b, hb⟩ := kep_three_blocks_clean (m := n / 3) H hH
  refine ⟨b.val * (n / 3), n / 3, ?_, ?_, hb⟩
  · have hmul := Nat.mul_le_mul_right (n / 3) (Nat.succ_le_of_lt b.isLt)
    have hdiv : n / 3 * 3 ≤ n := Nat.div_mul_le_self n 3
    rw [Nat.succ_mul] at hmul
    rw [Nat.mul_comm] at hdiv
    omega
  · have hn : n ≤ n / 3 * 3 + 2 := by omega
    have hnR : (n : ℝ) ≤ (n / 3 : ℕ) * 3 + 2 := by exact_mod_cast hn
    linarith

end

end PGM
