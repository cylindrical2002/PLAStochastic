import PLAStochastic.Index.Model.IIDGaps
import PLAStochastic.ForMathlib.Probability.Hellinger.SequenceKernel

/-!
# The actual stopped gap prefix and its absorbing transition

The completed failed-prefix decision is retained at every finite horizon.
Zero padding after the greedy stopping rank preserves that decision because
the original failing keys have already been observed.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepStoppedPrefix (eps : ℝ) (i : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun k => if k < i ∧ (k : ℕ∞) < gapSegLen eps g then g k else 0

theorem measurable_kepStoppedPrefix (eps : ℝ) (i : ℕ) :
    Measurable (kepStoppedPrefix eps i) := by
  refine measurable_pi_lambda _ fun k => ?_
  exact Measurable.ite
    ((MeasurableSet.const (k < i)).inter ((isStoppingRule_gapSegLen eps).measurableSet_lt k))
    (measurable_pi_apply k) measurable_const

theorem kepStoppedPrefix_causal (eps : ℝ) (i : ℕ) {g g' : ℕ → ℝ}
    (hp : ∀ k < i, g k = g' k) :
    kepStoppedPrefix eps i g = kepStoppedPrefix eps i g' := by
  funext k
  by_cases hk : k < i
  · have ht : (k : ℕ∞) < gapSegLen eps g ↔ (k : ℕ∞) < gapSegLen eps g' :=
      mem_iff_of_measurableSet_comap_seqPrefix (isStoppingRule_gapSegLen eps k)
        (fun a ha => hp a (ha.trans hk))
    simp only [kepStoppedPrefix, hk, true_and, ht, hp k hk]
  · simp only [kepStoppedPrefix, hk, false_and, if_false]

theorem kepStoppedPrefix_agree_of_active {eps : ℝ} {i : ℕ} {g : ℕ → ℝ}
    (hi : (i : ℕ∞) < gapSegLen eps g) :
    ∀ k < i, kepStoppedPrefix eps i g k = g k := by
  intro k hk
  have ht : (k : ℕ∞) < gapSegLen eps g :=
    (ENat.natCast_lt_natCast.mpr hk).trans hi
  exact if_pos ⟨hk, ht⟩

theorem kepStoppedPrefix_active (eps : ℝ) (i : ℕ) (g : ℕ → ℝ) :
    (i : ℕ∞) < gapSegLen eps (kepStoppedPrefix eps i g) ↔
      (i : ℕ∞) < gapSegLen eps g := by
  by_cases hi : (i : ℕ∞) < gapSegLen eps g
  · exact (mem_iff_of_measurableSet_comap_seqPrefix (isStoppingRule_gapSegLen eps i)
      (kepStoppedPrefix_agree_of_active hi))
  · have hle : gapSegLen eps g ≤ (i : ℕ∞) := le_of_not_gt hi
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top (ENat.natCast_ne_top i) hle)
    have ht' : gapSegLen eps g = (t : ℕ∞) := ht.symm
    have hti : t ≤ i := by rw [ht'] at hle; exact ENat.natCast_le_natCast.mp hle
    have hp : ∀ k < t, kepStoppedPrefix eps i g k = g k := by
      intro k hk
      apply if_pos
      exact ⟨hk.trans_le hti, ht' ▸ ENat.natCast_lt_natCast.mpr hk⟩
    have he : gapSegLen eps (kepStoppedPrefix eps i g) = (t : ℕ∞) :=
      (mem_iff_of_measurableSet_comap_seqPrefix
        ((isStoppingRule_gapSegLen eps).measurableSet_eq t) hp).mpr ht'
    rw [he]
    exact iff_of_false (not_lt.mpr (ENat.natCast_le_natCast.mpr hti)) hi

theorem kepStoppedPrefix_succ (eps : ℝ) (i : ℕ) (g : ℕ → ℝ) :
    kepStoppedPrefix eps (i + 1) g =
      if (i : ℕ∞) < gapSegLen eps g
      then Function.update (kepStoppedPrefix eps i g) i (g i)
      else kepStoppedPrefix eps i g := by
  classical
  funext k
  by_cases hi : (i : ℕ∞) < gapSegLen eps g
  · rw [if_pos hi]
    by_cases hki : k = i
    · subst k
      rw [Function.update_self]
      exact if_pos ⟨Nat.lt_succ_self i, hi⟩
    · rw [Function.update_of_ne hki]
      by_cases hk : k < i
      · simp only [kepStoppedPrefix, hk, hk.trans (Nat.lt_succ_self i), true_and]
      · have hk' : ¬ k < i + 1 := by omega
        simp only [kepStoppedPrefix, hk, hk', false_and, if_false]
  · rw [if_neg hi]
    by_cases hki : k = i
    · subst k
      simp only [kepStoppedPrefix, hi, and_false, if_false]
    · have hk : k < i + 1 ↔ k < i := by omega
      simp only [kepStoppedPrefix, hk]

theorem kepStoppedPrefix_fixed_of_stopped {eps : ℝ} {i t : ℕ} {g : ℕ → ℝ}
    (ht : gapSegLen eps g = t) (hti : t ≤ i) :
    kepStoppedPrefix eps i g = kepStoppedPrefix eps t g := by
  funext k
  simp only [kepStoppedPrefix, ht, ENat.natCast_lt_natCast]
  by_cases hk : k < t
  · simp only [hk, hk.trans_le hti, and_self, if_true]
  · simp only [hk, and_false, if_false]

theorem kepStoppedPrefix_succ_update (eps : ℝ) (i : ℕ) (g : ℕ → ℝ) (z : ℝ) :
    kepStoppedPrefix eps (i + 1) (Function.update g i z) =
      if (i : ℕ∞) < gapSegLen eps g
      then Function.update (kepStoppedPrefix eps i g) i z
      else kepStoppedPrefix eps i g := by
  classical
  have hp : ∀ k < i, Function.update g i z k = g k := fun k hk =>
    Function.update_of_ne (Nat.ne_of_lt hk) _ _
  have ht : (i : ℕ∞) < gapSegLen eps (Function.update g i z) ↔
      (i : ℕ∞) < gapSegLen eps g :=
    mem_iff_of_measurableSet_comap_seqPrefix (isStoppingRule_gapSegLen eps i) hp
  simp only [kepStoppedPrefix_succ, kepStoppedPrefix_causal eps i hp, ht, Function.update_self]

theorem kepStoppedPrefix_gapKeys_of_active {eps : ℝ} {i : ℕ} {g : ℕ → ℝ}
    (hi : (i : ℕ∞) < gapSegLen eps g) :
    gapKeys (kepStoppedPrefix eps i g) i = gapKeys g i :=
  gapKeys_congr (kepStoppedPrefix_agree_of_active hi) i le_rfl

end

end PGM
