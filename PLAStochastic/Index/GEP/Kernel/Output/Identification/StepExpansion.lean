import PLAStochastic.Index.GEP.Kernel.Output.Finite.DirectPrimitive
import PLAStochastic.Index.GEP.Kernel.Output.Identification.FacetSeries
import PLAStochastic.Index.GEP.Kernel.Output.Finite.StopSeries

/-!
# The birth and post-mark occupation expansion

The first term includes the marked gap itself; subsequent terms are genuine
surviving increments. This expansion is absolutely dominated by the same
deleted-mark windows for both the test primitive and its direct derivative.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval ENNReal

def outputStep (eps : ℝ) (F : ℝ → ℝ) (a : ℕ × ℕ) (x : ℝ)
    (g : ℕ → ℝ) : ℝ :=
  if a.2 ≤ a.1 then (survSet eps a.1).indicator
    (fun h => F (gapKeys h (a.1+1)) - if a.2 = a.1 then 0 else F (gapKeys h a.1))
      (Function.update g a.2 x) else 0

theorem output_step_birth (eps : ℝ) (F : ℝ → ℝ) (i : ℕ) (x : ℝ) (g : ℕ → ℝ) :
    outputStep eps F (i,i) x g = (survSet eps i).indicator
      (fun g => F (gapKeys (Function.update g i x) (i+1))) g := by
  simp only [outputStep, le_refl, if_true, sub_zero, indicator_apply,
    survSet, mem_ofPred_eq, lt_gapSegLen_update_iff]

theorem output_step_after (eps : ℝ) (F : ℝ → ℝ) {k i : ℕ} (hik : i < k)
    (x : ℝ) (g : ℕ → ℝ) :
    outputStep eps F (k,i) x g = incInd eps F k (Function.update g i x) := by
  simp only [outputStep, hik.le, if_true, hik.ne, if_false, incInd]

theorem output_step_measurable (eps : ℝ) {F : ℝ → ℝ} (hF : Measurable F)
    (a : ℕ × ℕ) (x : ℝ) : Measurable (outputStep eps F a x) := by
  classical
  unfold outputStep
  split_ifs with ha he
  · exact ((hF.comp (rawAsm_measurable_gapKeys (a.1+1))).sub measurable_const
      |>.indicator (measurableSet_survSet eps a.1)).comp
        ((measurable_update_pair a.2).comp (measurable_const.prodMk measurable_id))
  · exact ((hF.comp (rawAsm_measurable_gapKeys (a.1+1))).sub
      (hF.comp (rawAsm_measurable_gapKeys a.1))
      |>.indicator (measurableSet_survSet eps a.1)).comp
        ((measurable_update_pair a.2).comp (measurable_const.prodMk measurable_id))
  · exact measurable_const

theorem output_step_of_eq {eps x : ℝ} (F : ℝ → ℝ) {g : ℕ → ℝ} {i m : ℕ}
    (hm : gapSegLen eps (Function.update g i x) = m) (k : ℕ) :
    outputStep eps F (k,i) x g = if i ≤ k then
      if k < m then F (gapKeys (Function.update g i x) (k+1)) -
        if i = k then 0 else F (gapKeys (Function.update g i x) k) else 0 else 0 := by
  unfold outputStep
  dsimp only
  by_cases hi : i ≤ k
  · rw [if_pos hi, if_pos hi]
    by_cases hk : k < m
    · rw [if_pos hk, indicator_of_mem ((mem_survSet_iff_of_eq hm k).mpr hk)]
    · rw [if_neg hk, indicator_of_notMem (fun h => hk ((mem_survSet_iff_of_eq hm k).mp h))]
  · rw [if_neg hi, if_neg hi]

theorem output_step_sum {eps x : ℝ} (F : ℝ → ℝ) {g : ℕ → ℝ} {i m : ℕ}
    (hm : gapSegLen eps (Function.update g i x) = m) (n : ℕ) :
    (∑ k ∈ Finset.range n, outputStep eps F (k,i) x g) =
      if i < min n m then F (gapKeys (Function.update g i x) (min n m)) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rw [output_step_of_eq F hm]
    by_cases hn : n < m
    · rw [min_eq_left hn.le, min_eq_left (show n+1 ≤ m by omega)]
      by_cases hi : i < n
      · simp only [hi, hi.le, hi.ne, if_true, if_false, hn,
          show i < n+1 by omega]
        ring
      · by_cases he : i = n
        · subst i
          simp only [lt_self_iff_false, if_false, le_refl, if_true, hn,
            Nat.lt_succ_self, sub_zero, zero_add]
        · have hni : ¬ i ≤ n := by omega
          have hni' : ¬ i < n+1 := by omega
          simp only [hi, hni, hni', if_false, add_zero]
    · rw [min_eq_right (by omega : m ≤ n), min_eq_right (by omega : m ≤ n+1)]
      simp only [hn, if_false, ite_self, add_zero]

theorem output_step_tsum {eps x : ℝ} (F : ℝ → ℝ) (g : ℕ → ℝ) (i : ℕ)
    (hfin : gapSegLen eps (Function.update g i x) ≠ ⊤) :
    (∑' k : ℕ, outputStep eps F (k,i) x g) =
      (survSet eps i).indicator (fun g => F (stopSum eps (Function.update g i x))) g := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  have hT := hm.symm
  rw [tsum_eq_sum (s := Finset.range m)]
  · rw [output_step_sum F hT, min_self]
    have he : g ∈ survSet eps i ↔ i < m := by
      change (i : ℕ∞) < gapSegLen eps g ↔ i < m
      rw [← lt_gapSegLen_update_iff (x := x), hT, Nat.cast_lt]
    by_cases hi : i < m
    · rw [if_pos hi, indicator_of_mem (he.mpr hi), stopSum_of_eq hT]
    · rw [if_neg hi, indicator_of_notMem (fun h => hi (he.mp h))]
  · intro k hk
    have hmk : m ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    simp only [output_step_of_eq F hT, not_lt.mpr hmk, if_false, ite_self]

theorem output_step_bound {eps x κ A : ℝ} {F : ℝ → ℝ}
    (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hF : ∀ s, 0 ≤ s → ‖F s‖ ≤ A * Real.exp (κ*s))
    {g : ℕ → ℝ} (hg : ∀ j, 0 ≤ g j) (hx : 0 ≤ x) (a : ℕ × ℕ) :
    ‖outputStep eps F a x g‖ ≤
      (2 * A * Real.exp (κ*x)) * (winSet eps a.2 (a.1+1)).indicator
        (fun g => Real.exp (κ * fluxUnmarkedSum (a.1+1) a.2 g)) g := by
  have hg' : ∀ j, 0 ≤ Function.update g a.2 x j := by
    intro j
    by_cases hj : j = a.2 <;> simp [hj, hx, hg]
  have hB0 : 0 ≤ (2*A*Real.exp (κ*x)) * (winSet eps a.2 (a.1+1)).indicator
      (fun g => Real.exp (κ * fluxUnmarkedSum (a.1+1) a.2 g)) g := by
    exact mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
  by_cases ha : a.2 ≤ a.1
  · by_cases hT : Function.update g a.2 x ∈ survSet eps a.1
    · have hW := flux_survival_subset_winSet (x := x) (by omega : a.2 < a.1+1)
        (le_refl (a.1+1)) hT
      rw [outputStep, if_pos ha, indicator_of_mem hT, indicator_of_mem hW]
      have h1 := hF _ (gapKeys_nonneg hg' (a.1+1))
      have h0 : ‖F (gapKeys (Function.update g a.2 x) a.1)‖ ≤
          A * Real.exp (κ * gapKeys (Function.update g a.2 x) (a.1+1)) := by
        exact (hF _ (gapKeys_nonneg hg' a.1)).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (gapKeys_mono hg' (Nat.le_succ _)) hκ)) hA)
      have he : (2*A*Real.exp (κ*x)) * Real.exp (κ * fluxUnmarkedSum (a.1+1) a.2 g) =
          2 * (A * Real.exp (κ * gapKeys (Function.update g a.2 x) (a.1+1))) := by
        rw [flux_gapKeys_update (by omega : a.2 < a.1+1), mul_add, Real.exp_add]
        ring
      rw [he]
      split_ifs
      · have hn := norm_nonneg (F (gapKeys (Function.update g a.2 x) (a.1+1)))
        simpa only [sub_zero] using h1.trans (by linarith)
      · exact (norm_sub_le _ _).trans (by linarith)
    · simpa only [outputStep, if_pos ha, indicator_of_notMem hT, norm_zero] using hB0
  · simpa only [outputStep, if_neg ha, norm_zero] using hB0

end
end PGM
