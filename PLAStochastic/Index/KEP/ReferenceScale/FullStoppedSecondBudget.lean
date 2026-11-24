import PLAStochastic.Index.KEP.ReferenceScale.PhysicalWeightBudgets
import PLAStochastic.Index.KEP.ReferenceScale.BoundedStoppedPrefixBudget

/-!
# Every actual short stopped prefix at the physical output weight

The finite exceptional small prefix lengths have an empty stopping event by
the original deterministic minimum segment length. The remaining lengths are
paid by the genuine inserted negative-moment estimate, at theta/C.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kep_short_stopped_prefix_empty {eps : ℝ} (heps : 9 ≤ eps)
    {n : ℕ} (hn : n ≤ 17) :
    {g : ℕ → ℝ | gapSegLen eps g ≤ (n : ℕ∞)} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have hT := floor_two_eps_lt_pairSegLen (by linarith : 0 ≤ eps) (fun t => (g t, 1))
  change ((⌊2 * eps⌋₊ : ℕ) : ℕ∞) < gapSegLen eps g at hT
  have hf : 18 ≤ ⌊2 * eps⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hnf : n ≤ ⌊2 * eps⌋₊ := by omega
  have hne : (n : ℕ∞) ≤ ((⌊2 * eps⌋₊ : ℕ) : ℕ∞) := by exact_mod_cast hnf
  exact (not_le.mpr (hne.trans_lt hT)) hg

theorem kepReference_full_short_stopped_second_budget :
    ∃ thetaMax : ℝ, 0 < thetaMax ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c E : ℝ,
        0 < K ∧ 0 < c ∧ kepReferenceClassicalThreshold ≤ E ∧
        ∀ eps, E ≤ eps → ∀ _heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j : ℕ, ∀ _hj : 1 ≤ j, ∀ n : ℕ, (n : ℝ) ≤ 17 * eps →
          ∀ phi phi' phi'' : ℝ → ℝ,
            (∀ x, HasDerivAt phi (phi' x) x) → (∀ x, HasDerivAt phi' (phi'' x) x) →
            Continuous phi'' → ∀ M : ℝ,
              (∀ t, |phi t| ≤ M ∧ |phi' t| ≤ M ∧ |phi'' t| ≤ M) →
            ∀ B : ℝ, 0 ≤ B → (∀ t, 0 ≤ t → |phi t| ≤
              B * Real.exp (theta * t / lawC eps (kepReferenceLaw eps j))) →
          |∫ g in {g : ℕ → ℝ | gapSegLen eps g ≤ (n : ℕ∞)},
            phi'' (gapKeys g n) ∂iidLaw (kepReferenceLaw eps j)| ≤
            B * K * (n + 1 : ℝ) * (1 + kepReferenceWeightedSecondNorm theta eps j) *
              Real.exp (-c * eps) := by
  obtain ⟨tm, e0, htm, he0, hstop⟩ := kepReference_original_bounded_stopped_prefix_second_budget
  refine ⟨tm, htm, ?_⟩
  intro theta ht htmax
  obtain ⟨K, c, u0, hK, hc, hu0, -, hb⟩ := hstop theta ht htmax
  have hcb : 0 < kepGraphMeanBracket := lt_of_lt_of_le (by norm_num) kepGraphMeanBracket_ge_one
  obtain ⟨ew, _hew, hw⟩ := kepReference_output_weight_admissible ht.le
    (mul_pos ht hcb) hu0 (by rw [mul_div_cancel_right₀ _ hcb.ne'])
  refine ⟨K, c, max e0 (max ew 9), hK, hc, he0.trans (le_max_left _ _), ?_⟩
  intro eps he heps j hj n hn phi phi' phi'' hdphi hddphi hcphi'' M htest B hB hphiB
  have he0' : e0 ≤ eps := (le_max_left _ _).trans he
  have hew' : ew ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans he)
  have he9 : 9 ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans he)
  have hphysical := hw eps hew' j
  by_cases hn18 : 18 ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two] using
      hb eps he0' heps j hj k hn18 (by simpa only [Nat.cast_succ] using hn)
      (theta / lawC eps (kepReferenceLaw eps j)) hphysical.2.1 hphysical.2.2.2.1
      phi phi' phi'' hdphi hddphi hcphi'' M htest B hB
      (fun t ht0 => by simpa only [div_mul_eq_mul_div] using hphiB t ht0)
  · rw [kep_short_stopped_prefix_empty he9 (by omega), setIntegral_empty, abs_zero]
    have hJ := kepReferenceWeightedSecondNorm_nonneg theta eps j
    positivity

end

end PGM
