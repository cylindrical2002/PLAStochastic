import PLAStochastic.Index.KEP.ReferenceScale.BoundedRareCertificateBudget
import PLAStochastic.Index.KEP.ReferenceScale.RareCertificateSeries
import PLAStochastic.Index.GEP.SurvivalBound.Constants

/-!
# All original rare certificates at a fixed stopping-scale weight

Both the bad-proportion tail and the joint tiny-bridge survival tail retain an
exponentially small tolerance factor. The remaining inverse-square survival
rate pays the complete quadratic pair count, with an explicit sixth-power
tolerance cost. Tests may vary with the original prefix length.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

theorem kepReference_original_bounded_rare_certificate_fixed_scale_series_budget :
    ∃ thetaMax eps0 V : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧ 0 < V ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c u0 : ℝ,
        0 < K ∧ 0 < c ∧ 0 < u0 ∧ u0 ≤ theta / 32 ∧
        ∀ eps, eps0 ≤ eps → ∀ _heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ layer, ∀ _hlayer : 1 ≤ layer, ∀ u : ℝ, 0 ≤ u → u ≤ V / eps ^ 2 → u ≤ u0 →
          ∀ phi phi' phi'' : ℕ → ℝ → ℝ,
            (∀ n x, HasDerivAt (phi n) (phi' n x) x) →
            (∀ n x, HasDerivAt (phi' n) (phi'' n x) x) →
            (∀ n, Continuous (phi'' n)) →
            (∀ n, ∃ Mtest : ℝ, ∀ t, |phi n t| ≤ Mtest ∧ |phi' n t| ≤ Mtest ∧ |phi'' n t| ≤ Mtest) →
            ∀ B : ℝ, 0 ≤ B → (∀ n t, 0 ≤ t → |phi n t| ≤ B * Real.exp (u * t)) →
          let F := fun n : ℕ => if 16 * eps ≤ (n : ℝ) then
            |kepSurvivingRareTerm eps (kepReferenceLaw eps layer)
              (kepReferenceGraphBridgeCutoff eps) n (phi'' n)| else 0
          Summable F ∧ (∑' n : ℕ, F n) ≤
            B * K * eps ^ 6 * Real.exp (-c * eps) *
              (1 + kepReferenceWeightedSecondNorm theta eps layer) := by
  obtain ⟨tm, e0, Vp, htm, he0, hVp, hpair⟩ := kepReference_original_bounded_rare_certificate_fixed_scale_budget
  refine ⟨tm, max e0 2, Vp, htm, he0.trans (le_max_left _ _), hVp, ?_⟩
  intro theta ht htcap
  obtain ⟨Kp, c, u0, hKp, hc, hu0, hucap, hpb⟩ := hpair theta ht htcap
  let A := 2 * Real.exp 1 * (1 + 4 / c) ^ 3
  refine ⟨2 * Kp * A, c, u0, by dsimp [A]; positivity, hc, hu0, hucap, ?_⟩
  intro eps he heps layer hlayer u hu huMax huDirect phi phi' phi'' hdphi hddphi hcphi hsupp B hB hphiB
  dsimp only
  let J := kepReferenceWeightedSecondNorm theta eps layer
  let r := c / (2 * eps ^ 2)
  let G := fun n : ℕ => (n + 1 : ℝ) ^ 2 * Real.exp (-r * n)
  let D := B * Kp * (1 + J) * 2 * Real.exp (-c * eps)
  have he2 : 2 ≤ eps := (le_max_right _ _).trans he
  have hepos : 0 < eps := by linarith
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps layer
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hsG : Summable G := kep_summable_polynomial_exp hr 2
  have hbG : (∑' n : ℕ, G n) ≤ A * eps ^ 6 := by
    have hh := Real.tsum_polynomial_mul_exp_neg_le hr 2
    have hinv : 1 + 2 / r ≤ (1 + 4 / c) * eps ^ 2 := by
      have heq : 2 / r = (4 / c) * eps ^ 2 := by dsimp [r]; field_simp; ring
      rw [heq]
      nlinarith [sq_nonneg (eps - 1)]
    calc
      _ ≤ 2 * Real.exp 1 * (1 + 2 / r) ^ 3 := by simpa [G] using hh
      _ ≤ 2 * Real.exp 1 * ((1 + 4 / c) * eps ^ 2) ^ 3 := by gcongr
      _ = A * eps ^ 6 := by dsimp [A]; ring
  let F := fun n : ℕ => if 16 * eps ≤ (n : ℝ) then
    |kepSurvivingRareTerm eps (kepReferenceLaw eps layer)
      (kepReferenceGraphBridgeCutoff eps) n (phi'' n)| else 0
  have hb (n : ℕ) : F n ≤ D * G n := by
    by_cases hn : 16 * eps ≤ (n : ℝ)
    · have hn18 : 18 ≤ n := by
        have hnr : (18 : ℝ) ≤ n := by linarith
        exact_mod_cast hnr
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      obtain ⟨Mtest, htest⟩ := hsupp (k + 1)
      have hp (ij : ℕ × ℕ) (hij : ij ∈ certPairs eps (k + 1)) :
          |kepCertificateTerm eps (kepReferenceLaw eps layer) (k + 1) ij.1 ij.2
            (kepCertificateRareCutoff (kepReferenceGraphBridgeCutoff eps) ij.1 ij.2) (phi'' (k + 1))| ≤
            B * Kp * (1 + J) * 2 * Real.exp (-c * eps) * Real.exp (-r * (k + 1)) := by
        obtain ⟨hlt, hlast, hlong⟩ := mem_certPairs.mp hij
        have hlong' : 2 * eps < (ij.2 - ij.1 : ℕ) := by
          rw [Nat.cast_sub hlt.le]
          exact hlong
        have hh := hpb eps ((le_max_left _ _).trans he) heps layer hlayer k ij.1 ij.2
          hn18 (by simpa only [Nat.cast_succ] using hn) hlt hlast hlong u hu huMax huDirect
          (phi (k + 1)) (phi' (k + 1)) (phi'' (k + 1)) (hdphi _) (hddphi _) (hcphi _)
          Mtest htest B hB (hphiB _)
        have ht := kep_rare_certificate_tail_envelope hc (by linarith) hn hlong'
        simp only [Nat.cast_succ] at ht
        calc
          _ ≤ _ := hh
          _ ≤ B * Kp * (1 + J) *
              (2 * Real.exp (-c * eps) * Real.exp (-(c / (2 * eps ^ 2)) * (k + 1))) :=
            mul_le_mul_of_nonneg_left ht (by positivity)
          _ = _ := by dsimp [r]; ring
      have hcard : ((certPairs eps (k + 1)).card : ℝ) ≤ (k + 1 + 1 : ℝ) ^ 2 := by
        exact_mod_cast surv_card_certPairs_le eps (k + 1)
      have hsum := Finset.sum_le_card_nsmul (certPairs eps (k + 1)) _ _ hp
      dsimp only [F]
      rw [if_pos hn, kepSurvivingRareTerm]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply hsum.trans
      simp only [nsmul_eq_mul] at *
      have hh := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤
        B * Kp * (1 + J) * 2 * Real.exp (-c * eps) * Real.exp (-r * (k + 1)))
      convert hh using 1
      dsimp [D, G]
      push_cast
      ring
    · simp only [F, if_neg hn]
      exact mul_nonneg hD (by dsimp [G]; positivity)
  have hsF := (hsG.mul_left D).of_nonneg_of_le (fun n => by dsimp [F]; split <;> positivity) hb
  refine ⟨hsF, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, D * G n := hsF.tsum_le_tsum hb (hsG.mul_left D)
    _ = D * ∑' n : ℕ, G n := tsum_mul_left
    _ ≤ D * (A * eps ^ 6) := mul_le_mul_of_nonneg_left hbG hD
    _ = _ := by dsimp [D, J]; ring

end

end PGM
