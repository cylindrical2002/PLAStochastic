import PLAStochastic.Index.KEP.ReferenceScale.FiniteCertificateTransfer
import PLAStochastic.Index.KEP.ReferenceScale.RareSupportInsertionBudget
import PLAStochastic.Index.KEP.ReferenceScale.WeightedMellinFieldTesting

/-!
# Unconditional physical second budget of every original rare certificate

The true infinite iid certificate is transferred to its complete multivariate
Mellin fields. Their original nonzero support and all insertion patterns are
paid by the actual negative-moment and joint-tail bounds. No analytic or rare
probability certificate remains a premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

theorem kepReference_original_rare_certificate_second_budget :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c u0 : ℝ,
        0 < K ∧ 0 < c ∧ 0 < u0 ∧ u0 ≤ theta / 32 ∧
        ∀ eps, eps0 ≤ eps → ∀ _heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ layer, ∀ _hlayer : 1 ≤ layer, ∀ k i j : ℕ, 18 ≤ k + 1 → 16 * eps ≤ k + 1 →
            i < j → j ≤ k + 1 → 2 * eps < (j : ℝ) - i →
            ∀ u : ℝ, 0 ≤ u → u ≤ u0 / eps ^ 2 →
            ∀ phi phi' phi'' : ℝ → ℝ,
              (∀ x, HasDerivAt phi (phi' x) x) → (∀ x, HasDerivAt phi' (phi'' x) x) →
              Continuous phi'' → ∀ a b : ℝ, 0 < a → Function.support phi ⊆ Icc a b →
              ∀ B : ℝ, 0 ≤ B → (∀ t, 0 ≤ t → |phi t| ≤ B * Real.exp (u * t)) →
            |kepCertificateTerm eps (kepReferenceLaw eps layer) (k + 1) i j
              (kepCertificateRareCutoff (kepReferenceGraphBridgeCutoff eps) i j) phi''| ≤
              B * K * (1 + kepReferenceWeightedSecondNorm theta eps layer) *
                (Real.exp (-c * (k + 1)) + Real.exp (-c * (j - i : ℕ) - c * (k + 1) / eps ^ 2)) := by
  obtain ⟨ti, ei, hti, hei, hins⟩ := kepReference_original_rare_support_insertion_budget
  obtain ⟨et, het, htransfer⟩ := kepReference_original_rare_certificate_second_transfer
  obtain ⟨tm, em, htm, hem, hmeas⟩ := kepReference_insertion_measure_budgets
  obtain ⟨R, hR, hrho⟩ := kepCertificateCore_physical_bounds
  refine ⟨min ti tm, max ei (max et em), lt_min hti htm, hei.trans (le_max_left _ _), ?_⟩
  intro theta ht htheta
  obtain ⟨Ki, c, u0, hKi, hc, hu0, hucap, hib⟩ := hins theta ht (htheta.trans (min_le_left _ _))
  obtain ⟨_Km, _, hmb⟩ := hmeas theta ht (htheta.trans (min_le_right _ _))
  refine ⟨2 * R * Ki, c, u0, by positivity, hc, hu0, hucap, ?_⟩
  intro eps he heps layer hlayer k i j hn18 hn hij hjn hL u hu huMax
    phi phi' phi'' hdphi hddphi hcphi'' a b ha hsupp B hB hphiB
  let n := k + 1
  have hn' : 16 * eps ≤ (n : ℝ) := by simpa only [n, Nat.cast_add, Nat.cast_one] using hn
  let f := (kepReferenceDensity heps hlayer).density
  let S := fun x : Fin n → ℝ => ∑ t, x t
  let C := kepFiniteCertificateEvent eps n i j
  let E := kepFiniteRareSupport eps n i j
  let slope := kepFiniteCertificateSlope eps n i j
  let M := kepReferenceGraphBridgeCutoff eps
  let rho0 := fun x => 1 - kepCertificateCoreCutoff M i j (slope x)
  let rho1 := fun x => -kepCertificateCoreFirst M i j (slope x)
  let rho2 := fun x => -kepCertificateCoreSecond M i j (slope x)
  let T := fun rho : (Fin n → ℝ) → ℝ => E.indicator (fun x => phi (S x) * rho x / (S x) ^ 2)
  let J := kepReferenceWeightedSecondNorm theta eps layer
  let tail := Real.exp (-c * n) + Real.exp (-c * (j - i : ℕ) - c * n / eps ^ 2)
  let Q := B * R * Ki * (1 + J) / (n : ℝ) ^ 2 * tail
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps layer
  have hQ : 0 ≤ Q := by dsimp [Q, tail]; positivity
  have hE : MeasurableSet E := measurableSet_kepFiniteRareSupport eps n i j
  have hC : MeasurableSet C := measurableSet_kepFiniteCertificateEvent eps n i j
  have hS : Measurable S := Finset.measurable_sum Finset.univ (fun t _ => measurable_pi_apply t)
  have hslope : Measurable slope := measurable_kepFiniteCertificateSlope eps n i j
  have hr0 : Measurable rho0 := measurable_const.sub ((measurable_kepCertificateCoreCutoff M i j).comp hslope)
  have hr1 : Measurable rho1 := ((measurable_kepCertificateCoreFirst M i j).comp hslope).neg
  have hr2 : Measurable rho2 := ((measurable_kepCertificateCoreSecond M i j).comp hslope).neg
  have hb0 (x) : |rho0 x| ≤ R := by
    have hh := kepCertificateCoreCutoff_bounds M i j (slope x)
    dsimp [rho0]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hb1 (x) : |rho1 x| ≤ R := by simpa only [rho1, abs_neg] using (hrho M i j (slope x)).2.1
  have hb2 (x) : |rho2 x| ≤ R := by simpa only [rho2, abs_neg] using (hrho M i j (slope x)).2.2
  have hphim : Measurable phi :=
    (continuous_iff_continuousAt.mpr fun t => (hdphi t).continuousAt).measurable
  have hpattern (rho : (Fin n → ℝ) → ℝ) (hm : Measurable rho) (hb : ∀ x, |rho x| ≤ R)
      (r : Fin n → ℕ) (hr : (∑ t, r t) ≤ 2) :
      Integrable (fun x => T rho x * kepMellinPatternProduct f r x) volume ∧
        |∫ x, T rho x * kepMellinPatternProduct f r x| ≤ Q := by
    have hmu (t : Fin n) := hmb eps ((le_max_right _ _).trans ((le_max_right _ _).trans he))
      heps layer hlayer (r t) ((kepInsertionPattern_bounds hr).1 t)
    have : ∀ t : Fin n, IsFiniteMeasure (kepAbsDensityMeasure ((mellinOp^[r t]) f)) := fun t => (hmu t).1
    have hnegative := hib eps ((le_max_left _ _).trans he) heps layer hlayer n i j
      hn18 hn' hij hjn hL r hr u hu huMax
    have hbound (x : Fin n → ℝ) (hx : x ∈ E) :
        |phi (S x) * rho x| ≤ (B * R) * Real.exp (u * S x) := by
      rw [abs_mul]
      have hpos : 0 < S x := kepFiniteCertificateEvent_sum_pos (by omega) hx.1
      exact (mul_le_mul (hphiB (S x) hpos.le) (hb x) (abs_nonneg _) (by positivity)).trans_eq (by ring)
    have hh := kep_mellin_pattern_test_bound (psi := fun x => phi (S x) * rho x)
      (kepReferenceDensity heps hlayer).measurable r hS hE
      ((hphim.comp hS).mul hm) (by positivity : 0 ≤ B * R) hbound hnegative.1
    have heq (x : Fin n → ℝ) : T rho x * kepMellinPatternProduct f r x =
        E.indicator (fun x => phi (S x) * rho x / (S x) ^ 2 * kepMellinPatternProduct f r x) x := by
      by_cases hx : x ∈ E
      · simp only [T, indicator_of_mem hx]
      · simp only [T, indicator_of_notMem hx, zero_mul]
    refine ⟨?_, ?_⟩
    · simp_rw [heq]
      exact hh.1
    · have htest : |∫ x, T rho x * kepMellinPatternProduct f r x| ≤
          B * R * ∫ x in E, ((S x) ^ 2)⁻¹ * Real.exp (u * S x)
            ∂Measure.pi (fun t => kepReferenceInsertionMeasure heps hlayer (r t)) := by
        simp_rw [heq]
        rw [integral_indicator hE]
        convert hh.2 using 1
        rfl
      apply htest.trans
      exact (mul_le_mul_of_nonneg_left hnegative.2 (by positivity)).trans_eq (by dsimp [Q, J, tail]; ring)
  have hbudget : ∀ V, (V = T rho0 ∨ V = T rho1 ∨ V = T rho2) →
      ∀ r : Fin n → ℕ, (∑ t, r t) ≤ 2 →
        Integrable (fun x => V x * kepMellinPatternProduct f r x) volume ∧
          |∫ x, V x * kepMellinPatternProduct f r x| ≤ Q := by
    intro V hV r hr
    rcases hV with hV | hV | hV
    · subst V
      exact hpattern rho0 hr0 hb0 r hr
    · subst V
      exact hpattern rho1 hr1 hb1 r hr
    · subst V
      exact hpattern rho2 hr2 hb2 r hr
  have hfields := kep_weighted_mellin_fields_test_budget hQ hbudget
  let F := fun x : Fin n → ℝ => T rho0 x *
    (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x) +
    T rho1 x * (2 * kepProductMellinFirst f x - 3 * kepProductDensity f x) + T rho2 x * kepProductDensity f x
  let G := fun x : Fin n → ℝ => phi (S x) / (S x) ^ 2 *
    (rho0 x * (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x) +
      rho1 x * (2 * kepProductMellinFirst f x - 3 * kepProductDensity f x) + rho2 x * kepProductDensity f x)
  have heq : C.indicator G = F := by
    funext x
    by_cases hx : x ∈ C
    · rw [indicator_of_mem hx]
      by_cases hxE : x ∈ E
      · simp only [F, T, indicator_of_mem hxE]
        dsimp [G]
        ring
      · have hzero : rho0 x = 0 ∧ rho1 x = 0 ∧ rho2 x = 0 := by
          have hf : ¬(1 - kepCertificateCoreCutoff M i j (slope x) ≠ 0 ∨
              kepCertificateCoreFirst M i j (slope x) ≠ 0 ∨ kepCertificateCoreSecond M i j (slope x) ≠ 0) :=
            fun hf => hxE ⟨hx, hf⟩
          simp only [not_or, not_not] at hf
          exact ⟨hf.1, by dsimp [rho1]; rw [hf.2.1, neg_zero], by dsimp [rho2]; rw [hf.2.2, neg_zero]⟩
        simp only [F, T, indicator_of_notMem hxE, zero_mul, zero_add]
        dsimp [G]
        rw [hzero.1, hzero.2.1, hzero.2.2]
        ring
    · have hxE : x ∉ E := fun hh => hx hh.1
      simp only [indicator_of_notMem hx, F, T, indicator_of_notMem hxE, zero_mul, zero_add]
  have htransfer' := htransfer eps ((le_max_left _ _).trans ((le_max_right _ _).trans he)) heps
    layer hlayer k M i j (by omega) hjn phi phi' phi'' hdphi hddphi hcphi'' a b ha hsupp
  dsimp only at htransfer'
  have hterm : kepCertificateTerm eps (kepReferenceLaw eps layer) (k + 1) i j
      (kepCertificateRareCutoff M i j) phi'' = ∫ x, F x := by
    rw [htransfer', ← integral_indicator hC, heq]
  rw [hterm]
  apply hfields.2.trans
  have hnR : (18 : ℝ) ≤ n := by exact_mod_cast hn18
  have hnpos : (0 : ℝ) < n := by linarith
  have hpoly : (n : ℝ) ^ 2 + 5 * n + 6 ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
  apply (mul_le_mul_of_nonneg_right hpoly hQ).trans_eq
  dsimp only [Q, J, tail, n]
  push_cast
  field_simp

end

end PGM
