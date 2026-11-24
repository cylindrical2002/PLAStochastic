import PLAStochastic.Index.KEP.ReferenceScale.StoppedNegativeBudget
import PLAStochastic.Index.KEP.ReferenceScale.ActualConeTransfer
import PLAStochastic.Index.KEP.ReferenceScale.FiniteCertificateGeometry
import PLAStochastic.Index.KEP.ReferenceScale.WeightedMellinFieldTesting

/-!
# The actual short stopped prefix has an exponentially small second budget

The unchanged stopping event is a positive cone. The exact iid marginal and
the full Mellin formula transfer its physical derivative, and every signed
insertion is paid by the proved actual inverse-square stopping budget.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set Filter

theorem kepFinitePositive_smul (n : ℕ) (x : Fin n → ℝ) {c : ℝ} (hc : 0 < c) :
    c • x ∈ kepFinitePositive n ↔ x ∈ kepFinitePositive n := by
  simp only [kepFinitePositive, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul,
    mul_pos_iff_of_pos_left hc]

theorem kepFinitePositive_sum_pos {n : ℕ} (hn : 0 < n)
    {x : Fin n → ℝ} (hx : x ∈ kepFinitePositive n) : 0 < ∑ t, x t := by
  apply sum_pos (fun t _ => hx t)
  exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem kep_ae_finite_positive {nu : ProbabilityMeasure ℝ}
    (hnu : (nu : Measure ℝ) (Iic 0) = 0) (n : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n => (nu : Measure ℝ)), x ∈ kepFinitePositive n := by
  have hs : ∀ᵐ t ∂(nu : Measure ℝ), 0 < t := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnu] with t ht
    exact lt_of_not_ge ht
  exact eventually_all.mpr (fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => (nu : Measure ℝ)) (i := i)).eventually hs)

theorem kepReference_original_stopped_prefix_second_budget :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c u0 : ℝ,
        0 < K ∧ 0 < c ∧ 0 < u0 ∧ u0 ≤ theta / 8 ∧
        ∀ eps, eps0 ≤ eps → ∀ _heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ layer, ∀ _hlayer : 1 ≤ layer, ∀ k : ℕ, 18 ≤ k + 1 → (k + 1 : ℝ) ≤ 17 * eps →
          ∀ u : ℝ, 0 ≤ u → u ≤ u0 → ∀ phi phi' phi'' : ℝ → ℝ,
            (∀ x, HasDerivAt phi (phi' x) x) → (∀ x, HasDerivAt phi' (phi'' x) x) →
            Continuous phi'' → ∀ a b : ℝ, 0 < a → Function.support phi ⊆ Icc a b →
            ∀ B : ℝ, 0 ≤ B → (∀ t, 0 ≤ t → |phi t| ≤ B * Real.exp (u * t)) →
          |∫ g in {g : ℕ → ℝ | gapSegLen eps g ≤ ((k + 1 : ℕ) : ℕ∞)},
            phi'' (gapKeys g (k + 1)) ∂iidLaw (kepReferenceLaw eps layer)| ≤
            B * K * (k + 2 : ℝ) * (1 + kepReferenceWeightedSecondNorm theta eps layer) *
              Real.exp (-c * eps) := by
  obtain ⟨tn, en, htn, hen, hnegative⟩ := kepReference_inserted_stopped_negative_budget
  obtain ⟨ec, hec, hcone⟩ := kepReference_cone_second_transfer
  obtain ⟨ti, ei, hti, hei, hmeasures⟩ := kepReference_insertion_measure_budgets
  refine ⟨min tn ti, max en (max ec ei), lt_min htn hti, hen.trans (le_max_left _ _), ?_⟩
  intro theta ht htcap
  obtain ⟨Kn, c, u0, hKn, hc, hu0, hucap, hnb⟩ := hnegative theta ht (htcap.trans (min_le_left _ _))
  obtain ⟨_Ki, _, hmb⟩ := hmeasures theta ht (htcap.trans (min_le_right _ _))
  refine ⟨2 * Kn, c, u0, by positivity, hc, hu0, hucap, ?_⟩
  intro eps he heps layer hlayer k hn18 hnMax u hu huMax phi phi' phi'' hdphi hddphi hcphi a b ha hsupp B hB hphiB
  let n := k + 1
  let f := (kepReferenceDensity heps hlayer).density
  let S := fun x : Fin n → ℝ => ∑ t, x t
  let E := kepFiniteStoppedEvent eps n
  let A := kepFinitePositive n ∩ E
  let T := A.indicator (fun x => phi (S x) / (S x) ^ 2)
  let J := kepReferenceWeightedSecondNorm theta eps layer
  let Q := B * Kn * (n + 1 : ℝ) * (1 + J) / (n : ℝ) ^ 2 * Real.exp (-c * eps)
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps layer
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hE : MeasurableSet E := measurableSet_kepFiniteStoppedEvent eps n
  have hA : MeasurableSet A := (measurableSet_kepFinitePositive n).inter hE
  have hS : Measurable S := Finset.measurable_sum univ (fun t _ => measurable_pi_apply t)
  have hphim : Measurable phi :=
    (continuous_iff_continuousAt.mpr fun t => (hdphi t).continuousAt).measurable
  have hpattern (r : Fin n → ℕ) (hr : (∑ t, r t) ≤ 2) :
      Integrable (fun x => T x * kepMellinPatternProduct f r x) volume ∧
        |∫ x, T x * kepMellinPatternProduct f r x| ≤ Q := by
    have hmu (t : Fin n) := hmb eps ((le_max_right _ _).trans ((le_max_right _ _).trans he))
      heps layer hlayer (r t) ((kepInsertionPattern_bounds hr).1 t)
    have : ∀ t : Fin n, IsFiniteMeasure (kepAbsDensityMeasure ((mellinOp^[r t]) f)) := fun t => (hmu t).1
    have hnMax' : (n : ℝ) ≤ 17 * eps := by simpa only [n, Nat.cast_add, Nat.cast_one] using hnMax
    have hn := hnb eps ((le_max_left _ _).trans he) heps layer hlayer n hn18 hnMax' r hr u hu huMax
    let G := fun x : Fin n → ℝ => ((S x) ^ 2)⁻¹ * Real.exp (u * S x)
    have hG : Measurable G := (hS.pow_const 2).inv.mul ((hS.const_mul u).exp)
    have hGA : Integrable (A.indicator G)
        (Measure.pi (fun t => kepReferenceInsertionMeasure heps hlayer (r t))) := by
      have hh := hn.1.indicator hA
      have heq : A.indicator (E.indicator G) = A.indicator G := by
        funext x
        by_cases hx : x ∈ A
        · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx.2]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx]
      rw [heq] at hh
      exact hh
    have hmass : (∫ x in A, G x ∂Measure.pi (fun t => kepReferenceInsertionMeasure heps hlayer (r t))) ≤
        Kn * (n + 1 : ℝ) * (1 + J) / (n : ℝ) ^ 2 * Real.exp (-c * eps) := by
      rw [← integral_indicator hA]
      have hnB := hn.2
      rw [← integral_indicator hE] at hnB
      apply (integral_mono hGA hn.1 (fun x => ?_)).trans hnB
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx, indicator_of_mem hx.2]
      · rw [indicator_of_notMem hx]
        exact indicator_nonneg (fun _ _ => by dsimp [G]; positivity) x
    have hh := kep_mellin_pattern_test_bound (psi := fun x => phi (S x))
      (kepReferenceDensity heps hlayer).measurable r hS hA (hphim.comp hS) hB
      (fun x hx => hphiB _ (kepFinitePositive_sum_pos (by omega) hx.1).le) hGA
    have heq (x : Fin n → ℝ) : T x * kepMellinPatternProduct f r x =
        A.indicator (fun x => phi (S x) / (S x) ^ 2 * kepMellinPatternProduct f r x) x := by
      by_cases hx : x ∈ A
      · simp only [T, indicator_of_mem hx]
      · simp only [T, indicator_of_notMem hx, zero_mul]
    refine ⟨?_, ?_⟩
    · simp_rw [heq]
      exact hh.1
    · simp_rw [heq]
      rw [integral_indicator hA]
      exact hh.2.trans ((mul_le_mul_of_nonneg_left hmass hB).trans_eq (by dsimp [Q]; ring))
  have hbudget : ∀ V : (Fin n → ℝ) → ℝ, (V = T ∨ V = 0 ∨ V = 0) →
      ∀ r : Fin n → ℕ, (∑ t, r t) ≤ 2 →
        Integrable (fun x => V x * kepMellinPatternProduct f r x) volume ∧
          |∫ x, V x * kepMellinPatternProduct f r x| ≤ Q := by
    intro V hV r hr
    rcases hV with hV | hV | hV
    · subst V; exact hpattern r hr
    · subst V; simpa using (show Integrable (fun _ : Fin n → ℝ => (0 : ℝ)) volume ∧ (0 : ℝ) ≤ Q from ⟨integrable_zero _ _ _, hQ⟩)
    · subst V; simpa using (show Integrable (fun _ : Fin n → ℝ => (0 : ℝ)) volume ∧ (0 : ℝ) ≤ Q from ⟨integrable_zero _ _ _, hQ⟩)
  have hfields := kep_weighted_mellin_fields_test_budget hQ hbudget
  simp only [Pi.zero_apply, zero_mul, add_zero] at hfields
  have hc := hcone eps ((le_max_left _ _).trans ((le_max_right _ _).trans he)) heps layer hlayer k A hA
    (fun x cc hcc => by
      change cc • x ∈ kepFinitePositive n ∧ cc • x ∈ E ↔ x ∈ kepFinitePositive n ∧ x ∈ E
      rw [kepFinitePositive_smul n x hcc, kepFiniteStoppedEvent_smul eps n hcc.ne' x])
    (fun _x hx => kepFinitePositive_sum_pos (by omega) hx.1)
    phi phi' phi'' hdphi hddphi hcphi a b ha hsupp
  have hid : (∫ g in {g : ℕ → ℝ | gapSegLen eps g ≤ ((k + 1 : ℕ) : ℕ∞)},
      phi'' (gapKeys g (k + 1)) ∂iidLaw (kepReferenceLaw eps layer)) =
      ∫ x in A, phi'' (S x) ∂Measure.pi (fun _ : Fin n => (kepReferenceLaw eps layer : Measure ℝ)) := by
    rw [kep_iidLaw_stopped_prefix_integral _ eps n hcphi.measurable,
      ← integral_indicator hE, ← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [kep_ae_finite_positive (kepReferenceLaw_Iic_zero heps hlayer) n] with x hx
    by_cases hxE : x ∈ E
    · rw [indicator_of_mem hxE, indicator_of_mem (show x ∈ A from ⟨hx, hxE⟩)]
    · rw [indicator_of_notMem hxE, indicator_of_notMem (show x ∉ A from fun h => hxE h.2)]
  have heq (x : Fin n → ℝ) : T x *
      (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x) =
      A.indicator (fun x => phi (S x) / (S x) ^ 2 *
        (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x)) x := by
    by_cases hx : x ∈ A
    · simp only [T, indicator_of_mem hx]
    · simp only [T, indicator_of_notMem hx, zero_mul]
  rw [hid, hc, ← integral_indicator hA]
  have hb := hfields.2
  simp_rw [heq] at hb
  apply hb.trans
  have hnR : (18 : ℝ) ≤ n := by exact_mod_cast hn18
  have hpoly : (n : ℝ) ^ 2 + 5 * n + 6 ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
  apply (mul_le_mul_of_nonneg_right hpoly hQ).trans_eq
  dsimp only [Q, J, n]
  push_cast
  field_simp
  ring

end

end PGM
