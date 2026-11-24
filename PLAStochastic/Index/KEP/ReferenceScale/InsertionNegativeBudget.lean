import PLAStochastic.Index.KEP.ReferenceScale.InsertionProductBudget
import PLAStochastic.Index.KEP.ReferenceScale.InsertedNegativeMoments

/-!
# The actual inserted fourth negative moment with its linear norm budget

At most two coordinates are inserted. For at least eighteen total coordinates,
the remaining clean count pays the fourth negative moment. The insertion mass
product costs a single factor `1 + J`, uniformly over every insertion pattern.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

theorem kep_measure_mass_eq_zero_moment (mu : Measure ℝ) [IsFiniteMeasure mu] :
    mu Set.univ = ENNReal.ofReal (∫ x, Real.exp ((0 : ℝ) * x) ∂mu) := by
  simp only [zero_mul, Real.exp_zero, integral_const, smul_eq_mul, mul_one]
  exact (ofReal_measureReal (measure_ne_top mu Set.univ)).symm

theorem kep_clean_fourth_negative_coarsening {n h : ℕ} (hn : 18 ≤ n) (hh : h ≤ 2) :
    (((n - h : ℕ) : ℝ) ^ (-4 : ℝ)) ≤ 16 / (n : ℝ) ^ 4 := by
  have hhn : h ≤ n := by omega
  have hn18 : (18 : ℝ) ≤ n := by exact_mod_cast hn
  have hh2 : (h : ℝ) ≤ 2 := by exact_mod_cast hh
  have hn0 : (0 : ℝ) < n := by linarith
  have hm : (n : ℝ) / 2 ≤ (n - h : ℕ) := by
    rw [Nat.cast_sub hhn]
    linarith
  have hm0 : (0 : ℝ) < (n - h : ℕ) := by linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2) hm 4
  calc
    _ = (((n - h : ℕ) : ℝ) ^ 4)⁻¹ := by rw [Real.rpow_neg hm0.le]; simp only [Real.rpow_ofNat]
    _ ≤ (((n : ℝ) / 2) ^ 4)⁻¹ := inv_anti₀ (by positivity) hpow
    _ = _ := by field_simp; ring

theorem kepReference_insertion_fourth_negative_budget :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K : ℝ, 0 < K ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, 18 ≤ n → ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
            let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
            (∫⁻ x, ENNReal.ofReal ((∑ i, x i) ^ (-4 : ℝ)) ∂Measure.pi mu) ≤
              ENNReal.ofReal (K * (1 + kepReferenceWeightedSecondNorm theta eps j) / (n : ℝ) ^ 4) := by
  obtain ⟨D, en, hD, hen, hnegative⟩ := kepReference_inserted_negative_moments
  obtain ⟨tm, ei, htm, hei, hins⟩ := kepReference_insertion_measure_budgets
  refine ⟨tm, max en ei, htm, hen.trans (le_max_left _ _), ?_⟩
  intro theta ht htheta
  obtain ⟨Ki, _, hi⟩ := hins theta ht htheta
  let K0 := max 1 Ki
  have hK0 : 1 ≤ K0 := le_max_left _ _
  have hKi : Ki ≤ K0 := le_max_right _ _
  refine ⟨16 * K0 ^ 2 * Real.exp (32 * D), by positivity, ?_⟩
  intro eps he heps j hj n hn r hr
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let H := kepInsertedCoordinates r
  let J := kepReferenceWeightedSecondNorm theta eps j
  obtain ⟨hrcoord, hcard, _⟩ := kepInsertionPattern_bounds hr
  have Hmu (i : Fin n) := hi eps ((le_max_right _ _).trans he) heps j hj (r i) (hrcoord i)
  have : ∀ i, IsFiniteMeasure (mu i) := fun i => (Hmu i).1
  have hclean (i : Fin n) (hiH : i ∉ H) : mu i = (kepReferenceLaw eps j : Measure ℝ) := by
    have hr0 : r i = 0 := by
      by_contra hz
      exact hiH (mem_filter.mpr ⟨mem_univ _, hz⟩)
    dsimp [mu]
    rw [hr0, kepReferenceInsertionMeasure_zero]
  have hpos (i : Fin n) : mu i (Set.Iic 0) = 0 := (Hmu i).2.1
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hcost (i : Fin n) : 0 ≤ K0 * kepMellinInsertionCost (r i) J := by
    rw [kepMellinInsertionCost_eq_pow hJ (hrcoord i)]
    positivity
  have hmass (i : Fin n) : mu i Set.univ ≤ ENNReal.ofReal (K0 * kepMellinInsertionCost (r i) J) := by
    rw [kep_measure_mass_eq_zero_moment]
    apply ENNReal.ofReal_le_ofReal
    have hh := ((Hmu i).2.2 0 (by positivity)).2
    apply hh.trans
    apply mul_le_mul_of_nonneg_right hKi
    rw [kepMellinInsertionCost_eq_pow hJ (hrcoord i)]
    positivity
  have hmassprod : (∏ i ∈ H, mu i Set.univ) ≤ ENNReal.ofReal (K0 ^ 2 * (1 + J)) := by
    calc
      _ ≤ ∏ i ∈ H, ENNReal.ofReal (K0 * kepMellinInsertionCost (r i) J) := prod_le_prod' (fun i _ => hmass i)
      _ = ENNReal.ofReal (∏ i ∈ H, K0 * kepMellinInsertionCost (r i) J) :=
        (ENNReal.ofReal_prod_of_nonneg (fun i _ => hcost i)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (kep_insertion_product_cost hr hJ hK0)
  have hHn : H.card < n := by dsimp [H] at *; omega
  have hnreal : (18 : ℝ) ≤ n := by exact_mod_cast hn
  have hcardreal : (H.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  have hnneg : 4 * (4 : ℝ) ≤ (n : ℝ) - H.card := by linarith
  have hneg := hnegative eps ((le_max_left _ _).trans he) heps j hj n mu H hclean hpos 4
    (by norm_num) hHn hnneg
  have hcoarse := kep_clean_fourth_negative_coarsening hn hcard
  calc
    _ ≤ (∏ i ∈ H, mu i Set.univ) *
        ENNReal.ofReal (((n - H.card : ℕ) : ℝ) ^ (-4 : ℝ) * Real.exp (8 * D * 4)) := hneg
    _ ≤ ENNReal.ofReal (K0 ^ 2 * (1 + J)) *
        ENNReal.ofReal ((16 / (n : ℝ) ^ 4) * Real.exp (8 * D * 4)) :=
      mul_le_mul' hmassprod (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoarse (Real.exp_pos _).le))
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), show 8 * D * 4 = 32 * D by ring]
      congr 1
      ring

end

end PGM
