import PLAStochastic.Index.KEP.ReferenceScale.MellinDerivativeBudget

/-!
# Actual positive finite measures for the Mellin insertions

Every Chernoff parameter below the fixed insertion exponent is paid by the
proved weighted insertion norm. The first and second insertions are finite
positive measures supported on the positive axis; the zeroth is exactly the
unchanged reference probability law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

def kepAbsDensityMeasure (F : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (|F x|))

theorem kepAbsDensityMeasure_positive {F : ℝ → ℝ}
    (hzero : ∀ x, x ≤ 0 → F x = 0) : kepAbsDensityMeasure F (Iic 0) = 0 := by
  rw [kepAbsDensityMeasure, withDensity_apply _ measurableSet_Iic]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
  simp only [hzero x hx, abs_zero, ENNReal.ofReal_zero, Pi.zero_apply]

theorem kepAbsDensityMeasure_exp_budget {F : ℝ → ℝ} (hF : Measurable F)
    (hzero : ∀ x, x ≤ 0 → F x = 0) {alpha u : ℝ} (hu : u ≤ alpha)
    (hi : Integrable (fun x => Real.exp (alpha * x) * F x) volume) :
    Integrable (fun x => Real.exp (u * x)) (kepAbsDensityMeasure F) ∧
      (∫ x, Real.exp (u * x) ∂kepAbsDensityMeasure F) ≤
        ∫ x, Real.exp (alpha * x) * |F x| := by
  have hiabs : Integrable (fun x => Real.exp (alpha * x) * |F x|) volume := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using hi.norm
  have hpt (x : ℝ) : Real.exp (u * x) * |F x| ≤ Real.exp (alpha * x) * |F x| := by
    by_cases hx : x ≤ 0
    · rw [hzero x hx, abs_zero, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hu (not_le.mp hx).le)) (abs_nonneg _)
  have hiu : Integrable (fun x => Real.exp (u * x) * |F x|) volume := by
    refine hiabs.mono' (((measurable_const.mul measurable_id).exp).mul hF.abs).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt x
  have hmeas : Measurable (fun x => ENNReal.ofReal (|F x|)) := hF.abs.ennreal_ofReal
  have hfin : ∀ᵐ x ∂volume, ENNReal.ofReal (|F x|) < ∞ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hiLaw : Integrable (fun x => Real.exp (u * x)) (kepAbsDensityMeasure F) := by
    apply (integrable_withDensity_iff_integrable_smul' hmeas hfin).mpr
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul, mul_comm] using hiu
  refine ⟨hiLaw, ?_⟩
  rw [kepAbsDensityMeasure, integral_withDensity_eq_integral_toReal_smul hmeas hfin]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]
  simpa only [mul_comm] using integral_mono hiu hiabs hpt

theorem kepAbsDensityMeasure_finite {F : ℝ → ℝ} (hF : Measurable F)
    (hzero : ∀ x, x ≤ 0 → F x = 0) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hi : Integrable (fun x => Real.exp (alpha * x) * F x) volume) :
    IsFiniteMeasure (kepAbsDensityMeasure F) := by
  have h0 := (kepAbsDensityMeasure_exp_budget hF hzero halpha hi).1
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (kepAbsDensityMeasure F) := by
    simpa only [zero_mul, Real.exp_zero] using h0
  exact (integrable_const_iff_isFiniteMeasure one_ne_zero).mp hconst

def kepMellinInsertionCost (r : ℕ) (J : ℝ) : ℝ :=
  if r = 0 then 1 else if r = 1 then Real.sqrt (1 + J) else 1 + J

def kepReferenceInsertionMeasure {eps : ℝ} (heps : kepReferenceClassicalThreshold ≤ eps)
    {j : ℕ} (hj : 1 ≤ j) (r : ℕ) : Measure ℝ :=
  kepAbsDensityMeasure ((mellinOp^[r]) (kepReferenceDensity heps hj).density)

theorem kepReferenceInsertionMeasure_zero {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j) :
    kepReferenceInsertionMeasure heps hj 0 = (kepReferenceLaw eps j : Measure ℝ) := by
  rw [← kepReferenceDensity_toMeasure heps hj]
  unfold kepReferenceInsertionMeasure kepAbsDensityMeasure
  simp only [Function.iterate_zero_apply, abs_of_nonneg ((kepReferenceDensity heps hj).nonneg _)]
  rfl

theorem kepReference_insertion_measure_budgets :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K : ℝ, 0 < K ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ r : ℕ, r ≤ 2 →
            let mu := kepReferenceInsertionMeasure heps hj r
            IsFiniteMeasure mu ∧ mu (Iic 0) = 0 ∧
              ∀ u : ℝ, u ≤ theta / 4 → Integrable (fun x => Real.exp (u * x)) mu ∧
                (∫ x, Real.exp (u * x) ∂mu) ≤
                  K * kepMellinInsertionCost r (kepReferenceWeightedSecondNorm theta eps j) := by
  obtain ⟨tm, e0, htm, he0, hbudget⟩ := kepReference_mellin_insertion_budgets
  refine ⟨tm, e0, htm, he0, ?_⟩
  intro theta ht htheta
  obtain ⟨K, hK, hb⟩ := hbudget theta ht htheta
  refine ⟨K, hK, ?_⟩
  intro eps he heps j hj r hr
  dsimp only
  let f := (kepReferenceDensity heps hj).density
  let J := kepReferenceWeightedSecondNorm theta eps j
  have hm := measurable_mellinOp_iterate (kepReferenceDensity heps hj).measurable r
  have hzero := mellinOp_iterate_eq_zero_of_nonpos (kepReferenceDensity_classical heps hj).1 r
  obtain ⟨h0, h1, h2, hb0, hb1, hb2⟩ := hb eps he heps j hj
  have hiorbit : Integrable (fun x => Real.exp ((theta / 4) * x) * ((mellinOp^[r]) f) x) volume := by
    interval_cases r
    · exact h0
    · exact h1
    · exact h2
  have hborbit : (∫ x, Real.exp ((theta / 4) * x) * |((mellinOp^[r]) f) x|) ≤
      K * kepMellinInsertionCost r J := by
    interval_cases r
    · simpa [kepMellinInsertionCost, f, J] using hb0
    · simpa [kepMellinInsertionCost, f, J] using hb1
    · change (∫ x, Real.exp ((theta / 4) * x) * |mellinOp (mellinOp f) x|) ≤ _
      simpa [kepMellinInsertionCost, f, J] using hb2
  refine ⟨kepAbsDensityMeasure_finite hm hzero (by positivity) hiorbit,
    kepAbsDensityMeasure_positive hzero, ?_⟩
  intro u hu
  obtain ⟨hiu, hbu⟩ := kepAbsDensityMeasure_exp_budget hm hzero hu hiorbit
  exact ⟨hiu, hbu.trans hborbit⟩

end

end PGM
