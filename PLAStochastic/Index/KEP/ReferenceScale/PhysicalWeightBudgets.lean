import PLAStochastic.Index.KEP.ReferenceScale.PhysicalOutputTests
import PLAStochastic.Index.KEP.ReferenceScale.ActualRecurrenceCriterion

/-!
# Paying the actual output weight and input-norm comparison

The physical output weight theta/C is on the genuine epsilon-squared stopping
scale. The uniform mean bracket pays both its fixed-scale cap and its ordinary
small-weight cap after theta is fixed. The unweighted second norm is bounded
by the same actual weighted second norm.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_second_density_zero_of_nonpos {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) (j : ℕ) {t : ℝ} (ht : t ≤ 0) :
    gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) t = 0 := by
  have hm := kepReferenceSpan_pos heps j
  have hx : kepReferenceSpan eps j * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm.le ht
  unfold gammaScaledSecond gammaMixtureSecond
  rw [gammaMixtureDensity_succ_of_nonpos _ 0 hx,
    gammaMixtureDensity_succ_of_nonpos _ 1 hx,
    gammaMixtureDensity_succ_of_nonpos _ 2 hx]
  ring

theorem kepReference_second_norm_le_weighted {eps theta : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) (htheta : 0 ≤ theta) (j : ℕ)
    (hi : Integrable (fun t => Real.exp (theta * t) *
      gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) t)) :
    kepReferenceSecondNorm eps j ≤ kepReferenceWeightedSecondNorm theta eps j := by
  have hia : Integrable (fun t => Real.exp (theta * t) *
      |gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) t|) := by
    simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using hi.abs
  apply integral_mono_of_nonneg (ae_of_all _ fun t => abs_nonneg _) hia
  exact ae_of_all _ fun t => by
    change |gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) t| ≤
      Real.exp (theta * t) * |gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) t|
    by_cases ht : 0 ≤ t
    · exact le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_exp (mul_nonneg htheta ht))
    · rw [kepReference_second_density_zero_of_nonpos heps j (le_of_not_ge ht), abs_zero, mul_zero]

theorem kepReference_output_weight_admissible {theta V u0 : ℝ}
    (htheta : 0 ≤ theta) (_hV : 0 < V) (hu0 : 0 < u0)
    (hcap : theta ≤ V / kepGraphMeanBracket) :
    ∃ E : ℝ, kepReferenceClassicalThreshold ≤ E ∧
      ∀ eps, E ≤ eps → ∀ j : ℕ,
        1 ≤ lawC eps (kepReferenceLaw eps j) ∧
        0 ≤ theta / lawC eps (kepReferenceLaw eps j) ∧
        theta / lawC eps (kepReferenceLaw eps j) ≤ V / eps ^ 2 ∧
        theta / lawC eps (kepReferenceLaw eps j) ≤ u0 ∧
        theta / lawC eps (kepReferenceLaw eps j) ≤ theta := by
  let cb := kepGraphMeanBracket
  have hcb1 : 1 ≤ cb := kepGraphMeanBracket_ge_one
  have hcb : 0 < cb := by linarith
  let E := max kepReferenceClassicalThreshold (max cb (theta * cb / u0))
  refine ⟨E, le_max_left _ _, ?_⟩
  intro eps he j
  have heps : kepReferenceClassicalThreshold ≤ eps := (le_max_left _ _).trans he
  have hecb : cb ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans he)
  have heu : theta * cb / u0 ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans he)
  have he1 : 1 ≤ eps := hcb1.trans hecb
  have hepos : 0 < eps := by linarith
  have hesq : 0 < eps ^ 2 := by positivity
  have hbr := kepReference_lawC_bracket heps j
  have hecb2 : cb ≤ eps ^ 2 := hecb.trans (by nlinarith)
  have hC1 : 1 ≤ lawC eps (kepReferenceLaw eps j) :=
    ((le_div_iff₀ hcb).mpr (by simpa using hecb2)).trans hbr.1
  have hCp : 0 < lawC eps (kepReferenceLaw eps j) := by linarith
  have hbase : theta / lawC eps (kepReferenceLaw eps j) ≤ theta * cb / eps ^ 2 := by
    calc
      _ ≤ theta / (eps ^ 2 / cb) := div_le_div_of_nonneg_left htheta (by positivity) hbr.1
      _ = _ := by field_simp
  refine ⟨hC1, by positivity, ?_, ?_, div_le_self htheta hC1⟩
  · apply hbase.trans
    apply div_le_div_of_nonneg_right _ hesq.le
    exact (le_div_iff₀ hcb).mp hcap
  · apply hbase.trans
    apply (div_le_iff₀ hesq).mpr
    have hmul := (div_le_iff₀ hu0).mp heu
    have hepssq : eps ≤ eps ^ 2 := by nlinarith
    exact hmul.trans ((mul_le_mul_of_nonneg_right hepssq hu0.le).trans_eq (mul_comm _ _))

end

end PGM
