import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Weighted Chernoff bounds with arbitrary finite coordinate insertions

The product measures need not be probabilities or share a marginal. The
moment factorization pays every inserted coordinate separately; clean
coordinates retain their original common moment bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Set Finset

theorem kep_pi_exp_sum_integral {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] (u : ℝ) :
    (∫ x, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) =
      ∏ i, ∫ y, Real.exp (u * y) ∂mu i := by
  simp_rw [Finset.mul_sum, Real.exp_sum]
  exact integral_fintype_prod_eq_prod (fun (_ : Fin n) (y : ℝ) => Real.exp (u * y))

theorem kep_pi_exp_sum_integrable {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] {u : ℝ}
    (hi : ∀ i, Integrable (fun y => Real.exp (u * y)) (mu i)) :
    Integrable (fun x => Real.exp (u * ∑ i, x i)) (Measure.pi mu) := by
  simp_rw [Finset.mul_sum, Real.exp_sum]
  exact Integrable.fintype_prod hi

theorem kep_pi_weighted_event_bound {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    (u v b : ℝ) (hi : ∀ i, Integrable (fun y => Real.exp (v * y)) (mu i))
    (hEbound : ∀ x ∈ E, u * (∑ i, x i) ≤ b + v * (∑ i, x i)) :
    IntegrableOn (fun x => Real.exp (u * ∑ i, x i)) E (Measure.pi mu) ∧
      (∫ x in E, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
        Real.exp b * ∏ i, ∫ y, Real.exp (v * y) ∂mu i := by
  have hS : Measurable (fun x : Fin n → ℝ => ∑ i, x i) :=
    Finset.measurable_sum univ (fun i _ => measurable_pi_apply i)
  have hmeas := (hS.const_mul u).exp.indicator hE
  have hdom := (kep_pi_exp_sum_integrable mu hi).const_mul (Real.exp b)
  have hpt (x : Fin n → ℝ) :
      E.indicator (fun x => Real.exp (u * ∑ i, x i)) x ≤
        Real.exp b * Real.exp (v * ∑ i, x i) := by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (hEbound x hx)
    · rw [indicator_of_notMem hx]
      positivity
  have hnonneg (x : Fin n → ℝ) : 0 ≤ E.indicator (fun x => Real.exp (u * ∑ i, x i)) x :=
    indicator_nonneg (fun x _ => (Real.exp_pos _).le) x
  have hiE : Integrable (E.indicator (fun x => Real.exp (u * ∑ i, x i))) (Measure.pi mu) := by
    refine hdom.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    exact hpt x
  refine ⟨(integrable_indicator_iff hE).mp hiE, ?_⟩
  rw [← integral_indicator hE]
  calc
    _ ≤ ∫ x, Real.exp b * Real.exp (v * ∑ i, x i) ∂Measure.pi mu :=
      integral_mono hiE hdom hpt
    _ = _ := by rw [integral_const_mul, kep_pi_exp_sum_integral]

theorem kep_pi_weighted_upper_tail {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] (u a : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hi : ∀ i, Integrable (fun y => Real.exp ((u + t) * y)) (mu i)) :
    (∫ x in {x | a ≤ ∑ i, x i}, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
      Real.exp (-t * a) * ∏ i, ∫ y, Real.exp ((u + t) * y) ∂mu i := by
  have hS : Measurable (fun x : Fin n → ℝ => ∑ i, x i) :=
    Finset.measurable_sum univ (fun i _ => measurable_pi_apply i)
  exact (kep_pi_weighted_event_bound mu (measurableSet_le measurable_const hS)
    u (u + t) (-t * a) hi (fun x hx => by dsimp at hx; nlinarith)).2

theorem kep_pi_weighted_lower_tail {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] (u a : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hi : ∀ i, Integrable (fun y => Real.exp ((u - t) * y)) (mu i)) :
    (∫ x in {x | (∑ i, x i) ≤ a}, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
      Real.exp (t * a) * ∏ i, ∫ y, Real.exp ((u - t) * y) ∂mu i := by
  have hS : Measurable (fun x : Fin n → ℝ => ∑ i, x i) :=
    Finset.measurable_sum univ (fun i _ => measurable_pi_apply i)
  exact (kep_pi_weighted_event_bound mu (measurableSet_le hS measurable_const)
    u (u - t) (t * a) hi (fun x hx => by dsimp at hx; nlinarith)).2

theorem kep_pi_exp_sum_inserted_le {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] (H : Finset (Fin n)) (u M : ℝ) (A : Fin n → ℝ)
    (hb : ∀ i, (∫ y, Real.exp (u * y) ∂mu i) ≤ if i ∈ H then A i else M) :
    (∫ x, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
      (∏ i ∈ H, A i) * M ^ (n - H.card) := by
  classical
  rw [kep_pi_exp_sum_integral]
  have hp : (∏ i, ∫ y, Real.exp (u * y) ∂mu i) ≤
      ∏ i, (if i ∈ H then A i else M) :=
    prod_le_prod (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le)) (fun i _ => hb i)
  have hprod : (∏ i, (if i ∈ H then A i else M)) = (∏ i ∈ H, A i) * M ^ (n - H.card) := by
    rw [prod_ite, filter_mem_eq_inter, ← sdiff_eq_filter, Finset.univ_inter, prod_const,
      card_sdiff, Finset.inter_univ, card_univ, Fintype.card_fin]
  exact hp.trans_eq hprod

end

end PGM
