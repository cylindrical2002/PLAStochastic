import PLAStochastic.Index.KEP.ReferenceScale.InsertionVectorMomentBudget

/-!
# Weighted partial-sum Chernoff bounds and the exact clean-coordinate phase

These estimates keep the original complete product law. A partial sum receives
its own Chernoff parameter while every coordinate retains the output weight.
Deleting at most two clean moment factors loses at most twice that parameter.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Finset Set

theorem kep_pi_weighted_linear_event_bound {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    (u b : ℝ) (t : Fin n → ℝ)
    (hi : ∀ i, Integrable (fun x => Real.exp (t i * x)) (mu i))
    (hEbound : ∀ x ∈ E, u * (∑ i, x i) ≤ b + ∑ i, t i * x i) :
    (∫ x in E, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
      Real.exp b * ∏ i, ∫ x, Real.exp (t i * x) ∂mu i := by
  have hS : Measurable (fun x : Fin n → ℝ => ∑ i, x i) :=
    Finset.measurable_sum univ (fun i _ => measurable_pi_apply i)
  have hmeas := (hS.const_mul u).exp.indicator hE
  have hdom := (kep_pi_exp_linear_integrable mu hi).const_mul (Real.exp b)
  have hpt (x : Fin n → ℝ) : E.indicator (fun x => Real.exp (u * ∑ i, x i)) x ≤
      Real.exp b * Real.exp (∑ i, t i * x i) := by
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
  rw [← integral_indicator hE]
  exact (integral_mono hiE hdom hpt).trans_eq (by
    rw [integral_const_mul, kep_pi_exp_linear_integral])

theorem kep_clean_vector_phase_bound {n : ℕ} (H : Finset (Fin n)) (hH : H.card ≤ 2)
    {C tau u : ℝ} (hC : 0 ≤ C) (htau : 0 ≤ tau) (_hu : 0 ≤ u)
    (t : Fin n → ℝ) (hmin : ∀ i, -tau ≤ t i) (habs : ∀ i, |t i| ≤ u + tau) :
    (∑ i ∈ Finset.univ \ H, (t i + C * (t i) ^ 2)) ≤
      (∑ i, t i) + 2 * tau + C * n * (u + tau) ^ 2 := by
  have hsplit : (∑ i ∈ Finset.univ \ H, t i) + ∑ i ∈ H, t i = ∑ i, t i :=
    sum_sdiff (f := t) (subset_univ H)
  have hsumH : -(2 * tau) ≤ ∑ i ∈ H, t i := by
    have hh := sum_le_sum (s := H) (fun i _ => hmin i)
    simp only [sum_const, nsmul_eq_mul] at hh
    have hc : (H.card : ℝ) ≤ 2 := by exact_mod_cast hH
    nlinarith [mul_le_mul_of_nonneg_right hc htau]
  have hsq (i) : (t i) ^ 2 ≤ (u + tau) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (t i)) (habs i) 2
  have hsumC : (∑ i ∈ Finset.univ \ H, C * (t i) ^ 2) ≤ C * n * (u + tau) ^ 2 := by
    have hh := sum_le_sum (s := Finset.univ \ H) (fun i _ => mul_le_mul_of_nonneg_left (hsq i) hC)
    simp only [sum_const, nsmul_eq_mul] at hh
    have hc : ((Finset.univ \ H).card : ℝ) ≤ n := by
      have hcNat : (Finset.univ \ H).card ≤ n := by
        simpa only [card_univ, Fintype.card_fin] using
          (card_le_card sdiff_subset : (Finset.univ \ H).card ≤ (Finset.univ : Finset (Fin n)).card)
      exact_mod_cast hcNat
    have hmul := mul_le_mul_of_nonneg_right hc (mul_nonneg hC (sq_nonneg (u + tau)))
    exact hh.trans (by nlinarith only [hmul])
  rw [sum_add_distrib]
  linarith

theorem kep_short_chernoff_weight_cost {eps C tau u : ℝ} {n : ℕ}
    (heps : 0 ≤ eps) (hC : 0 ≤ C) (htau : 0 < tau) (hCt : C * tau ≤ 1 / 1024)
    (hu0 : 0 ≤ u) (hu : u ≤ tau / 256) (hn : (n : ℝ) ≤ 17 * eps) :
    u * n + C * n * (u + tau) ^ 2 ≤ tau * eps / 4 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsq : (u + tau) ^ 2 ≤ 4 * tau ^ 2 := by nlinarith
  have hcurv := mul_le_mul_of_nonneg_right hCt htau.le
  have hcu := mul_le_mul_of_nonneg_left hsq (mul_nonneg hC hn0)
  have hcn := mul_le_mul_of_nonneg_left hcurv (by positivity : 0 ≤ 4 * (n : ℝ))
  have hun := mul_le_mul_of_nonneg_right hu hn0
  have hne := mul_le_mul_of_nonneg_left hn htau.le
  nlinarith only [hcu, hcn, hun, hne, mul_nonneg htau.le heps]

end

end PGM
