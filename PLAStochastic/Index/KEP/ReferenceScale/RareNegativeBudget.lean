import PLAStochastic.Index.KEP.ReferenceScale.InsertedDeviationBounds
import PLAStochastic.Index.KEP.ReferenceScale.InsertionNegativeBudget
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual negative second moments on proportion deviation events

Cauchy--Schwarz combines the actual fourth negative moment with the inserted
Chernoff estimate. All insertion costs remain linear in the original weighted
second norm. The bound applies to every measurable subset of the deviation
union, so it also pays the nonzero radial cutoff derivatives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

theorem kep_integrable_of_nonnegative_lintegral_bound {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {f : alpha → ℝ} (hm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    {A : ℝ} (hA : 0 ≤ A) (hb : (∫⁻ x, ENNReal.ofReal (f x) ∂mu) ≤ ENNReal.ofReal A) :
    Integrable f mu ∧ (∫ x, f x ∂mu) ≤ A := by
  have ha : 0 ≤ᵐ[mu] f := ae_of_all _ hf
  have hfin : (∫⁻ x, ENNReal.ofReal (f x) ∂mu) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable ha).mp hfin, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae ha hm.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal hA] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

theorem kep_integral_mul_le_sqrt_budget {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {f g : alpha → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    (hfi : Integrable (fun x => f x ^ 2) mu) (hgi : Integrable (fun x => g x ^ 2) mu)
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hfA : (∫ x, f x ^ 2 ∂mu) ≤ A) (hgB : (∫ x, g x ^ 2 ∂mu) ≤ B) :
    (∫ x, f x * g x ∂mu) ≤ Real.sqrt (A * B) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hflp : MemLp f 2 mu := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hfi
  have hglp : MemLp g 2 mu := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hgi
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ hfn) (ae_of_all _ hgn)
    (by simpa using hflp) (by simpa using hglp)
  simp only [Real.rpow_ofNat, ← Real.sqrt_eq_rpow] at hh
  apply hh.trans
  rw [Real.sqrt_mul hA]
  exact mul_le_mul (Real.sqrt_le_sqrt hfA) (Real.sqrt_le_sqrt hgB)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem kep_sqrt_negative_chernoff_budget {A B J c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hJ : 0 ≤ J) {n : ℕ} (hn : 0 < n) :
    Real.sqrt ((A * (1 + J) / (n : ℝ) ^ 4) *
      (B * (1 + J) * Real.exp (-c * n))) =
        Real.sqrt (A * B) * (1 + J) / (n : ℝ) ^ 2 * Real.exp (-(c / 2) * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show (A * (1 + J) / (n : ℝ) ^ 4) * (B * (1 + J) * Real.exp (-c * n)) =
      (A * B) * ((1 + J) ^ 2 / ((n : ℝ) ^ 2) ^ 2) * Real.exp (-c * n) by ring]
  rw [Real.sqrt_mul (by positivity : 0 ≤ A * B * ((1 + J) ^ 2 / ((n : ℝ) ^ 2) ^ 2)),
    Real.sqrt_mul (mul_nonneg hA hB), Real.sqrt_div (by positivity),
    Real.sqrt_sq (by positivity : 0 ≤ 1 + J), Real.sqrt_sq (sq_nonneg (n : ℝ)),
    ← Real.exp_half]
  rw [show -c * (n : ℝ) / 2 = -(c / 2) * n by ring]
  ring

theorem kepReference_inserted_rare_negative_budget :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c u0 : ℝ,
        0 < K ∧ 0 < c ∧ 0 < u0 ∧ u0 ≤ theta / 8 ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, 18 ≤ n → ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
            ∀ u : ℝ, 0 ≤ u → u ≤ u0 → ∀ E : Set (Fin n → ℝ), MeasurableSet E →
              E ⊆ {x | 7 * n / 6 ≤ ∑ i, x i} ∪ {x | (∑ i, x i) ≤ 3 * n / 4} →
            let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
            (∫ x in E, ((∑ i, x i) ^ 2)⁻¹ * Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
              K * (1 + kepReferenceWeightedSecondNorm theta eps j) / (n : ℝ) ^ 2 *
                Real.exp (-c * n) := by
  obtain ⟨td, ed, htd, hed, hd⟩ := kepReference_inserted_proportion_deviations
  obtain ⟨tn, en, htn, hen, hn⟩ := kepReference_insertion_fourth_negative_budget
  obtain ⟨ti, ei, hti, hei, hi⟩ := kepReference_insertion_measure_budgets
  refine ⟨min td (min tn ti), max ed (max en ei), lt_min htd (lt_min htn hti),
    hed.trans (le_max_left _ _), ?_⟩
  intro theta ht htheta
  obtain ⟨Kd, cd, ud, hKd, hcd, hud, hudcap, hdb⟩ := hd theta ht (htheta.trans (min_le_left _ _))
  obtain ⟨Kn, hKn, hnb⟩ := hn theta ht ((htheta.trans (min_le_right _ _)).trans (min_le_left _ _))
  obtain ⟨Ki, _, hib⟩ := hi theta ht ((htheta.trans (min_le_right _ _)).trans (min_le_right _ _))
  refine ⟨Real.sqrt (Kn * Kd), cd / 2, ud / 2, Real.sqrt_pos.mpr (mul_pos hKn hKd),
    by positivity, by positivity, by linarith, ?_⟩
  intro eps he heps j hj n hn18 r hr u hu0 hu E hE hEsub
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let S := fun x : Fin n → ℝ => ∑ i, x i
  let J := kepReferenceWeightedSecondNorm theta eps j
  let U := {x | 7 * n / 6 ≤ S x}
  let L := {x | S x ≤ 3 * n / 4}
  let f := fun x : Fin n → ℝ => ((S x) ^ 2)⁻¹
  let g := E.indicator (fun x => Real.exp (u * S x))
  have hS : Measurable S := Finset.measurable_sum univ (fun i _ => measurable_pi_apply i)
  have hf : Measurable f := hS.pow_const 2 |>.inv
  have hg : Measurable g := (hS.const_mul u).exp.indicator hE
  have hfn (x) : 0 ≤ f x := inv_nonneg.mpr (sq_nonneg _)
  have hgn (x) : 0 ≤ g x := indicator_nonneg (fun x _ => (Real.exp_pos _).le) x
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hmu (i : Fin n) := hib eps ((le_max_right _ _).trans ((le_max_right _ _).trans he))
    heps j hj (r i) ((kepInsertionPattern_bounds hr).1 i)
  have : ∀ i, IsFiniteMeasure (mu i) := fun i => (hmu i).1
  have hsq (x) : f x ^ 2 = (S x) ^ (-4 : ℝ) := by
    dsimp [f]
    rw [Real.rpow_neg_ofNat]
    simp only [zpow_neg, zpow_ofNat, inv_pow]
    congr 1
    ring
  have hbneg := hnb eps ((le_max_left _ _).trans ((le_max_right _ _).trans he)) heps j hj n hn18 r hr
  have hneg : Integrable (fun x => f x ^ 2) (Measure.pi mu) ∧
      (∫ x, f x ^ 2 ∂Measure.pi mu) ≤ Kn * (1 + J) / (n : ℝ) ^ 4 := by
    apply kep_integrable_of_nonnegative_lintegral_bound (hf.pow_const 2) (fun _ => sq_nonneg _)
      (by positivity)
    simpa only [hsq] using hbneg
  have hexp : Integrable (fun x => Real.exp ((2 * u) * S x)) (Measure.pi mu) := by
    apply kep_pi_exp_sum_integrable
    exact fun i => ((hmu i).2.2 (2 * u) (by linarith)).1
  have hg2 (x) : g x ^ 2 = E.indicator (fun x => Real.exp ((2 * u) * S x)) x := by
    by_cases hx : x ∈ E
    · simp only [g, indicator_of_mem hx, sq, ← Real.exp_add]
      congr 1
      ring
    · simp only [g, indicator_of_notMem hx, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  have hgi : Integrable (fun x => g x ^ 2) (Measure.pi mu) := by
    simpa only [hg2] using hexp.indicator hE
  have hU : MeasurableSet U := measurableSet_le measurable_const hS
  have hL : MeasurableSet L := measurableSet_le hS measurable_const
  have hpoint (x) : E.indicator (fun x => Real.exp ((2 * u) * S x)) x ≤
      U.indicator (fun x => Real.exp ((2 * u) * S x)) x +
        L.indicator (fun x => Real.exp ((2 * u) * S x)) x := by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      rcases hEsub hx with hxU | hxL
      · rw [indicator_of_mem hxU]
        exact le_add_of_nonneg_right (indicator_nonneg (fun x _ => (Real.exp_pos _).le) x)
      · rw [indicator_of_mem hxL]
        exact le_add_of_nonneg_left (indicator_nonneg (fun x _ => (Real.exp_pos _).le) x)
    · rw [indicator_of_notMem hx]
      exact add_nonneg (indicator_nonneg (fun x _ => (Real.exp_pos _).le) x)
        (indicator_nonneg (fun x _ => (Real.exp_pos _).le) x)
  have hgB : (∫ x, g x ^ 2 ∂Measure.pi mu) ≤ Kd * (1 + J) * Real.exp (-cd * n) := by
    have hh := integral_mono (hexp.indicator hE) ((hexp.indicator hU).add (hexp.indicator hL)) hpoint
    simp only [Pi.add_apply] at hh
    rw [integral_add (hexp.indicator hU) (hexp.indicator hL), integral_indicator hU,
      integral_indicator hL] at hh
    simp only [hg2]
    exact hh.trans (hdb eps ((le_max_left _ _).trans he) heps j hj n (by omega) r hr (2 * u)
      (by positivity) (by linarith))
  have hcs := kep_integral_mul_le_sqrt_budget hf hg hfn hgn hneg.1 hgi
    (by positivity) (by positivity) hneg.2 hgB
  rw [kep_sqrt_negative_chernoff_budget hKn.le hKd.le hJ (by omega)] at hcs
  have hid : (∫ x, f x * g x ∂Measure.pi mu) =
      ∫ x in E, ((S x) ^ 2)⁻¹ * Real.exp (u * S x) ∂Measure.pi mu := by
    rw [← integral_indicator hE]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ E
      · simp only [g, f, indicator_of_mem hx]
      · simp only [g, indicator_of_notMem hx, mul_zero]
  exact hid.symm ▸ hcs

end

end PGM
