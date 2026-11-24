import PLAStochastic.Index.KEP.ReferenceScale.ProductConeTransfer
import PLAStochastic.Index.KEP.ReferenceScale.MellinInsertionMeasures
import PLAStochastic.ForMathlib.MeasureTheory.Constructions.PiFactor

/-!
# Unconditional product-cone second transfer for the actual reference law

The true reference density supplies classical derivatives and the required
Mellin integrability. Its product is exactly the original iid law; none of the
analytic hypotheses of the general cone transfer remains in the conclusion.
Only the measurable cone and the original compact physical test are inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

theorem kepReference_mellin_insertions_integrable :
    ∃ eps0 : ℝ, kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j,
          Integrable (kepReferenceDensity heps hj).density volume ∧
            Integrable (mellinOp (kepReferenceDensity heps hj).density) volume ∧
            Integrable (mellinOp (mellinOp (kepReferenceDensity heps hj).density)) volume := by
  obtain ⟨tm, e0, htm, he0, hb⟩ := kepReference_mellin_insertion_budgets
  obtain ⟨_K, _, hbudget⟩ := hb (tm / 2) (by positivity) (by linarith)
  refine ⟨e0, he0, ?_⟩
  intro eps he heps j hj
  obtain ⟨_h0, h1, h2, _, _, _⟩ := hbudget eps he heps j hj
  have hz := (kepReferenceDensity_classical heps hj).1
  have hm := (kepReferenceDensity heps hj).measurable
  have hi1 := (kep_weighted_polynomial_budget (measurable_mellinOp hm)
    (mellinOp_eq_zero_of_nonpos hz) (by positivity : (0 : ℝ) < (tm / 2) / 4) 0 h1).1
  have hi2 := (kep_weighted_polynomial_budget (measurable_mellinOp (measurable_mellinOp hm))
    (mellinOp_eq_zero_of_nonpos (mellinOp_eq_zero_of_nonpos hz))
    (by positivity : (0 : ℝ) < (tm / 2) / 4) 0 h2).1
  refine ⟨(kepReferenceDensity heps hj).integrable, ?_, ?_⟩
  · simpa only [zero_mul, Real.exp_zero, pow_zero, mul_one, one_mul] using hi1
  · simpa only [zero_mul, Real.exp_zero, pow_zero, mul_one, one_mul] using hi2

theorem kepReference_iid_integral_eq_product_density {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    (n : ℕ) (F : (Fin n → ℝ) → ℝ) :
    (∫ x, F x ∂Measure.pi (fun _ : Fin n => (kepReferenceLaw eps j : Measure ℝ))) =
      ∫ x, F x * kepProductDensity (kepReferenceDensity heps hj).density x := by
  let p := kepReferenceDensity heps hj
  have he : (kepReferenceLaw eps j : Measure ℝ) =
      volume.withDensity (fun x => ENNReal.ofReal (p.density x)) :=
    (kepReferenceDensity_toMeasure heps hj).symm
  have : ∀ _i : Fin n, IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (p.density x))) := by
    intro i
    rw [← he]
    infer_instance
  rw [he, pi_withDensity_fin volume (fun _ : Fin n => fun x => ENNReal.ofReal (p.density x))
    (fun _ => p.measurable.ennreal_ofReal)]
  have hrho (x : Fin n → ℝ) : (∏ i, ENNReal.ofReal (p.density (x i))) =
      ENNReal.ofReal (kepProductDensity p.density x) :=
    (ENNReal.ofReal_prod_of_nonneg (fun i _ => p.nonneg (x i))).symm
  simp_rw [hrho]
  have hp : Measurable (kepProductDensity (n := n) p.density) :=
    Finset.measurable_prod univ (fun i _ => p.measurable.comp (measurable_pi_apply i))
  rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hpn (x : Fin n → ℝ) : 0 ≤ kepProductDensity p.density x := prod_nonneg (fun i _ => p.nonneg (x i))
  simp only [ENNReal.toReal_ofReal (hpn _), smul_eq_mul]
  convert integral_congr_ae (μ := (volume : Measure (Fin n → ℝ)))
    (ae_of_all _ fun x => mul_comm (kepProductDensity p.density x) (F x)) using 1
  rfl

theorem kepReference_cone_second_transfer :
    ∃ eps0 : ℝ, kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ k : ℕ, ∀ A : Set (Fin (k + 1) → ℝ), MeasurableSet A →
          (∀ x (c : ℝ), 0 < c → (c • x ∈ A ↔ x ∈ A)) →
          (∀ x ∈ A, 0 < ∑ i, x i) →
          ∀ phi phi' phi'' : ℝ → ℝ,
            (∀ x, HasDerivAt phi (phi' x) x) → (∀ x, HasDerivAt phi' (phi'' x) x) →
            Continuous phi'' → ∀ a b : ℝ, 0 < a → Function.support phi ⊆ Icc a b →
                      let f := (kepReferenceDensity heps hj).density
            (∫ x in A, phi'' (∑ i, x i) ∂Measure.pi (fun _ => (kepReferenceLaw eps j : Measure ℝ))) =
              ∫ x in A, phi (∑ i, x i) / (∑ i, x i) ^ 2 *
                (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x) := by
  obtain ⟨e0, he0, hib⟩ := kepReference_mellin_insertions_integrable
  refine ⟨e0, he0, ?_⟩
  intro eps he heps j hj k A hA hcone hpos phi phi' phi'' hdphi hddphi hcphi'' a b ha hsupp
  dsimp only
  obtain ⟨hi0, hi1, hi2⟩ := hib eps he heps j hj
  have hc := kepReferenceDensity_classical heps hj
  have hid : (∫ x in A, phi'' (∑ i, x i) ∂Measure.pi (fun _ : Fin (k + 1) =>
      (kepReferenceLaw eps j : Measure ℝ))) =
      ∫ x in A, phi'' (∑ i, x i) * kepProductDensity (kepReferenceDensity heps hj).density x := by
    rw [← integral_indicator hA, kepReference_iid_integral_eq_product_density heps hj,
      ← integral_indicator hA]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  rw [hid]
  exact kep_product_cone_second_transfer hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
    hi0 hi1 hi2 hA hcone hpos hdphi hddphi hcphi'' ha hsupp

end

end PGM
