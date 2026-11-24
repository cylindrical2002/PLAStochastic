import PLAStochastic.Index.KEP.ReferenceScale.ConeSecondTransfer
import PLAStochastic.Index.KEP.ReferenceScale.ProductMellinIntegrability
import PLAStochastic.Index.KEP.ReferenceScale.ProductMellinSupport
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Complete physical weak transfer for a product density on a cone

The one-dimensional Mellin integrability pays every multivariate derivative
term. Compact tests supported away from zero pay the inverse square and both
sides are absolutely integrable. These are proved here, rather than left as
analytic inputs to the cone transfer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Set Finset

theorem kep_compact_test_inverse_square_bound {phi : ℝ → ℝ} (hphi : Continuous phi)
    {a b : ℝ} (ha : 0 < a) (hsupp : Function.support phi ⊆ Icc a b) :
    ∃ M : ℝ, ∀ x, |phi x / x ^ 2| ≤ M := by
  have hc : HasCompactSupport phi :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hsupp isClosed_Icc)
  obtain ⟨M, hM⟩ := hphi.bounded_above_of_compact_support hc
  have hM0 : 0 ≤ M := (norm_nonneg (phi 0)).trans (hM 0)
  refine ⟨M / a ^ 2, ?_⟩
  intro x
  by_cases hx : phi x = 0
  · rw [hx, zero_div, abs_zero]
    positivity
  · have hxa : a ≤ x := (hsupp hx).1
    have hpow : a ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ ha.le hxa 2
    rw [abs_div, abs_of_nonneg (sq_nonneg x)]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos ha 2) hpow).trans
      (div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hM x) (sq_nonneg a))

theorem kep_product_cone_second_transfer {k : ℕ} {f f' f'' : ℝ → ℝ}
    (hzero : ∀ x ≤ 0, f x = 0)
    (hdf : ∀ x, HasDerivAt f (f' x) x) (hddf : ∀ x, HasDerivAt f' (f'' x) x)
    (hcf'' : Continuous f'')
    (hi0 : Integrable f volume) (hi1 : Integrable (mellinOp f) volume)
    (hi2 : Integrable (mellinOp (mellinOp f)) volume)
    {A : Set (Fin (k + 1) → ℝ)} (hA : MeasurableSet A)
    (hcone : ∀ x (c : ℝ), 0 < c → (c • x ∈ A ↔ x ∈ A))
    (hpos : ∀ x ∈ A, 0 < ∑ i, x i)
    {phi phi' phi'' : ℝ → ℝ}
    (hdphi : ∀ x, HasDerivAt phi (phi' x) x)
    (hddphi : ∀ x, HasDerivAt phi' (phi'' x) x) (hcphi'' : Continuous phi'')
    {a b : ℝ} (ha : 0 < a) (hsupp : Function.support phi ⊆ Icc a b) :
    (∫ x in A, phi'' (∑ i, x i) * kepProductDensity f x) =
      ∫ x in A, phi (∑ i, x i) / (∑ i, x i) ^ 2 *
        (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x) := by
  obtain ⟨_hc0, _hc1, hc2⟩ := kepProductMellin_continuous (n := k + 1) hdf hddf hcf''
  obtain ⟨hp0, hp1, hp2⟩ := kepProductMellin_integrable (n := k + 1) hi0 hi1 hi2
  have hMzero (x : Fin (k + 1) → ℝ) (hx : x (Fin.last k) ≤ 0) :
      kepProductDensity f x = 0 ∧ kepProductMellinFirst f x = 0 ∧ kepProductMellinSecond f x = 0 :=
    kepProductMellin_zero_coordinate x (Fin.last k) (hzero _ hx)
      (mellinOp_iterate_eq_zero_of_nonpos hzero 1 _ hx)
      (mellinOp_iterate_eq_zero_of_nonpos hzero 2 _ hx)
  have hS : Measurable (fun x : Fin (k + 1) → ℝ => ∑ i, x i) :=
    Finset.measurable_sum univ (fun i _ => measurable_pi_apply i)
  have hcphi := continuous_iff_continuousAt.mpr fun x => (hdphi x).continuousAt
  have hsphi : HasCompactSupport phi :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hsupp isClosed_Icc)
  have he1 : phi' = deriv phi := funext fun x => (hdphi x).deriv.symm
  have he2 : phi'' = deriv phi' := funext fun x => (hddphi x).deriv.symm
  have hsphi'' : HasCompactSupport phi'' := by rw [he2, he1]; exact hsphi.deriv.deriv
  obtain ⟨M2, hM2⟩ := hcphi''.bounded_above_of_compact_support hsphi''
  obtain ⟨M0, hM0⟩ := kep_compact_test_inverse_square_bound hcphi ha hsupp
  have hl : Integrable (A.indicator (fun x : Fin (k + 1) → ℝ =>
      phi'' (∑ i, x i) * kepProductDensity f x)) volume := by
    apply Integrable.indicator _ hA
    exact hp0.bdd_mul (hcphi''.measurable.comp hS).aestronglyMeasurable
      (ae_of_all _ fun x => hM2 (∑ i, x i))
  have hq : Integrable (fun x : Fin (k + 1) → ℝ =>
      kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x) volume :=
    (hp2.sub (hp1.const_mul 3)).add (hp0.const_mul 2)
  have hr : Integrable (A.indicator (fun x : Fin (k + 1) → ℝ => phi (∑ i, x i) / (∑ i, x i) ^ 2 *
      (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x))) volume := by
    apply Integrable.indicator _ hA
    exact hq.bdd_mul ((hcphi.measurable.comp hS).div (hS.pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hM0 (∑ i, x i))
  exact kep_cone_physical_second_transfer hA hcone hpos hMzero
    (fun x s => (kepProductMellin_radial_derivatives hdf hddf x s).1)
    (fun x s => (kepProductMellin_radial_derivatives hdf hddf x s).2)
    (fun x => by fun_prop) hdphi hddphi hcphi'' ha hsupp hl hr

end

end PGM
