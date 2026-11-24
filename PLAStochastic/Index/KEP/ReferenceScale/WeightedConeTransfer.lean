import PLAStochastic.Index.KEP.ReferenceScale.ProductConeTransfer

/-!
# Exact physical second transfer with a smooth radial weight

The angular event may be arbitrary. True radial derivatives of the bounded
weight pay the cutoff terms. The density derivatives are the complete product
Mellin fields, with both ordered cross insertions retained. All integrability
and coordinate-face boundary inputs are discharged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Set Finset

theorem kep_weighted_product_cone_second_transfer {k : ℕ} {f f' f'' : ℝ → ℝ}
    (hzero : ∀ x ≤ 0, f x = 0)
    (hdf : ∀ x, HasDerivAt f (f' x) x) (hddf : ∀ x, HasDerivAt f' (f'' x) x)
    (hcf'' : Continuous f'')
    (hi0 : Integrable f volume) (hi1 : Integrable (mellinOp f) volume)
    (hi2 : Integrable (mellinOp (mellinOp f)) volume)
    {A : Set (Fin (k + 1) → ℝ)} (hA : MeasurableSet A)
    (hcone : ∀ x (c : ℝ), 0 < c → (c • x ∈ A ↔ x ∈ A))
    (hpos : ∀ x ∈ A, 0 < ∑ i, x i)
    {rho0 rho1 rho2 : (Fin (k + 1) → ℝ) → ℝ}
    (hm0 : Measurable rho0) (hm1 : Measurable rho1) (hm2 : Measurable rho2)
    {B : ℝ} (hb0 : ∀ x, |rho0 x| ≤ B) (hb1 : ∀ x, |rho1 x| ≤ B) (hb2 : ∀ x, |rho2 x| ≤ B)
    (hdr0 : ∀ x s, HasDerivAt (fun t => rho0 (Real.exp t • x)) (rho1 (Real.exp s • x)) s)
    (hdr1 : ∀ x s, HasDerivAt (fun t => rho1 (Real.exp t • x)) (rho2 (Real.exp s • x)) s)
    (hcr2 : ∀ x, Continuous (fun s => rho2 (Real.exp s • x)))
    {phi phi' phi'' : ℝ → ℝ}
    (hdphi : ∀ x, HasDerivAt phi (phi' x) x)
    (hddphi : ∀ x, HasDerivAt phi' (phi'' x) x) (hcphi'' : Continuous phi'')
    {a b : ℝ} (ha : 0 < a) (hsupp : Function.support phi ⊆ Icc a b) :
    (∫ x in A, phi'' (∑ i, x i) * rho0 x * kepProductDensity f x) =
      ∫ x in A, phi (∑ i, x i) / (∑ i, x i) ^ 2 *
        (rho0 x * (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x) +
          rho1 x * (2 * kepProductMellinFirst f x - 3 * kepProductDensity f x) + rho2 x * kepProductDensity f x) := by
  let G0 := fun x : Fin (k + 1) → ℝ => rho0 x * kepProductDensity f x
  let G1 := fun x : Fin (k + 1) → ℝ => rho0 x * kepProductMellinFirst f x + rho1 x * kepProductDensity f x
  let G2 := fun x : Fin (k + 1) → ℝ => rho0 x * kepProductMellinSecond f x +
    2 * (rho1 x * kepProductMellinFirst f x) + rho2 x * kepProductDensity f x
  obtain ⟨hc0, hc1, hc2⟩ := kepProductMellin_continuous (n := k + 1) hdf hddf hcf''
  obtain ⟨hp0, hp1, hp2⟩ := kepProductMellin_integrable (n := k + 1) hi0 hi1 hi2
  have hPr0 := kepProductMellin_radial_derivatives (n := k + 1) hdf hddf
  have hdG0 (x : Fin (k + 1) → ℝ) (s : ℝ) : HasDerivAt
      (fun t => Real.exp (((k + 1 : ℕ) : ℝ) * t) * G0 (Real.exp t • x))
      (Real.exp (((k + 1 : ℕ) : ℝ) * s) * G1 (Real.exp s • x)) s := by
    convert (hdr0 x s).mul (hPr0 x s).1 using 1 <;> first
    | rfl
    | (funext t; dsimp [G0]; ring)
    | (dsimp [G1]; ring)
  have hdG1 (x : Fin (k + 1) → ℝ) (s : ℝ) : HasDerivAt
      (fun t => Real.exp (((k + 1 : ℕ) : ℝ) * t) * G1 (Real.exp t • x))
      (Real.exp (((k + 1 : ℕ) : ℝ) * s) * G2 (Real.exp s • x)) s := by
    convert ((hdr0 x s).mul (hPr0 x s).2).add ((hdr1 x s).mul (hPr0 x s).1) using 1 <;> first
    | rfl
    | (funext t; dsimp [G1]; ring)
    | (dsimp [G2]; ring)
  have hGzero (x : Fin (k + 1) → ℝ) (hx : x (Fin.last k) ≤ 0) : G0 x = 0 ∧ G1 x = 0 ∧ G2 x = 0 := by
    have hz := kepProductMellin_zero_coordinate x (Fin.last k) (hzero _ hx)
      (mellinOp_iterate_eq_zero_of_nonpos hzero 1 _ hx) (mellinOp_iterate_eq_zero_of_nonpos hzero 2 _ hx)
    simp only [G0, G1, G2, hz.1, hz.2.1, hz.2.2, mul_zero, add_zero, and_self]
  have hcG2 (x : Fin (k + 1) → ℝ) :
      Continuous (fun s => Real.exp (((k + 1 : ℕ) : ℝ) * s) * G2 (Real.exp s • x)) := by
    have hcR0 := continuous_iff_continuousAt.mpr fun s => (hdr0 x s).continuousAt
    have hcR1 := continuous_iff_continuousAt.mpr fun s => (hdr1 x s).continuousAt
    have hcR2 := hcr2 x
    have hmap : Continuous (fun s : ℝ => Real.exp s • x) := Real.continuous_exp.smul continuous_const
    dsimp [G2]
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (((hcR0.mul (hc2.comp hmap)).add ((hcR1.mul (hc1.comp hmap)).const_mul 2)).add
        (hcR2.mul (hc0.comp hmap)))
  have hR0 : ∀ᵐ x ∂(volume : Measure (Fin (k + 1) → ℝ)), ‖rho0 x‖ ≤ B := by
    simpa only [Real.norm_eq_abs] using ae_of_all volume hb0
  have hR1 : ∀ᵐ x ∂(volume : Measure (Fin (k + 1) → ℝ)), ‖rho1 x‖ ≤ B := by
    simpa only [Real.norm_eq_abs] using ae_of_all volume hb1
  have hR2 : ∀ᵐ x ∂(volume : Measure (Fin (k + 1) → ℝ)), ‖rho2 x‖ ≤ B := by
    simpa only [Real.norm_eq_abs] using ae_of_all volume hb2
  have hiG0 : Integrable G0 volume := hp0.bdd_mul hm0.aestronglyMeasurable hR0
  have hiG1 : Integrable G1 volume := (hp1.bdd_mul hm0.aestronglyMeasurable hR0).add
    (hp0.bdd_mul hm1.aestronglyMeasurable hR1)
  have hiG2 : Integrable G2 volume := ((hp2.bdd_mul hm0.aestronglyMeasurable hR0).add
    ((hp1.bdd_mul hm1.aestronglyMeasurable hR1).const_mul 2)).add (hp0.bdd_mul hm2.aestronglyMeasurable hR2)
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
  have hl : Integrable (A.indicator (fun x => phi'' (∑ i, x i) * G0 x)) volume :=
    (hiG0.bdd_mul (hcphi''.measurable.comp hS).aestronglyMeasurable
      (ae_of_all _ fun x => hM2 (∑ i, x i))).indicator hA
  have hq : Integrable (fun x => G2 x - 3 * G1 x + 2 * G0 x) volume :=
    (hiG2.sub (hiG1.const_mul 3)).add (hiG0.const_mul 2)
  have hr : Integrable (A.indicator (fun x => phi (∑ i, x i) / (∑ i, x i) ^ 2 *
      (G2 x - 3 * G1 x + 2 * G0 x))) volume :=
    (hq.bdd_mul ((hcphi.measurable.comp hS).div (hS.pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, Pi.div_apply, Function.comp_apply] using hM0 (∑ i, x i))).indicator hA
  have hh := kep_cone_physical_second_transfer hA hcone hpos hGzero hdG0 hdG1 hcG2
    hdphi hddphi hcphi'' ha hsupp hl hr
  calc
    _ = ∫ x in A, phi'' (∑ i, x i) * G0 x := by
      apply setIntegral_congr_fun hA
      intro x _
      dsimp [G0]
      ring
    _ = ∫ x in A, phi (∑ i, x i) / (∑ i, x i) ^ 2 * (G2 x - 3 * G1 x + 2 * G0 x) := hh
    _ = _ := by
      apply setIntegral_congr_fun hA
      intro x _
      dsimp [G0, G1, G2]
      ring

end

end PGM
