import PLAStochastic.Index.KEP.ReferenceScale.IntegrableConeTransfer
import PLAStochastic.Index.KEP.ReferenceScale.ProductInverseIntegrability

/-!
# Weighted physical cone transfer for bounded tests meeting the origin

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

theorem kep_bounded_test_inverse_integrable {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {S P : alpha → ℝ} (hS : Measurable S)
    {A : Set alpha} (hA : MeasurableSet A) {psi : ℝ → ℝ} (hpsi : Measurable psi)
    {M : ℝ} (hb : ∀ t, |psi t| ≤ M) {m : ℕ}
    (hi : Integrable (fun x => ((S x) ^ m)⁻¹ * P x) mu) :
    Integrable (A.indicator (fun x => psi (S x) / (S x) ^ m * P x)) mu := by
  have hbound : ∀ᵐ x ∂mu, ‖psi (S x)‖ ≤ M := by
    simpa only [Real.norm_eq_abs] using ae_of_all mu (fun x => hb (S x))
  have hh := (hi.bdd_mul (hpsi.comp hS).aestronglyMeasurable hbound).indicator hA
  convert hh using 1 <;> first
  | rfl
  | (funext x
     by_cases hx : x ∈ A
     · simp only [indicator_of_mem hx, div_eq_mul_inv, Function.comp_apply]
       ring
     · simp only [indicator_of_notMem hx])

theorem kep_weighted_integrable_product_cone_second_transfer {k : ℕ} {f f' f'' : ℝ → ℝ}
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
    (_hcr2 : ∀ x, Continuous (fun s => rho2 (Real.exp s • x)))
    {phi phi' phi'' : ℝ → ℝ}
    (hdphi : ∀ x, HasDerivAt phi (phi' x) x)
    (hddphi : ∀ x, HasDerivAt phi' (phi'' x) x) (hcphi'' : Continuous phi'')
    {M : ℝ} (htest : ∀ t, |phi t| ≤ M ∧ |phi' t| ≤ M ∧ |phi'' t| ≤ M)
    (hiInv0 : Integrable (fun x : Fin (k + 1) → ℝ => ((∑ i, x i) ^ 2)⁻¹ * kepProductDensity f x))
    (hiInv1 : Integrable (fun x : Fin (k + 1) → ℝ => ((∑ i, x i) ^ 2)⁻¹ * kepProductMellinFirst f x))
    (hiInv2 : Integrable (fun x : Fin (k + 1) → ℝ => ((∑ i, x i) ^ 2)⁻¹ * kepProductMellinSecond f x)) :
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
  have hcphi' := continuous_iff_continuousAt.mpr fun x => (hddphi x).continuousAt
  have hiI0 : Integrable (fun x => ((∑ i, x i) ^ 2)⁻¹ * G0 x) volume := by
    convert hiInv0.bdd_mul hm0.aestronglyMeasurable hR0 using 1
    funext x
    dsimp [G0]
    ring
  have hiI1 : Integrable (fun x => ((∑ i, x i) ^ 2)⁻¹ * G1 x) volume := by
    convert (hiInv1.bdd_mul hm0.aestronglyMeasurable hR0).add
      (hiInv0.bdd_mul hm1.aestronglyMeasurable hR1) using 1 <;> first
    | rfl
    | (funext x; dsimp [G1]; ring)
  have hiI2 : Integrable (fun x => ((∑ i, x i) ^ 2)⁻¹ * G2 x) volume := by
    convert ((hiInv2.bdd_mul hm0.aestronglyMeasurable hR0).add
      ((hiInv1.bdd_mul hm1.aestronglyMeasurable hR1).const_mul 2)).add
      (hiInv0.bdd_mul hm2.aestronglyMeasurable hR2) using 1 <;> first
    | rfl
    | (funext x; dsimp [G2]; ring)
  have hiJ0 := kep_inverse_first_integrable_of_second hS hiG0 hiI0
  have hiJ1 := kep_inverse_first_integrable_of_second hS hiG1 hiI1
  have h00 := kep_bounded_test_inverse_integrable hS hA hcphi.measurable (fun t => (htest t).1) hiI0
  have h10 := kep_bounded_test_inverse_integrable hS hA hcphi'.measurable (fun t => (htest t).2.1) (m := 1)
    (by simpa only [pow_one] using hiJ0)
  have h20 := kep_bounded_test_inverse_integrable hS hA hcphi''.measurable (fun t => (htest t).2.2) (m := 0)
    (by simpa only [pow_zero, inv_one, one_mul] using hiG0)
  have h01 := kep_bounded_test_inverse_integrable hS hA hcphi.measurable (fun t => (htest t).1) hiI1
  have h11 := kep_bounded_test_inverse_integrable hS hA hcphi'.measurable (fun t => (htest t).2.1) (m := 1)
    (by simpa only [pow_one] using hiJ1)
  have h02 := kep_bounded_test_inverse_integrable hS hA hcphi.measurable (fun t => (htest t).1) hiI2
  simp only [pow_one, pow_zero, div_one] at h10 h20 h11
  have hh := kep_cone_integrable_physical_second_transfer hA hcone hpos hGzero hdG0 hdG1
    hdphi hddphi h00 h10 h20 h01 h11 h02
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
