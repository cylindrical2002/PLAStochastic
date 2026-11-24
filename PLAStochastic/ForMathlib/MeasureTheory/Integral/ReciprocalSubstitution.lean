import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Reciprocal substitution on a positive compact interval

The derivative factor is retained exactly. This is useful when a physical
endpoint is sampled along the curve `x = b / a` while integrating over slope.
-/

set_option autoImplicit false

namespace MeasureTheory

noncomputable section

open Set

private theorem reciprocal_continuousOn {b lo hi : ℝ} (hlo : 0 < lo) :
    ContinuousOn (fun a : ℝ => b / a) (Icc lo hi) :=
  continuousOn_const.div continuousOn_id (fun _ ha => ne_of_gt (hlo.trans_le ha.1))

private theorem reciprocal_derivOn {b lo hi : ℝ} (hlo : 0 < lo) :
    ∀ a ∈ Ioo lo hi, HasDerivAt (fun a : ℝ => b / a) (-(b / a ^ 2)) a := by
  intro a ha
  simpa only [div_eq_mul_inv, mul_neg] using
    (hasDerivAt_inv (ne_of_gt (hlo.trans ha.1))).const_mul b

/-- The exact reciprocal Jacobian, with no integrability restriction on the
integrand. The Bochner change-of-variables theorem also handles undefined
integrals consistently. -/
theorem integral_div_sq_comp_reciprocal_Icc (g : ℝ → ℝ) {b lo hi : ℝ}
    (hb : 0 < b) (hlo : 0 < lo) (hle : lo ≤ hi) :
    (∫ a in Icc lo hi, g (b / a) / a ^ 2) =
      (∫ x in Icc (b / hi) (b / lo), g x) / b := by
  have h := integral_Icc_deriv_smul_of_deriv_nonpos
    (reciprocal_continuousOn (b := b) (hi := hi) hlo)
    (reciprocal_derivOn (b := b) (hi := hi) hlo)
    (fun a _ => neg_nonpos.mpr (div_nonneg hb.le (sq_nonneg a))) hle (g := g)
  simp only [smul_eq_mul] at h
  have he : (fun a : ℝ => -(b / a ^ 2) * g (b / a)) =
      (fun a : ℝ => -b * (g (b / a) / a ^ 2)) := by
    funext a
    ring
  rw [he, integral_const_mul] at h
  apply (eq_div_iff hb.ne').mpr
  nlinarith [h]

theorem integrableOn_div_sq_comp_reciprocal_Icc {g : ℝ → ℝ} {b lo hi : ℝ}
    (hb : 0 < b) (hlo : 0 < lo) (hle : lo ≤ hi)
    (hg : IntegrableOn g (Icc (b / hi) (b / lo))) :
    IntegrableOn (fun a => g (b / a) / a ^ 2) (Icc lo hi) := by
  have h := (integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos
    (reciprocal_continuousOn (b := b) (hi := hi) hlo)
    (reciprocal_derivOn (b := b) (hi := hi) hlo)
    (fun a _ => neg_nonpos.mpr (div_nonneg hb.le (sq_nonneg a))) hle (g := g)).mpr hg
  have he : (fun a : ℝ => -(b / a ^ 2) • g (b / a)) =
      (fun a : ℝ => -b * (g (b / a) / a ^ 2)) := by
    funext a
    simp only [smul_eq_mul]
    ring
  rw [he] at h
  have hi' : IntegrableOn (fun a => -b * (g (b / a) / a ^ 2) / -b) (Icc lo hi) :=
    h.div_const (-b)
  exact hi'.congr_fun (fun a _ => by
    dsimp only
    field_simp) measurableSet_Icc

theorem integral_div_sq_comp_reciprocal_Icc_le {g : ℝ → ℝ} {b lo hi : ℝ}
    (hb : 0 < b) (hlo : 0 < lo) (hle : lo ≤ hi)
    (hg : Integrable g volume) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ a in Icc lo hi, g (b / a) / a ^ 2) ≤ (∫ x, g x) / b := by
  rw [integral_div_sq_comp_reciprocal_Icc g hb hlo hle]
  exact div_le_div_of_nonneg_right (setIntegral_le_integral hg (ae_of_all _ hg0)) hb.le

end

end MeasureTheory
