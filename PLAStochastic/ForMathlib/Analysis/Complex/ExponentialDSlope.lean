import PLAStochastic.ForMathlib.Analysis.Complex.QuadraticExpUnit

/-! # Entire exponential divided differences on arbitrary moving-node parameter curves -/

noncomputable section
open Complex Filter Topology
namespace PGM

/-- The entire exponential divided difference uses a fixed removable unit. -/
theorem dslope_exp_eq_exp_mul (a b : ℂ) :
    dslope exp a b = exp a * dslope exp 0 (b - a) := by
  by_cases hab : b = a
  · subst b
    simp [dslope_same]
  · have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
    rw [dslope_of_ne _ hab, dslope_of_ne _ hba, slope_def_field, slope_def_field,
      sub_zero, exp_zero]
    have he : exp b = exp a * exp (b - a) := by
      rw [← exp_add, add_sub_cancel]
    rw [he]
    ring

/-- The reflected exponential divided difference is also entire in both nodes. -/
theorem dslope_exp_neg_eq_exp_mul (a b : ℂ) :
    dslope (fun ξ : ℂ => exp (-ξ)) a b = -exp (-a) * dslope exp 0 (a - b) := by
  by_cases hab : b = a
  · subst b
    rw [dslope_same]
    have hd : HasDerivAt (fun ξ : ℂ => exp (-ξ)) (-exp (-a)) a := by
      simpa only [mul_neg, mul_one, Pi.neg_apply, id_eq] using! (hasDerivAt_id a).neg.cexp
    rw [hd.deriv]
    simp [dslope_same]
  · have hba : a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    rw [dslope_of_ne _ hab, dslope_of_ne _ hba, slope_def_field, slope_def_field,
      sub_zero, exp_zero]
    have he : exp (-b) = exp (-a) * exp (a - b) := by
      rw [← exp_add]
      congr 1
      ring
    rw [he]
    field_simp
    ring

/-- Analytic parameter curves through colliding exponential nodes need no separation premise. -/
theorem analyticAt_dslope_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : E → ℂ} {x : E} (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x) :
    AnalyticAt ℂ (fun x => dslope exp (a x) (b x)) x := by
  have hunit := (complex_exp_dslope_differentiable.analyticAt (b x - a x)).comp
    (x := x) (f := fun x => b x - a x) (hb.sub ha)
  have he : (fun x => dslope exp (a x) (b x)) =
      (fun x => exp (a x) * dslope exp 0 (b x - a x)) :=
    funext fun x => dslope_exp_eq_exp_mul _ _
  rw [he]
  simpa only [Pi.mul_apply, Function.comp_apply] using! ha.cexp.mul hunit

theorem analyticAt_dslope_exp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : E → ℂ} {x : E} (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x) :
    AnalyticAt ℂ (fun x => dslope (fun ξ : ℂ => exp (-ξ)) (a x) (b x)) x := by
  have hunit := (complex_exp_dslope_differentiable.analyticAt (a x - b x)).comp
    (x := x) (f := fun x => a x - b x) (ha.sub hb)
  have he : (fun x => dslope (fun ξ : ℂ => exp (-ξ)) (a x) (b x)) =
      (fun x => -exp (-a x) * dslope exp 0 (a x - b x)) :=
    funext fun x => dslope_exp_neg_eq_exp_mul _ _
  rw [he]
  simpa only [Pi.mul_apply, Pi.neg_apply, Function.comp_apply] using! ha.neg.cexp.neg.mul hunit

end PGM
