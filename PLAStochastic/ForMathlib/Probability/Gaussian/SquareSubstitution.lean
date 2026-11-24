import PLAStochastic.ForMathlib.Probability.Gaussian.HyperbolaSubstitution

/-! # Squaring as a genuine change of variable on the positive half line -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem image_sq_Ioi_zero : (fun x : ℝ => x^2) '' Ioi 0=Ioi 0 := by
  ext t
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact sq_pos_of_pos (show 0 < x from hx)
  · intro ht
    exact ⟨Real.sqrt t,Real.sqrt_pos.mpr ht,Real.sq_sqrt ht.le⟩

theorem injOn_sq_Ioi_zero : Set.InjOn (fun x : ℝ => x^2) (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  dsimp only at hxy
  nlinarith

private theorem hasDerivWithinAt_sq_Ioi (x : ℝ) :
    HasDerivWithinAt (fun x : ℝ => x^2) (2*x) (Ioi 0) x := by
  convert! ((hasDerivAt_id x).pow 2).hasDerivWithinAt using 1
  simp

theorem integrableOn_Ioi_square_iff (F : ℝ → ℝ) :
    IntegrableOn F (Ioi 0) ↔ IntegrableOn (fun x => 2*x*F (x^2)) (Ioi 0) := by
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun x (_ : x ∈ Ioi (0:ℝ)) => hasDerivWithinAt_sq_Ioi x) injOn_sq_Ioi_zero F
  rw [image_sq_Ioi_zero] at hi
  rw [hi]
  refine integrableOn_congr_fun ?_ measurableSet_Ioi
  intro x hx
  change 0 < x at hx
  dsimp only
  rw [smul_eq_mul,abs_of_pos (by positivity : 0 < 2*x)]

theorem integral_Ioi_eq_square (F : ℝ → ℝ) :
    (∫ t in Ioi (0:ℝ), F t)=∫ x in Ioi (0:ℝ), 2*x*F (x^2) := by
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x (_ : x ∈ Ioi (0:ℝ)) => hasDerivWithinAt_sq_Ioi x) injOn_sq_Ioi_zero F
  rw [image_sq_Ioi_zero] at hi
  rw [hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change 0 < x at hx
  dsimp only
  rw [smul_eq_mul,abs_of_pos (by positivity : 0 < 2*x)]

end BrownianAffine
