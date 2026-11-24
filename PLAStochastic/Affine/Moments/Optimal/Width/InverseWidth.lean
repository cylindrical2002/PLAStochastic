import PLAStochastic.Affine.Moments.Optimal.Width.UnitWidthCoordinates
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Inverse-square width substitution with the exact real-order weight and Jacobian. -/
theorem integral_inverseSquare_moment_weight (F : ℝ→ℝ) (q : ℝ) :
    (∫ r in Ioi (0:ℝ), r^(-2*q)*F (1/r^2))=
      (1/2:ℝ)*∫ T in Ioi (0:ℝ), T^(q-3/2)*F T := by
  have h := integral_comp_rpow_Ioi (fun T : ℝ => T^(q-3/2)*F T) (p := (-2:ℝ)) (by norm_num)
  have hpoint {r : ℝ} (hr : 0<r) :
      (|(-2:ℝ)| *r^((-2:ℝ)-1)) • ((r^(-2:ℝ))^(q-3/2)*F (r^(-2:ℝ)))=
        2*(r^(-2*q)*F (1/r^2)) := by
    rw [smul_eq_mul,←Real.rpow_mul hr.le]
    have he : (-2:ℝ)-1+(-2)*(q-3/2)=-2*q := by ring
    rw [show |(-2:ℝ)|=2 by norm_num]
    calc
      _ = 2*(r^((-2:ℝ)-1)*r^((-2)*(q-3/2)))*F (r^(-2:ℝ)) := by ring
      _ = _ := by
        rw [←Real.rpow_add hr,he,Real.rpow_neg hr.le,show r^(2:ℝ)=r^2 from Real.rpow_natCast r 2,one_div]
        ring
  have heq : (∫ r in Ioi (0:ℝ),
      (|(-2:ℝ)| *r^((-2:ℝ)-1)) • ((r^(-2:ℝ))^(q-3/2)*F (r^(-2:ℝ))))=
      2*∫ r in Ioi (0:ℝ), r^(-2*q)*F (1/r^2) := by
    rw [←integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => hpoint hr)
  rw [heq] at h
  linarith

/-- Positive powers admit the same arbitrary nonnegative substitution, with no integrability premise. -/
theorem lintegral_comp_rpow_Ioi (G : ℝ→ℝ≥0∞) {p : ℝ} (hp : p≠0) :
    (∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal (|p| *x^(p-1))*G (x^p))=∫⁻ y in Ioi (0:ℝ), G y := by
  have him : (fun x : ℝ => x^p) '' Ioi (0:ℝ)=Ioi (0:ℝ) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact Real.rpow_pos_of_pos hx p
    · intro hy
      exact ⟨y^(1/p),Real.rpow_pos_of_pos hy _,by simp [←Real.rpow_mul hy.le,hp]⟩
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')).hasDerivWithinAt)
    ((Real.rpow_left_injOn hp).mono (show Ioi (0:ℝ)⊆Ici (0:ℝ) from fun _ hx => mem_Ici.mpr (mem_Ioi.mp hx).le)) G
  rw [him] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg hx.le _)]

/-- The exact inverse-width moment substitution also preserves infinite nonnegative integrals. -/
theorem lintegral_inverseSquare_moment_weight (F : ℝ→ℝ≥0∞) (q : ℝ) :
    (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(-2*q))*F (1/r^2))=
      (1/2:ℝ≥0∞)*∫⁻ T in Ioi (0:ℝ), ENNReal.ofReal (T^(q-3/2))*F T := by
  have h := lintegral_comp_rpow_Ioi (fun T : ℝ => ENNReal.ofReal (T^(q-3/2))*F T)
    (p := (-2:ℝ)) (by norm_num)
  have he : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (|(-2:ℝ)| *r^((-2:ℝ)-1))*
      (ENNReal.ofReal ((r^(-2:ℝ))^(q-3/2))*F (r^(-2:ℝ))))=
      2*∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(-2*q))*F (1/r^2) := by
    rw [←lintegral_const_mul' _ _ (by norm_num : (2:ℝ≥0∞)≠∞)]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    have hc : |(-2:ℝ)| *r^((-2:ℝ)-1)*(r^(-2:ℝ))^(q-3/2)=2*r^(-2*q) := by
      rw [←Real.rpow_mul hr.le]
      calc
        _ = 2*(r^((-2:ℝ)-1)*r^((-2)*(q-3/2))) := by norm_num; ring
        _ = _ := by rw [←Real.rpow_add hr,show (-2:ℝ)-1+(-2)*(q-3/2)=-2*q by ring]
    rw [←mul_assoc,←ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hr.le _)),hc,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,
      Real.rpow_neg hr.le,show r^(2:ℝ)=r^2 from Real.rpow_natCast r 2,one_div,mul_assoc]
  rw [he] at h
  have heq := (ENNReal.eq_div_iff (by norm_num : (2:ℝ≥0∞)≠0) (by norm_num : (2:ℝ≥0∞)≠∞)).mpr h
  simpa only [one_div,ENNReal.div_eq_inv_mul] using heq

end BrownianAffine
