import PLAStochastic.Affine.Moments.Optimal.Survival.Spatial.Boundary

/-! # The genuine reindexing boundary vanishes at infinite image index -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem shifted_pow_exp_tendsto {r : ℝ} (hr : 0<r) (p : ℕ) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^p*Real.exp (-r*(n:ℝ))) atTop (𝓝 0) := by
  have h := ((Real.summable_pow_mul_exp_neg_nat_mul p hr).tendsto_atTop_zero.comp
    (tendsto_add_atTop_nat 1)).mul_const (Real.exp r)
  convert! h using 1
  · funext n
    dsimp only [Function.comp_apply]
    push_cast
    rw [mul_assoc,←Real.exp_add,show -r*((n:ℝ)+1)+r= -r*(n:ℝ) by ring]
  · simp

private theorem pow_image_exp_tendsto {T : ℝ} (hT : 0<T) (φ : ℕ→ℝ)
    (hφ : ∀n : ℕ,(n:ℝ)≤φ n) (p : ℕ) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^p*Real.exp (-2*φ n/T)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (shifted_pow_exp_tendsto (by positivity : 0<2/T) p)
  · intro n
    positivity
  · intro n
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (hφ n) (by positivity : 0≤2/T)
    convert! neg_le_neg h using 1 <;> ring

private theorem rational_quadratic_image_tendsto {E : ℕ→ℝ}
    (hE : ∀p : ℕ,Tendsto (fun n : ℕ => ((n:ℝ)+1)^p*E n) atTop (𝓝 0))
    (a b c d e : ℝ) :
    Tendsto (fun n : ℕ => (a*((n:ℝ)+1)^2+b*((n:ℝ)+1)+c+d/((n:ℝ)+1)+e/((n:ℝ)+1)^2)*E n)
      atTop (𝓝 0) := by
  have h₀ : Tendsto E atTop (𝓝 0) := by simpa only [pow_zero,one_mul] using hE 0
  have h₁ : Tendsto (fun n : ℕ => ((n:ℝ)+1)*E n) atTop (𝓝 0) := by simpa only [pow_one] using hE 1
  have hi : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h := ((((hE 2).const_mul a).add (h₁.const_mul b)).add (h₀.const_mul c)).add
    ((hi.mul h₀).const_mul d) |>.add (((hi.pow 2).mul h₀).const_mul e)
  convert! h using 1
  · funext n
    simp only [div_eq_mul_inv,inv_pow]
    ring
  · simp

private theorem boundary_middle_coefficient (n : ℕ) (T : ℝ) :
    imageEqualMiddleCoefficient ((n:ℝ)+1) T (optimalQImagePreviousC n) (optimalQImagePreviousB n)-
      4*optimalQImagePreviousC n/((n:ℝ)+1)=
      (-8/3)*((n:ℝ)+1)^2+4*((n:ℝ)+1)+(T/3-4/3)+0/((n:ℝ)+1)+(-T/3)/((n:ℝ)+1)^2 := by
  unfold imageEqualMiddleCoefficient optimalQImagePreviousC optimalQImagePreviousB
  have hm : (n:ℝ)+1≠0 := by positivity
  field_simp
  ring

private theorem boundary_upper_coefficient (n : ℕ) (T : ℝ) :
    imageEqualUpperCoefficient ((n:ℝ)+1) T (optimalQImagePreviousC n) (optimalQImagePreviousB n)=
      (2/3)*((n:ℝ)+1)^2+(-2/3)*((n:ℝ)+1)+(-T/6-1/6)+(1/6)/((n:ℝ)+1)+(T/6)/((n:ℝ)+1)^2 := by
  unfold imageEqualUpperCoefficient optimalQImagePreviousC optimalQImagePreviousB
  have hm : (n:ℝ)+1≠0 := by positivity
  field_simp
  ring

private theorem boundary_lower_coefficient (n : ℕ) (T : ℝ) :
    imageEqualLowerCoefficient ((n:ℝ)+1) T (optimalQImageCoefficientC n) (optimalQImageCoefficientB n)=
      (2/3)*((n:ℝ)+1)^2+(2/3)*((n:ℝ)+1)+(-T/6-1/6)+(-1/6)/((n:ℝ)+1)+(T/6)/((n:ℝ)+1)^2 := by
  unfold imageEqualLowerCoefficient optimalQImageCoefficientC optimalQImageCoefficientB
  have hm : (n:ℝ)+1≠0 := by positivity
  field_simp
  ring

private theorem boundary_e1_tendsto {T : ℝ} (hT : 0<T) :
    Tendsto (fun n : ℕ => 4*optimalQImagePreviousB n*exponentialIntegralE1 (2*((n:ℝ)+1)^2/T))
      atTop (𝓝 0) := by
  have hg := pow_image_exp_tendsto hT (fun n : ℕ => ((n:ℝ)+1)^2)
    (fun n : ℕ => by nlinarith [Nat.cast_nonneg (α := ℝ) n,sq_nonneg (n:ℝ)]) 0
  have hg' : Tendsto (fun n : ℕ => T*Real.exp (-2*((n:ℝ)+1)^2/T)) atTop (𝓝 0) := by
    simpa only [pow_zero,one_mul,mul_zero] using hg.const_mul T
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg'
  · intro n
    exact mul_nonneg (by unfold optimalQImagePreviousB; positivity) (exponentialIntegralE1_nonneg _)
  · intro n
    have hn := Nat.cast_nonneg (α := ℝ) n
    have harg : 0<2*((n:ℝ)+1)^2/T := by positivity
    have hb : 0≤4*optimalQImagePreviousB n := by unfold optimalQImagePreviousB; positivity
    have h := mul_le_mul_of_nonneg_left (exponentialIntegralE1_le harg) hb
    apply h.trans
    rw [show -(2*((n:ℝ)+1)^2/T)= -2*((n:ℝ)+1)^2/T by ring]
    have hc : 4*optimalQImagePreviousB n/(2*((n:ℝ)+1)^2/T)≤T := by
      unfold optimalQImagePreviousB
      apply (div_le_iff₀ harg).mpr
      field_simp
      nlinarith
    calc
      _ = (4*optimalQImagePreviousB n/(2*((n:ℝ)+1)^2/T))*Real.exp (-2*((n:ℝ)+1)^2/T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)

/-- The complete, explicitly defined spatial collection boundary has zero limit. -/
theorem tendsto_optimalImageSpatialBoundary {T : ℝ} (hT : 0<T) :
    Tendsto (fun n : ℕ => optimalImageSpatialBoundary n T) atTop (𝓝 0) := by
  have h₀ := pow_image_exp_tendsto hT (fun n : ℕ => ((n:ℝ)+1)^2)
    (fun n : ℕ => by nlinarith [Nat.cast_nonneg (α := ℝ) n,sq_nonneg (n:ℝ)])
  have h₁ := pow_image_exp_tendsto hT (fun n : ℕ => ((n:ℝ)+1)*((n:ℝ)+2))
    (fun n : ℕ => by nlinarith [Nat.cast_nonneg (α := ℝ) n,sq_nonneg (n:ℝ)])
  have h₂ := pow_image_exp_tendsto hT (fun n : ℕ => ((n:ℝ)+1)*(n:ℝ))
    (fun n : ℕ => by nlinarith [sq_nonneg (n:ℝ)])
  have h := (((rational_quadratic_image_tendsto h₀ (-8/3) 4 (T/3-4/3) 0 (-T/3)).add
    (boundary_e1_tendsto hT)).add
    (rational_quadratic_image_tendsto h₁ (2/3) (-2/3) (-T/6-1/6) (1/6) (T/6))).sub
    (rational_quadratic_image_tendsto h₂ (2/3) (2/3) (-T/6-1/6) (-1/6) (T/6))
  convert! h using 1
  · funext n
    dsimp only [optimalImageSpatialBoundary]
    rw [boundary_middle_coefficient,boundary_upper_coefficient,boundary_lower_coefficient]
    rw [show (n:ℝ)+1+1=(n:ℝ)+2 by ring,show (n:ℝ)+1-1=(n:ℝ) by ring]
    simp only [mul_assoc]
  · norm_num

end BrownianAffine
