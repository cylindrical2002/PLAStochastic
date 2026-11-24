import PLAStochastic.ForMathlib.Probability.Gaussian.CoshLaplaceMixture
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.ExponentialIntegral

/-! # Two actual changes of variable behind the inverse Gaussian Laplace transform -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def gaussianHyperbola (a b x : ℝ) : ℝ := a*x-b/x

theorem hasDerivAt_gaussianHyperbola (a b : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (gaussianHyperbola a b) (a+b/x^2) x := by
  convert! ((hasDerivAt_id x).const_mul a).sub
    ((hasDerivAt_const x b).div (hasDerivAt_id x) hx) using 1
  dsimp only [id]
  ring

theorem strictMonoOn_gaussianHyperbola {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StrictMonoOn (gaussianHyperbola a b) (Ioi 0) := by
  intro x hx y hy hxy
  have hdiv : b/y < b/x := div_lt_div_of_pos_left hb hx hxy
  have hmul := mul_lt_mul_of_pos_left hxy ha
  dsimp only [gaussianHyperbola]
  linarith

theorem image_gaussianHyperbola {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    gaussianHyperbola a b '' Ioi 0=Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  let s := Real.sqrt (y^2+4*a*b)
  have hrad : 0 ≤ y^2+4*a*b := by positivity
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2=y^2+4*a*b := Real.sq_sqrt hrad
  have hsy : |y| < s := by nlinarith [sq_abs y]
  have hnum : 0 < y+s := by linarith [neg_abs_le y]
  let x := (y+s)/(2*a)
  have hx : 0 < x := div_pos hnum (by positivity)
  refine ⟨x,hx,?_⟩
  have hquad : a*x^2-y*x-b=0 := by
    dsimp only [x]
    field_simp
    nlinarith [hs2]
  dsimp only [gaussianHyperbola]
  apply (sub_eq_iff_eq_add).mpr
  field_simp
  nlinarith [hquad]

def gaussianReciprocal (a b x : ℝ) : ℝ := b/(a*x)

theorem gaussianReciprocal_pos {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    0 < gaussianReciprocal a b x := by unfold gaussianReciprocal; positivity

theorem gaussianReciprocal_involutive {a b x : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    gaussianReciprocal a b (gaussianReciprocal a b x)=x := by
  unfold gaussianReciprocal
  field_simp

theorem image_gaussianReciprocal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    gaussianReciprocal a b '' Ioi 0=Ioi 0 := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact gaussianReciprocal_pos ha hb hy
  · intro hx
    exact ⟨gaussianReciprocal a b x,gaussianReciprocal_pos ha hb hx,
      gaussianReciprocal_involutive ha.ne' hb.ne'⟩

theorem hasDerivAt_gaussianReciprocal {a b x : ℝ} (ha : a ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (gaussianReciprocal a b) (-b/(a*x^2)) x := by
  convert! (hasDerivAt_const x b).div ((hasDerivAt_id x).const_mul a) (mul_ne_zero ha hx) using 1
  dsimp only [id]
  field_simp
  ring

theorem gaussianHyperbola_reciprocal {a b x : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) :
    gaussianHyperbola a b (gaussianReciprocal a b x) = -gaussianHyperbola a b x := by
  unfold gaussianHyperbola gaussianReciprocal
  field_simp
  ring

end BrownianAffine
