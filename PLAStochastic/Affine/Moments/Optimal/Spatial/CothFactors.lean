import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.CenteredCoth.Asymptotics

/-! # The genuine first three derivatives of the spatial cotangent factor -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

def spatialCothFactor0 (x : ℝ) : ℝ :=
  ((centeredCoth x)*(1/(Real.sinh x)^3))

def spatialCothFactor1 (x : ℝ) : ℝ :=
  ((1/(Real.sinh x)^3)*(1 + (-4*((centeredCoth x)^2)) + (-5*(centeredCoth x)*(1/x^1))))

def spatialCothFactor2 (x : ℝ) : ℝ :=
  ((1/(Real.sinh x)^3)*((-11*(centeredCoth x)) + (-8*(1/x^1)) + (20*((centeredCoth x)^3)) + (30*(centeredCoth x)*(1/x^2)) + (48*((centeredCoth x)^2)*(1/x^1))))

def spatialCothFactor3 (x : ℝ) : ℝ :=
  ((1/(Real.sinh x)^3)*(-11 + (-120*((centeredCoth x)^4)) + (62*(1/x^2)) + (104*((centeredCoth x)^2)) + (-504*((centeredCoth x)^2)*(1/x^2)) + (-420*((centeredCoth x)^3)*(1/x^1)) + (-210*(centeredCoth x)*(1/x^3)) + (175*(centeredCoth x)*(1/x^1))))

theorem cosh_eq_centeredCoth {x : ℝ} (hx : x ≠ 0) :
    Real.cosh x=(centeredCoth x+1/x)*Real.sinh x := by
  unfold centeredCoth
  have hs := Real.sinh_ne_zero.mpr hx
  field_simp
  ring

theorem hasDerivAt_spatialCothFactor0 {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt spatialCothFactor0 (spatialCothFactor1 x) x := by
  have hx0 := hx
  have hs0 := Real.sinh_ne_zero.mpr hx
  have hf := hasDerivAt_centeredCoth hx
  have hd := (hf.mul ((hasDerivAt_const x (1 : ℝ)).div ((Real.hasDerivAt_sinh x).pow 3) (pow_ne_zero 3 hs0)))
  convert! hd using 1
  dsimp only [spatialCothFactor1,Pi.pow_apply,Pi.div_apply,Pi.mul_apply,Pi.add_apply,id_eq]
  rw [cosh_eq_centeredCoth hx]
  field_simp
  ring

theorem hasDerivAt_spatialCothFactor1 {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt spatialCothFactor1 (spatialCothFactor2 x) x := by
  have hx0 := hx
  have hs0 := Real.sinh_ne_zero.mpr hx
  have hf := hasDerivAt_centeredCoth hx
  have hd := (((hasDerivAt_const x (1 : ℝ)).div ((Real.hasDerivAt_sinh x).pow 3) (pow_ne_zero 3 hs0)).mul (((hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_const x (-4 : ℝ)).mul (hf.pow 2))).add (((hasDerivAt_const x (-5 : ℝ)).mul hf).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 1) (pow_ne_zero 1 hx0)))))
  convert! hd using 1
  dsimp only [spatialCothFactor2,Pi.pow_apply,Pi.div_apply,Pi.mul_apply,Pi.add_apply,id_eq]
  rw [cosh_eq_centeredCoth hx]
  field_simp
  ring

theorem hasDerivAt_spatialCothFactor2 {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt spatialCothFactor2 (spatialCothFactor3 x) x := by
  have hx0 := hx
  have hs0 := Real.sinh_ne_zero.mpr hx
  have hf := hasDerivAt_centeredCoth hx
  have hd := (((hasDerivAt_const x (1 : ℝ)).div ((Real.hasDerivAt_sinh x).pow 3) (pow_ne_zero 3 hs0)).mul ((((((hasDerivAt_const x (-11 : ℝ)).mul hf).add ((hasDerivAt_const x (-8 : ℝ)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 1) (pow_ne_zero 1 hx0)))).add ((hasDerivAt_const x (20 : ℝ)).mul (hf.pow 3))).add (((hasDerivAt_const x (30 : ℝ)).mul hf).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx0)))).add (((hasDerivAt_const x (48 : ℝ)).mul (hf.pow 2)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 1) (pow_ne_zero 1 hx0)))))
  convert! hd using 1
  dsimp only [spatialCothFactor3,Pi.pow_apply,Pi.div_apply,Pi.mul_apply,Pi.add_apply,id_eq]
  rw [cosh_eq_centeredCoth hx]
  field_simp
  ring

end BrownianAffine
