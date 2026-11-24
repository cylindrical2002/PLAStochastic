import PLAStochastic.Affine.Moments.Optimal.Spatial.CothFactors
import PLAStochastic.Affine.Moments.Optimal.Laplace.ConvolutionLaplace

/-! # Actual parameter derivatives of the spatial Laplace kernel -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

def spatialKernelWeight0 (x a b : ℝ) : ℝ :=
  ((Real.sinh (x*(1-a)))*(Real.sinh (x*b)))

def spatialKernelWeight1 (x a b : ℝ) : ℝ :=
  ((b*(Real.cosh (x*b))*(Real.sinh (x*(1-a)))) + ((Real.cosh (x*(1-a)))*(Real.sinh (x*b))*(1-a)))

def spatialKernelWeight2 (x a b : ℝ) : ℝ :=
  (((Real.sinh (x*(1-a)))*(Real.sinh (x*b))*((b^2) + ((1-a)^2))) + (2*b*(Real.cosh (x*(1-a)))*(Real.cosh (x*b))*(1-a)))

def spatialKernelWeight3 (x a b : ℝ) : ℝ :=
  (((Real.cosh (x*(1-a)))*(Real.sinh (x*b))*(((1-a)^3) + (3*(1-a)*(b^2)))) + ((Real.cosh (x*b))*(Real.sinh (x*(1-a)))*((b^3) + (3*b*((1-a)^2)))))

theorem hasDerivAt_spatialKernelWeight0 (x a b : ℝ) :
    HasDerivAt (spatialKernelWeight0 · a b) (spatialKernelWeight1 x a b) x := by
  have hd := (((Real.hasDerivAt_sinh (x*(1-a))).comp x ((hasDerivAt_id x).mul_const (1-a))).mul ((Real.hasDerivAt_sinh (x*b)).comp x ((hasDerivAt_id x).mul_const b)))
  convert! hd using 1
  dsimp only [spatialKernelWeight1,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,Function.comp_def,id_eq]
  ring

theorem hasDerivAt_spatialKernelWeight1 (x a b : ℝ) :
    HasDerivAt (spatialKernelWeight1 · a b) (spatialKernelWeight2 x a b) x := by
  have hd := ((((hasDerivAt_const x (b : ℝ)).mul ((Real.hasDerivAt_cosh (x*b)).comp x ((hasDerivAt_id x).mul_const b))).mul ((Real.hasDerivAt_sinh (x*(1-a))).comp x ((hasDerivAt_id x).mul_const (1-a)))).add ((((Real.hasDerivAt_cosh (x*(1-a))).comp x ((hasDerivAt_id x).mul_const (1-a))).mul ((Real.hasDerivAt_sinh (x*b)).comp x ((hasDerivAt_id x).mul_const b))).mul (hasDerivAt_const x ((1-a) : ℝ))))
  convert! hd using 1
  dsimp only [spatialKernelWeight2,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,Function.comp_def,id_eq]
  ring

theorem hasDerivAt_spatialKernelWeight2 (x a b : ℝ) :
    HasDerivAt (spatialKernelWeight2 · a b) (spatialKernelWeight3 x a b) x := by
  have hd := (((((Real.hasDerivAt_sinh (x*(1-a))).comp x ((hasDerivAt_id x).mul_const (1-a))).mul ((Real.hasDerivAt_sinh (x*b)).comp x ((hasDerivAt_id x).mul_const b))).mul (((hasDerivAt_const x (b : ℝ)).pow 2).add ((hasDerivAt_const x ((1-a) : ℝ)).pow 2))).add (((((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_const x (b : ℝ))).mul ((Real.hasDerivAt_cosh (x*(1-a))).comp x ((hasDerivAt_id x).mul_const (1-a)))).mul ((Real.hasDerivAt_cosh (x*b)).comp x ((hasDerivAt_id x).mul_const b))).mul (hasDerivAt_const x ((1-a) : ℝ))))
  convert! hd using 1
  dsimp only [spatialKernelWeight3,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,Function.comp_def,id_eq]
  norm_num only
  ring

def spatialKernelDerivative0 (x a b : ℝ) : ℝ :=
  (8*(spatialCothFactor0 x)*(spatialKernelWeight0 x a b))

def spatialKernelDerivative1 (x a b : ℝ) : ℝ :=
  ((8*(spatialCothFactor0 x)*(spatialKernelWeight1 x a b)) + (8*(spatialCothFactor1 x)*(spatialKernelWeight0 x a b)))

def spatialKernelDerivative2 (x a b : ℝ) : ℝ :=
  ((8*(spatialCothFactor0 x)*(spatialKernelWeight2 x a b)) + (8*(spatialCothFactor2 x)*(spatialKernelWeight0 x a b)) + (16*(spatialCothFactor1 x)*(spatialKernelWeight1 x a b)))

def spatialKernelDerivative3 (x a b : ℝ) : ℝ :=
  ((8*(spatialCothFactor0 x)*(spatialKernelWeight3 x a b)) + (8*(spatialCothFactor3 x)*(spatialKernelWeight0 x a b)) + (24*(spatialCothFactor1 x)*(spatialKernelWeight2 x a b)) + (24*(spatialCothFactor2 x)*(spatialKernelWeight1 x a b)))

theorem hasDerivAt_spatialKernelDerivative0 {x : ℝ} (hx : x ≠ 0) (a b : ℝ) :
    HasDerivAt (spatialKernelDerivative0 · a b) (spatialKernelDerivative1 x a b) x := by
  have hd := (((hasDerivAt_const x (8 : ℝ)).mul (hasDerivAt_spatialCothFactor0 hx)).mul (hasDerivAt_spatialKernelWeight0 x a b))
  convert! hd using 1
  dsimp only [spatialKernelDerivative1,Pi.add_apply,Pi.mul_apply,id_eq]
  ring

theorem hasDerivAt_spatialKernelDerivative1 {x : ℝ} (hx : x ≠ 0) (a b : ℝ) :
    HasDerivAt (spatialKernelDerivative1 · a b) (spatialKernelDerivative2 x a b) x := by
  have hd := ((((hasDerivAt_const x (8 : ℝ)).mul (hasDerivAt_spatialCothFactor0 hx)).mul (hasDerivAt_spatialKernelWeight1 x a b)).add (((hasDerivAt_const x (8 : ℝ)).mul (hasDerivAt_spatialCothFactor1 hx)).mul (hasDerivAt_spatialKernelWeight0 x a b)))
  convert! hd using 1
  dsimp only [spatialKernelDerivative2,Pi.add_apply,Pi.mul_apply,id_eq]
  ring

theorem hasDerivAt_spatialKernelDerivative2 {x : ℝ} (hx : x ≠ 0) (a b : ℝ) :
    HasDerivAt (spatialKernelDerivative2 · a b) (spatialKernelDerivative3 x a b) x := by
  have hd := (((((hasDerivAt_const x (8 : ℝ)).mul (hasDerivAt_spatialCothFactor0 hx)).mul (hasDerivAt_spatialKernelWeight2 x a b)).add (((hasDerivAt_const x (8 : ℝ)).mul (hasDerivAt_spatialCothFactor2 hx)).mul (hasDerivAt_spatialKernelWeight0 x a b))).add (((hasDerivAt_const x (16 : ℝ)).mul (hasDerivAt_spatialCothFactor1 hx)).mul (hasDerivAt_spatialKernelWeight1 x a b)))
  convert! hd using 1
  dsimp only [spatialKernelDerivative3,Pi.add_apply,Pi.mul_apply,id_eq]
  ring

def spatialLaplaceFormula0 (x a b : ℝ) : ℝ :=
  (spatialKernelDerivative0 x a b)

def spatialLaplaceFormula1 (x a b : ℝ) : ℝ :=
  (-1*(spatialKernelDerivative1 x a b)*(1/x^1))

def spatialLaplaceFormula2 (x a b : ℝ) : ℝ :=
  (((spatialKernelDerivative2 x a b)*(1/x^2)) + (-1*(spatialKernelDerivative1 x a b)*(1/x^3)))

def spatialLaplaceFormula3 (x a b : ℝ) : ℝ :=
  ((-1*(spatialKernelDerivative3 x a b)*(1/x^3)) + (-3*(spatialKernelDerivative1 x a b)*(1/x^5)) + (3*(spatialKernelDerivative2 x a b)*(1/x^4)))

theorem hasDerivAt_spatialLaplaceFormula0 {x : ℝ} (hx : x ≠ 0) (a b : ℝ) :
    HasDerivAt (spatialLaplaceFormula0 · a b) (-x*spatialLaplaceFormula1 x a b) x := by
  have hd := (hasDerivAt_spatialKernelDerivative0 hx a b)
  convert! hd using 1
  dsimp only [spatialLaplaceFormula1,Pi.add_apply,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,Function.comp_def,id_eq]
  field_simp

theorem hasDerivAt_spatialLaplaceFormula1 {x : ℝ} (hx : x ≠ 0) (a b : ℝ) :
    HasDerivAt (spatialLaplaceFormula1 · a b) (-x*spatialLaplaceFormula2 x a b) x := by
  have hd := (((hasDerivAt_const x (-1 : ℝ)).mul (hasDerivAt_spatialKernelDerivative1 hx a b)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 1) (pow_ne_zero 1 hx)))
  convert! hd using 1
  dsimp only [spatialLaplaceFormula2,Pi.add_apply,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,Function.comp_def,id_eq]
  field_simp
  ring

theorem hasDerivAt_spatialLaplaceFormula2 {x : ℝ} (hx : x ≠ 0) (a b : ℝ) :
    HasDerivAt (spatialLaplaceFormula2 · a b) (-x*spatialLaplaceFormula3 x a b) x := by
  have hd := (((hasDerivAt_spatialKernelDerivative2 hx a b).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx))).add (((hasDerivAt_const x (-1 : ℝ)).mul (hasDerivAt_spatialKernelDerivative1 hx a b)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx))))
  convert! hd using 1
  dsimp only [spatialLaplaceFormula3,Pi.add_apply,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,Function.comp_def,id_eq]
  field_simp
  ring

theorem spatialLaplaceFormula0_eq (x a b : ℝ) :
    spatialLaplaceFormula0 x a b=optimalMomentLaplaceKernel x a b := by
  unfold spatialLaplaceFormula0 spatialKernelDerivative0 spatialCothFactor0 spatialKernelWeight0 optimalMomentLaplaceKernel
  ring

theorem continuous_spatialLaplaceFormula0 (x : ℝ) :
    Continuous (fun p : ℝ×ℝ => spatialLaplaceFormula0 x p.1 p.2) := by
  unfold spatialLaplaceFormula0 spatialKernelDerivative0 spatialCothFactor0 spatialKernelWeight0
  fun_prop

theorem continuousOn_spatialLaplaceFormula0 :
    ContinuousOn (fun p : ℝ×(ℝ×ℝ) => spatialLaplaceFormula0 p.1 p.2.1 p.2.2)
      (Ioi 0 ×ˢ Set.univ) := by
  intro p hp
  have hx : 0 < p.1 := hp.1
  have hx0 := hx.ne'
  have hs0 := Real.sinh_ne_zero.mpr hx0
  have hcf : ContinuousAt (fun p : ℝ×(ℝ×ℝ) => centeredCoth p.1) p :=
    (hasDerivAt_centeredCoth hx0).continuousAt.comp continuous_fst.continuousAt
  apply ContinuousAt.continuousWithinAt
  unfold spatialLaplaceFormula0 spatialKernelDerivative0 spatialCothFactor0 spatialKernelWeight0
  fun_prop (disch := first | assumption | positivity)

theorem continuous_spatialLaplaceFormula1 (x : ℝ) :
    Continuous (fun p : ℝ×ℝ => spatialLaplaceFormula1 x p.1 p.2) := by
  unfold spatialLaplaceFormula1 spatialKernelDerivative1 spatialCothFactor0 spatialKernelWeight0 spatialCothFactor1 spatialKernelWeight1
  fun_prop

theorem continuousOn_spatialLaplaceFormula1 :
    ContinuousOn (fun p : ℝ×(ℝ×ℝ) => spatialLaplaceFormula1 p.1 p.2.1 p.2.2)
      (Ioi 0 ×ˢ Set.univ) := by
  intro p hp
  have hx : 0 < p.1 := hp.1
  have hx0 := hx.ne'
  have hs0 := Real.sinh_ne_zero.mpr hx0
  have hcf : ContinuousAt (fun p : ℝ×(ℝ×ℝ) => centeredCoth p.1) p :=
    (hasDerivAt_centeredCoth hx0).continuousAt.comp continuous_fst.continuousAt
  apply ContinuousAt.continuousWithinAt
  unfold spatialLaplaceFormula1 spatialKernelDerivative1 spatialCothFactor0 spatialKernelWeight0 spatialCothFactor1 spatialKernelWeight1
  fun_prop (disch := first | assumption | positivity)

theorem continuous_spatialLaplaceFormula2 (x : ℝ) :
    Continuous (fun p : ℝ×ℝ => spatialLaplaceFormula2 x p.1 p.2) := by
  unfold spatialLaplaceFormula2 spatialKernelDerivative1 spatialKernelDerivative2 spatialCothFactor0 spatialKernelWeight0 spatialCothFactor1 spatialKernelWeight1 spatialCothFactor2 spatialKernelWeight2
  fun_prop

theorem continuousOn_spatialLaplaceFormula2 :
    ContinuousOn (fun p : ℝ×(ℝ×ℝ) => spatialLaplaceFormula2 p.1 p.2.1 p.2.2)
      (Ioi 0 ×ˢ Set.univ) := by
  intro p hp
  have hx : 0 < p.1 := hp.1
  have hx0 := hx.ne'
  have hs0 := Real.sinh_ne_zero.mpr hx0
  have hcf : ContinuousAt (fun p : ℝ×(ℝ×ℝ) => centeredCoth p.1) p :=
    (hasDerivAt_centeredCoth hx0).continuousAt.comp continuous_fst.continuousAt
  apply ContinuousAt.continuousWithinAt
  unfold spatialLaplaceFormula2 spatialKernelDerivative1 spatialKernelDerivative2 spatialCothFactor0 spatialKernelWeight0 spatialCothFactor1 spatialKernelWeight1 spatialCothFactor2 spatialKernelWeight2
  fun_prop (disch := first | assumption | positivity)

theorem continuous_spatialLaplaceFormula3 (x : ℝ) :
    Continuous (fun p : ℝ×ℝ => spatialLaplaceFormula3 x p.1 p.2) := by
  unfold spatialLaplaceFormula3 spatialKernelDerivative1 spatialKernelDerivative2 spatialKernelDerivative3 spatialCothFactor0 spatialKernelWeight0 spatialCothFactor1 spatialKernelWeight1 spatialCothFactor2 spatialKernelWeight2 spatialCothFactor3 spatialKernelWeight3
  fun_prop

theorem continuousOn_spatialLaplaceFormula3 :
    ContinuousOn (fun p : ℝ×(ℝ×ℝ) => spatialLaplaceFormula3 p.1 p.2.1 p.2.2)
      (Ioi 0 ×ˢ Set.univ) := by
  intro p hp
  have hx : 0 < p.1 := hp.1
  have hx0 := hx.ne'
  have hs0 := Real.sinh_ne_zero.mpr hx0
  have hcf : ContinuousAt (fun p : ℝ×(ℝ×ℝ) => centeredCoth p.1) p :=
    (hasDerivAt_centeredCoth hx0).continuousAt.comp continuous_fst.continuousAt
  apply ContinuousAt.continuousWithinAt
  unfold spatialLaplaceFormula3 spatialKernelDerivative1 spatialKernelDerivative2 spatialKernelDerivative3 spatialCothFactor0 spatialKernelWeight0 spatialCothFactor1 spatialKernelWeight1 spatialCothFactor2 spatialKernelWeight2 spatialCothFactor3 spatialKernelWeight3
  fun_prop (disch := first | assumption | positivity)

end BrownianAffine
