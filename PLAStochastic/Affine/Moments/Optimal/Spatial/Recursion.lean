import PLAStochastic.Affine.Moments.Optimal.Spatial.GeneratingIntegral
import PLAStochastic.Affine.Moments.Optimal.Spatial.DifferenceMoments
import PLAStochastic.Affine.Moments.Optimal.Spatial.CothFactors

/-! # Three genuine partial derivatives with the spatial weight held fixed -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

def optimalSpatialWeight0 (x h : ℝ) : ℝ :=
  (((Real.exp (-h))*((spatialDifferenceMoment 0 x h)^2)) + ((Real.exp h)*((spatialDifferenceMoment 0 x (-h))^2)))

def optimalSpatialWeight1 (x h : ℝ) : ℝ :=
  ((2*(spatialDifferenceMoment 0 x h)*(spatialDifferenceMoment 1 x h)*(Real.exp (-h))) + (2*(spatialDifferenceMoment 0 x (-h))*(spatialDifferenceMoment 1 x (-h))*(Real.exp h)))

def optimalSpatialWeight2 (x h : ℝ) : ℝ :=
  ((2*(Real.exp (-h))*(((spatialDifferenceMoment 1 x h)^2) + ((spatialDifferenceMoment 0 x h)*(spatialDifferenceMoment 2 x h)))) + (2*(Real.exp h)*(((spatialDifferenceMoment 1 x (-h))^2) + ((spatialDifferenceMoment 0 x (-h))*(spatialDifferenceMoment 2 x (-h))))))

def optimalSpatialWeight3 (x h : ℝ) : ℝ :=
  ((2*(Real.exp (-h))*(((spatialDifferenceMoment 0 x h)*(spatialDifferenceMoment 3 x h)) + (3*(spatialDifferenceMoment 1 x h)*(spatialDifferenceMoment 2 x h)))) + (2*(Real.exp h)*(((spatialDifferenceMoment 0 x (-h))*(spatialDifferenceMoment 3 x (-h))) + (3*(spatialDifferenceMoment 1 x (-h))*(spatialDifferenceMoment 2 x (-h))))))

theorem hasDerivAt_optimalSpatialWeight0 (x h : ℝ) :
    HasDerivAt (optimalSpatialWeight0 · h) (optimalSpatialWeight1 x h) x := by
  have hd := (((hasDerivAt_const x ((Real.exp (-h)) : ℝ)).mul ((hasDerivAt_spatialDifferenceMoment 0 x h).pow 2)).add ((hasDerivAt_const x ((Real.exp h) : ℝ)).mul ((hasDerivAt_spatialDifferenceMoment 0 x (-h)).pow 2)))
  convert! hd using 1
  dsimp only [optimalSpatialWeight1,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id_eq]
  norm_num only
  ring

theorem hasDerivAt_optimalSpatialWeight1 (x h : ℝ) :
    HasDerivAt (optimalSpatialWeight1 · h) (optimalSpatialWeight2 x h) x := by
  have hd := (((((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_spatialDifferenceMoment 0 x h)).mul (hasDerivAt_spatialDifferenceMoment 1 x h)).mul (hasDerivAt_const x ((Real.exp (-h)) : ℝ))).add ((((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_spatialDifferenceMoment 0 x (-h))).mul (hasDerivAt_spatialDifferenceMoment 1 x (-h))).mul (hasDerivAt_const x ((Real.exp h) : ℝ))))
  convert! hd using 1
  dsimp only [optimalSpatialWeight2,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id_eq]
  norm_num only
  ring

theorem hasDerivAt_optimalSpatialWeight2 (x h : ℝ) :
    HasDerivAt (optimalSpatialWeight2 · h) (optimalSpatialWeight3 x h) x := by
  have hd := ((((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_const x ((Real.exp (-h)) : ℝ))).mul (((hasDerivAt_spatialDifferenceMoment 1 x h).pow 2).add ((hasDerivAt_spatialDifferenceMoment 0 x h).mul (hasDerivAt_spatialDifferenceMoment 2 x h)))).add (((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_const x ((Real.exp h) : ℝ))).mul (((hasDerivAt_spatialDifferenceMoment 1 x (-h)).pow 2).add ((hasDerivAt_spatialDifferenceMoment 0 x (-h)).mul (hasDerivAt_spatialDifferenceMoment 2 x (-h))))))
  convert! hd using 1
  dsimp only [optimalSpatialWeight3,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id_eq]
  norm_num only
  ring

def optimalSpatialDerivative0 (x h : ℝ) : ℝ :=
  ((spatialCothFactor0 x)*(optimalSpatialWeight0 x h))

def optimalSpatialDerivative1 (x h : ℝ) : ℝ :=
  (((spatialCothFactor0 x)*(optimalSpatialWeight1 x h)) + ((spatialCothFactor1 x)*(optimalSpatialWeight0 x h)))

def optimalSpatialDerivative2 (x h : ℝ) : ℝ :=
  (((spatialCothFactor0 x)*(optimalSpatialWeight2 x h)) + ((spatialCothFactor2 x)*(optimalSpatialWeight0 x h)) + (2*(spatialCothFactor1 x)*(optimalSpatialWeight1 x h)))

def optimalSpatialDerivative3 (x h : ℝ) : ℝ :=
  (((spatialCothFactor0 x)*(optimalSpatialWeight3 x h)) + ((spatialCothFactor3 x)*(optimalSpatialWeight0 x h)) + (3*(spatialCothFactor1 x)*(optimalSpatialWeight2 x h)) + (3*(spatialCothFactor2 x)*(optimalSpatialWeight1 x h)))

theorem hasDerivAt_optimalSpatialDerivative0 {x : ℝ} (hx : x ≠ 0) (h : ℝ) :
    HasDerivAt (optimalSpatialDerivative0 · h) (optimalSpatialDerivative1 x h) x := by
  have hd := ((hasDerivAt_spatialCothFactor0 hx).mul (hasDerivAt_optimalSpatialWeight0 x h))
  convert! hd using 1
  dsimp only [optimalSpatialDerivative1,Pi.add_apply,Pi.mul_apply,id_eq]
  ring

theorem hasDerivAt_optimalSpatialDerivative1 {x : ℝ} (hx : x ≠ 0) (h : ℝ) :
    HasDerivAt (optimalSpatialDerivative1 · h) (optimalSpatialDerivative2 x h) x := by
  have hd := (((hasDerivAt_spatialCothFactor0 hx).mul (hasDerivAt_optimalSpatialWeight1 x h)).add ((hasDerivAt_spatialCothFactor1 hx).mul (hasDerivAt_optimalSpatialWeight0 x h)))
  convert! hd using 1
  dsimp only [optimalSpatialDerivative2,Pi.add_apply,Pi.mul_apply,id_eq]
  ring

theorem hasDerivAt_optimalSpatialDerivative2 {x : ℝ} (hx : x ≠ 0) (h : ℝ) :
    HasDerivAt (optimalSpatialDerivative2 · h) (optimalSpatialDerivative3 x h) x := by
  have hd := ((((hasDerivAt_spatialCothFactor0 hx).mul (hasDerivAt_optimalSpatialWeight2 x h)).add ((hasDerivAt_spatialCothFactor2 hx).mul (hasDerivAt_optimalSpatialWeight0 x h))).add (((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_spatialCothFactor1 hx)).mul (hasDerivAt_optimalSpatialWeight1 x h)))
  convert! hd using 1
  dsimp only [optimalSpatialDerivative3,Pi.add_apply,Pi.mul_apply,id_eq]
  ring

def optimalSpatialFormula0 (x h : ℝ) : ℝ :=
  (optimalSpatialDerivative0 x h)

def optimalSpatialFormula1 (x h : ℝ) : ℝ :=
  (-1*(optimalSpatialDerivative1 x h)*(1/x^1))

def optimalSpatialFormula2 (x h : ℝ) : ℝ :=
  (((optimalSpatialDerivative2 x h)*(1/x^2)) + (-1*(optimalSpatialDerivative1 x h)*(1/x^3)))

def optimalSpatialFormula3 (x h : ℝ) : ℝ :=
  ((-1*(optimalSpatialDerivative3 x h)*(1/x^3)) + (-3*(optimalSpatialDerivative1 x h)*(1/x^5)) + (3*(optimalSpatialDerivative2 x h)*(1/x^4)))

theorem hasDerivAt_optimalSpatialFormula0 {x : ℝ} (hx : x ≠ 0) (h : ℝ) :
    HasDerivAt (optimalSpatialFormula0 · h) (-x*optimalSpatialFormula1 x h) x := by
  have hd := (hasDerivAt_optimalSpatialDerivative0 hx h)
  convert! hd using 1
  dsimp only [optimalSpatialFormula1,Pi.add_apply,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,id_eq]
  field_simp

theorem hasDerivAt_optimalSpatialFormula1 {x : ℝ} (hx : x ≠ 0) (h : ℝ) :
    HasDerivAt (optimalSpatialFormula1 · h) (-x*optimalSpatialFormula2 x h) x := by
  have hd := (((hasDerivAt_const x (-1 : ℝ)).mul (hasDerivAt_optimalSpatialDerivative1 hx h)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 1) (pow_ne_zero 1 hx)))
  convert! hd using 1
  dsimp only [optimalSpatialFormula2,Pi.add_apply,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,id_eq]
  field_simp
  all_goals ring

theorem hasDerivAt_optimalSpatialFormula2 {x : ℝ} (hx : x ≠ 0) (h : ℝ) :
    HasDerivAt (optimalSpatialFormula2 · h) (-x*optimalSpatialFormula3 x h) x := by
  have hd := (((hasDerivAt_optimalSpatialDerivative2 hx h).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx))).add (((hasDerivAt_const x (-1 : ℝ)).mul (hasDerivAt_optimalSpatialDerivative1 hx h)).mul ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx))))
  convert! hd using 1
  dsimp only [optimalSpatialFormula3,Pi.add_apply,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,id_eq]
  field_simp
  all_goals ring

/-- Literal spatial recursion from the manuscript. The second parameter remains fixed. -/
def optimalSpatialB : ℕ → ℝ → ℝ → ℝ
  | 0, k, h => 8*centeredCoth k/Real.sinh k^3*optimalSpatialGenerating k h
  | n+1, k, h => -deriv (optimalSpatialB n · h) k/k

theorem optimalSpatialB_zero (k h : ℝ) : optimalSpatialB 0 k h=optimalSpatialFormula0 k h := by
  rw [optimalSpatialB,optimalSpatialGenerating_eq_exponentialMoments]
  simp only [optimalSpatialFormula0,optimalSpatialDerivative0,spatialCothFactor0,optimalSpatialWeight0,spatialDifferenceMoment,pow_zero,one_mul,←sub_eq_add_neg]
  ring

theorem optimalSpatialB_one {k : ℝ} (hk : k ≠ 0) (h : ℝ) :
    optimalSpatialB 1 k h=optimalSpatialFormula1 k h := by
  have he : (optimalSpatialB 0 · h) =ᶠ[𝓝 k] (optimalSpatialFormula0 · h) := by
    exact Eventually.of_forall fun x => optimalSpatialB_zero x h
  have hd := (hasDerivAt_optimalSpatialFormula0 hk h).congr_of_eventuallyEq he
  change -deriv (optimalSpatialB 0 · h) k/k=_
  rw [hd.deriv]
  field_simp

theorem optimalSpatialB_two {k : ℝ} (hk : k ≠ 0) (h : ℝ) :
    optimalSpatialB 2 k h=optimalSpatialFormula2 k h := by
  have he : (optimalSpatialB 1 · h) =ᶠ[𝓝 k] (optimalSpatialFormula1 · h) := by
    filter_upwards [eventually_ne_nhds hk] with x hx
    exact optimalSpatialB_one hx h
  have hd := (hasDerivAt_optimalSpatialFormula1 hk h).congr_of_eventuallyEq he
  change -deriv (optimalSpatialB 1 · h) k/k=_
  rw [hd.deriv]
  field_simp

theorem optimalSpatialB_three {k : ℝ} (hk : k ≠ 0) (h : ℝ) :
    optimalSpatialB 3 k h=optimalSpatialFormula3 k h := by
  have he : (optimalSpatialB 2 · h) =ᶠ[𝓝 k] (optimalSpatialFormula2 · h) := by
    filter_upwards [eventually_ne_nhds hk] with x hx
    exact optimalSpatialB_two hx h
  have hd := (hasDerivAt_optimalSpatialFormula2 hk h).congr_of_eventuallyEq he
  change -deriv (optimalSpatialB 2 · h) k/k=_
  rw [hd.deriv]
  field_simp

end BrownianAffine
