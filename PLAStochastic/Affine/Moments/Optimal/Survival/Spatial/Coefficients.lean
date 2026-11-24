import PLAStochastic.Affine.Moments.Optimal.Survival.Spatial.EqualSign
import PLAStochastic.Affine.Moments.Optimal.Survival.Spatial.MixedSign
import PLAStochastic.Affine.Moments.Optimal.Survival.QImage.Geometric

/-! # The coefficients obtained by genuine spatial integration of each image -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def imageEqualLowerCoefficient (m T c b : ℝ) : ℝ :=
  (2*m-1)*c/m^2-b*T/m^2+c*T/m^3

def imageEqualMiddleCoefficient (m T c b : ℝ) : ℝ :=
  -4*c/m+2*b*T/m^2-2*c*T/m^3

def imageEqualUpperCoefficient (m T c b : ℝ) : ℝ :=
  (2*m+1)*c/m^2-b*T/m^2+c*T/m^3

def imageEqualClosed (m T c b : ℝ) : ℝ :=
  imageEqualLowerCoefficient m T c b*Real.exp (-2*m*(m-1)/T)+
  imageEqualMiddleCoefficient m T c b*Real.exp (-2*m^2/T)+
  imageEqualUpperCoefficient m T c b*Real.exp (-2*m*(m+1)/T)

theorem imageEqualSpatial_closed {m T : ℝ} (hm : 0<m) (hT : 0<T) (c b : ℝ) :
    4/T^2*((2*m*c-b*T)*imageEqualSpatialF m T-c*imageEqualSpatialD m T)=
      imageEqualClosed m T c b := by
  have hp : Real.exp (-2*m^2/T)*Real.exp (2*m/T)=Real.exp (-2*m*(m-1)/T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hn : Real.exp (-2*m^2/T)*Real.exp (-(2*m/T))=Real.exp (-2*m*(m+1)/T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = imageEqualLowerCoefficient m T c b*(Real.exp (-2*m^2/T)*Real.exp (2*m/T))+
        imageEqualMiddleCoefficient m T c b*Real.exp (-2*m^2/T)+
        imageEqualUpperCoefficient m T c b*(Real.exp (-2*m^2/T)*Real.exp (-(2*m/T))) := by
      unfold imageEqualSpatialF imageEqualSpatialD imageEqualF imageEqualD
        imageEqualLowerCoefficient imageEqualMiddleCoefficient imageEqualUpperCoefficient
      rw [Real.cosh_eq]
      field_simp
      ring
    _ = _ := by rw [hp,hn]; rfl

/-- The mixed contribution already includes both opposite-sign images and the factor 4/T². -/
def imageMixedClosed (m T c b : ℝ) : ℝ :=
  -4*c*(Real.exp (-2*m^2/T)/m-(1/m+1/(m+1))*Real.exp (-2*m*(m+1)/T)+
    Real.exp (-2*(m+1)^2/T)/(m+1))+
  4*b*(exponentialIntegralE1 (2*m^2/T)-2*exponentialIntegralE1 (2*m*(m+1)/T)+
    exponentialIntegralE1 (2*(m+1)^2/T))

theorem imageMixedSpatial_closed {m T : ℝ} (hm : 0<m) (hT : 0<T) (c b : ℝ) :
    -(8/T^2)*(∫ u in m..m+1, ∫ v in m..m+1,
      (c*(u+v)-b*T)*Real.exp (-(2/T)*u*v))=imageMixedClosed m T c b := by
  rw [integral_imageMixed_J hm hT]
  unfold imageMixedClosed
  have h₁ : -(2/T)*m^2= -2*m^2/T := by ring
  have h₂ : -(2/T)*m*(m+1)= -2*m*(m+1)/T := by ring
  have h₃ : -(2/T)*(m+1)^2= -2*(m+1)^2/T := by ring
  have h₄ : (2/T)*m^2=2*m^2/T := by ring
  have h₅ : (2/T)*m*(m+1)=2*m*(m+1)/T := by ring
  have h₆ : (2/T)*(m+1)^2=2*(m+1)^2/T := by ring
  rw [h₁,h₂,h₃,h₄,h₅,h₆]
  field_simp
  ring

end BrownianAffine
