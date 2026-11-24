import PLAStochastic.Affine.Moments.Optimal.Survival.Spatial.Boundary

/-! # Polynomial identities for collecting square and consecutive-product images -/
noncomputable section
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem imageCoefficient_collection_square {m : ℝ} (hm : m≠0) (T : ℝ) :
    imageEqualMiddleCoefficient m T (m*(m+1)*(2*m+1)/6) (m*(m+1)/2)-
      4*(m*(m+1)*(2*m+1)/6)/m+
    imageEqualMiddleCoefficient m T ((m-1)*m*(2*m-1)/6) ((m-1)*m/2)-
      4*((m-1)*m*(2*m-1)/6)/m =
    -8*(2*m^2+1)/3+(4*T)/6*(1-1/m^2) := by
  unfold imageEqualMiddleCoefficient
  field_simp
  ring

theorem imageCoefficient_collection_product {m : ℝ} (hm : 0<m) (T : ℝ) :
    imageEqualUpperCoefficient m T (m*(m+1)*(2*m+1)/6) (m*(m+1)/2)+
    imageEqualLowerCoefficient (m+1) T (m*(m+1)*(2*m+1)/6) (m*(m+1)/2)+
    4*(m*(m+1)*(2*m+1)/6)*(1/m+1/(m+1))+
    imageEqualUpperCoefficient m T ((m-1)*m*(2*m-1)/6) ((m-1)*m/2)+
    imageEqualLowerCoefficient (m+1) T ((m+1)*(m+2)*(2*m+3)/6) ((m+1)*(m+2)/2) =
    (2*m+1)^4/(3*m*(m+1))+(4*T)/12*(-2+1/m^2+1/(m+1)^2) := by
  have hmp : m+1≠0 := by positivity
  unfold imageEqualUpperCoefficient imageEqualLowerCoefficient
  field_simp
  ring

theorem optimalImageCoefficientA_collection (n : ℕ) (T : ℝ) :
    imageEqualMiddleCoefficient ((n:ℝ)+1) T (optimalQImageCoefficientC n) (optimalQImageCoefficientB n)-
      4*optimalQImageCoefficientC n/((n:ℝ)+1)+
    imageEqualMiddleCoefficient ((n:ℝ)+1) T (optimalQImagePreviousC n) (optimalQImagePreviousB n)-
      4*optimalQImagePreviousC n/((n:ℝ)+1) = optimalImageCoefficientA n (4*T) := by
  convert! imageCoefficient_collection_square (by positivity : (n:ℝ)+1≠0) T using 1
  dsimp only [optimalQImageCoefficientC,optimalQImageCoefficientB,optimalQImagePreviousC,
      optimalQImagePreviousB,optimalImageCoefficientA,imageEqualMiddleCoefficient]
  ring_nf

theorem optimalImageCoefficientB_collection (n : ℕ) (T : ℝ) :
    imageEqualUpperCoefficient ((n:ℝ)+1) T (optimalQImageCoefficientC n) (optimalQImageCoefficientB n)+
    imageEqualLowerCoefficient (((n:ℝ)+1)+1) T (optimalQImageCoefficientC n) (optimalQImageCoefficientB n)+
    4*optimalQImageCoefficientC n*(1/((n:ℝ)+1)+1/(((n:ℝ)+1)+1))+
    imageEqualUpperCoefficient ((n:ℝ)+1) T (optimalQImagePreviousC n) (optimalQImagePreviousB n)+
    imageEqualLowerCoefficient (((n:ℝ)+1)+1) T (optimalQImageCoefficientC (n+1)) (optimalQImageCoefficientB (n+1)) =
      optimalImageCoefficientB n (4*T) := by
  convert! imageCoefficient_collection_product (by positivity : 0<(n:ℝ)+1) T using 1
  dsimp only [optimalQImageCoefficientC,optimalQImageCoefficientB,optimalQImagePreviousC,
      optimalQImagePreviousB,optimalImageCoefficientB,imageEqualUpperCoefficient,imageEqualLowerCoefficient]
  push_cast
  ring_nf

end BrownianAffine
