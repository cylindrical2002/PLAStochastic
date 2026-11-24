import PLAStochastic.Affine.Moments.Optimal.Survival.Spatial.Coefficients

/-! # The actual signed spatial integrals that arise from the Q images -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def imageUnitSquareIntegral (F : ℝ×ℝ → ℝ) : ℝ :=
  ∫ p : ℝ×ℝ in Icc 0 1 ×ˢ Icc 0 1, F p

theorem imageUnitSquareIntegral_eq_interval {F : ℝ×ℝ → ℝ} (hF : Continuous F) :
    imageUnitSquareIntegral F = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, F (x,y) := by
  have hi : IntegrableOn F (Icc 0 1 ×ˢ Icc 0 1) ((volume : Measure ℝ).prod volume) :=
    hF.continuousOn.integrableOn_compact
    (μ := (volume : Measure ℝ).prod volume) (isCompact_Icc.prod isCompact_Icc)
  unfold imageUnitSquareIntegral
  change (∫ p : ℝ×ℝ in Icc 0 1 ×ˢ Icc 0 1, F p ∂(volume : Measure ℝ).prod volume)=_
  rw [setIntegral_prod F hi]
  simp_rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num)]

theorem imageUnitSquareIntegral_add {F G : ℝ×ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) :
    imageUnitSquareIntegral (F+G)=imageUnitSquareIntegral F+imageUnitSquareIntegral G := by
  exact integral_add (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (hG.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))

theorem imageUnitSquareIntegral_sub {F G : ℝ×ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) :
    imageUnitSquareIntegral (F-G)=imageUnitSquareIntegral F-imageUnitSquareIntegral G := by
  exact integral_sub (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (hG.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))

/-- The signed displacement affects L; the endpoint displacement d is held fixed. -/
def optimalImageSpatialSigned (n : ℕ) (T σ η : ℝ) (p : ℝ×ℝ) : ℝ :=
  let L := optimalQImageLength n (σ*p.1) (η*p.2)
  (optimalQImageCoefficientC n*L-optimalQImageCoefficientB n*T)*
    Real.exp (-(L^2-(p.1+p.2-1)^2)/(2*T))

theorem continuous_optimalImageSpatialSigned (n : ℕ) (T σ η : ℝ) :
    Continuous (optimalImageSpatialSigned n T σ η) := by
  unfold optimalImageSpatialSigned optimalQImageLength
  fun_prop

def optimalImageSpatialTerm (n : ℕ) (T : ℝ) : ℝ×ℝ → ℝ :=
  optimalImageSpatialSigned n T 1 1+optimalImageSpatialSigned n T (-1) (-1)-
    optimalImageSpatialSigned n T 1 (-1)-optimalImageSpatialSigned n T (-1) 1

def optimalImageSpatialMode (n : ℕ) (T : ℝ) : ℝ :=
  4/T^2*imageUnitSquareIntegral (optimalImageSpatialTerm n T)

theorem optimalImageSpatialMode_split (n : ℕ) (T : ℝ) :
    optimalImageSpatialMode n T = 4/T^2*(
      imageUnitSquareIntegral (optimalImageSpatialSigned n T 1 1)+
      imageUnitSquareIntegral (optimalImageSpatialSigned n T (-1) (-1))-
      imageUnitSquareIntegral (optimalImageSpatialSigned n T 1 (-1))-
      imageUnitSquareIntegral (optimalImageSpatialSigned n T (-1) 1)) := by
  unfold optimalImageSpatialMode optimalImageSpatialTerm
  have hc := continuous_optimalImageSpatialSigned n T
  rw [imageUnitSquareIntegral_sub (((hc 1 1).add (hc (-1) (-1))).sub (hc 1 (-1))) (hc (-1) 1),
    imageUnitSquareIntegral_sub ((hc 1 1).add (hc (-1) (-1))) (hc 1 (-1)),
    imageUnitSquareIntegral_add (hc 1 1) (hc (-1) (-1))]

theorem integral_optimalImageSpatialSigned_pos_pos (n : ℕ) {T : ℝ} (hT : 0<T) :
    imageUnitSquareIntegral (optimalImageSpatialSigned n T 1 1) =
      (2*((n:ℝ)+1)*optimalQImageCoefficientC n-optimalQImageCoefficientB n*T)*imageEqualSpatialF ((n:ℝ)+1) T-optimalQImageCoefficientC n*imageEqualSpatialD ((n:ℝ)+1) T := by
  rw [imageUnitSquareIntegral_eq_interval (continuous_optimalImageSpatialSigned n T 1 1)]
  have he (x y : ℝ) : optimalImageSpatialSigned n T 1 1 (x,y) =
      (optimalQImageCoefficientC n*(2*((n:ℝ)+1)+1-x-y)-optimalQImageCoefficientB n*T)*
        Real.exp (-((2*((n:ℝ)+1)+1-x-y)^2-(x+y-1)^2)/(2*T)) := by
    dsimp only [optimalImageSpatialSigned,optimalQImageLength]
    congr 1 <;> congr 1 <;> ring
  simp_rw [he]
  exact integral_imageEqual_pos_pos (by positivity : 0<(n:ℝ)+1) hT (optimalQImageCoefficientC n) (optimalQImageCoefficientB n)

theorem integral_optimalImageSpatialSigned_neg_neg (n : ℕ) {T : ℝ} (hT : 0<T) :
    imageUnitSquareIntegral (optimalImageSpatialSigned n T (-1) (-1)) =
      (2*(((n:ℝ)+1)+1)*optimalQImageCoefficientC n-optimalQImageCoefficientB n*T)*imageEqualSpatialF (((n:ℝ)+1)+1) T-optimalQImageCoefficientC n*imageEqualSpatialD (((n:ℝ)+1)+1) T := by
  rw [imageUnitSquareIntegral_eq_interval (continuous_optimalImageSpatialSigned n T (-1) (-1))]
  have he (x y : ℝ) : optimalImageSpatialSigned n T (-1) (-1) (x,y) =
      (optimalQImageCoefficientC n*(2*((n:ℝ)+1)+1+x+y)-optimalQImageCoefficientB n*T)*
        Real.exp (-((2*((n:ℝ)+1)+1+x+y)^2-(x+y-1)^2)/(2*T)) := by
    dsimp only [optimalImageSpatialSigned,optimalQImageLength]
    congr 1 <;> congr 1 <;> ring
  simp_rw [he]
  exact integral_imageEqual_neg_neg (by positivity : 0<(n:ℝ)+1) hT (optimalQImageCoefficientC n) (optimalQImageCoefficientB n)

theorem integral_optimalImageSpatialSigned_pos_neg (n : ℕ) {T : ℝ} (_hT : 0<T) :
    imageUnitSquareIntegral (optimalImageSpatialSigned n T 1 (-1)) =
      (∫ u in ((n:ℝ)+1)..((n:ℝ)+1)+1, ∫ v in ((n:ℝ)+1)..((n:ℝ)+1)+1,
      (optimalQImageCoefficientC n*(u+v)-optimalQImageCoefficientB n*T)*Real.exp (-(2/T)*u*v)) := by
  rw [imageUnitSquareIntegral_eq_interval (continuous_optimalImageSpatialSigned n T 1 (-1))]
  have he (x y : ℝ) : optimalImageSpatialSigned n T 1 (-1) (x,y) =
      (optimalQImageCoefficientC n*(2*((n:ℝ)+1)+1-x+y)-optimalQImageCoefficientB n*T)*
        Real.exp (-((2*((n:ℝ)+1)+1-x+y)^2-(x+y-1)^2)/(2*T)) := by
    dsimp only [optimalImageSpatialSigned,optimalQImageLength]
    congr 1 <;> congr 1 <;> ring
  simp_rw [he]
  exact integral_imageMixed_pos_neg (optimalQImageCoefficientC n) (optimalQImageCoefficientB n)

theorem integral_optimalImageSpatialSigned_neg_pos (n : ℕ) {T : ℝ} (_hT : 0<T) :
    imageUnitSquareIntegral (optimalImageSpatialSigned n T (-1) 1) =
      (∫ u in ((n:ℝ)+1)..((n:ℝ)+1)+1, ∫ v in ((n:ℝ)+1)..((n:ℝ)+1)+1,
      (optimalQImageCoefficientC n*(u+v)-optimalQImageCoefficientB n*T)*Real.exp (-(2/T)*u*v)) := by
  rw [imageUnitSquareIntegral_eq_interval (continuous_optimalImageSpatialSigned n T (-1) 1)]
  have he (x y : ℝ) : optimalImageSpatialSigned n T (-1) 1 (x,y) =
      (optimalQImageCoefficientC n*(2*((n:ℝ)+1)+1+x-y)-optimalQImageCoefficientB n*T)*
        Real.exp (-((2*((n:ℝ)+1)+1+x-y)^2-(x+y-1)^2)/(2*T)) := by
    dsimp only [optimalImageSpatialSigned,optimalQImageLength]
    congr 1 <;> congr 1 <;> ring
  simp_rw [he]
  exact integral_imageMixed_neg_pos (optimalQImageCoefficientC n) (optimalQImageCoefficientB n)

theorem optimalImageSpatialMode_closed (n : ℕ) {T : ℝ} (hT : 0<T) :
    optimalImageSpatialMode n T =
      imageEqualClosed ((n:ℝ)+1) T (optimalQImageCoefficientC n) (optimalQImageCoefficientB n)+
      imageEqualClosed (((n:ℝ)+1)+1) T (optimalQImageCoefficientC n) (optimalQImageCoefficientB n)+
      imageMixedClosed ((n:ℝ)+1) T (optimalQImageCoefficientC n) (optimalQImageCoefficientB n) := by
  rw [optimalImageSpatialMode_split,
    integral_optimalImageSpatialSigned_pos_pos n hT,integral_optimalImageSpatialSigned_neg_neg n hT,
    integral_optimalImageSpatialSigned_pos_neg n hT,integral_optimalImageSpatialSigned_neg_pos n hT]
  rw [← imageEqualSpatial_closed (by positivity : 0<(n:ℝ)+1) hT,
    ← imageEqualSpatial_closed (by positivity : 0<((n:ℝ)+1)+1) hT,
    ← imageMixedSpatial_closed (by positivity : 0<(n:ℝ)+1) hT]
  ring

end BrownianAffine
