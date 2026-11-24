import PLAStochastic.Affine.Process.Killed.Boundary.Identities

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem heatSpatialMode_width_scaling {r : ℝ} (hr : r ≠ 0)
    (a b n : ℕ) (t x z : ℝ) :
    heatSpatialMode r a b n (r^2*t) (r*x) (r*z)=
      (r^(a+b+1))⁻¹ * heatSpatialMode 1 a b n t x z := by
  have hf : heatFrequency r n=heatFrequency 1 n/r := by
    simp only [heatFrequency,div_one]
    ring
  have hx : heatFrequency r n*(r*x)=heatFrequency 1 n*x := by rw [hf]; field_simp
  have hz : heatFrequency r n*(r*z)=heatFrequency 1 n*z := by rw [hf]; field_simp
  have ht : -(heatFrequency r n^2)*(r^2*t)/2=-(heatFrequency 1 n^2)*t/2 := by
    rw [hf]
    field_simp
  have hc : 2/r*heatFrequency r n^(a+b)=(r^(a+b+1))⁻¹*(2/1*heatFrequency 1 n^(a+b)) := by
    rw [hf,div_pow,pow_succ,div_one,mul_inv_rev]
    ring
  simp only [heatSpatialMode,hx,hz,ht,hc]
  ring

theorem heatSpatialSeries_width_scaling {r : ℝ} (hr : r ≠ 0)
    (a b : ℕ) (t x z : ℝ) :
    heatSpatialSeries r a b (r^2*t) (r*x) (r*z)=
      (r^(a+b+1))⁻¹ * heatSpatialSeries 1 a b t x z := by
  simp only [heatSpatialSeries,heatSpatialMode_width_scaling hr]
  exact tsum_mul_left

theorem heatBoundaryLeft_width_scaling {r : ℝ} (hr : r ≠ 0) (t x : ℝ) :
    heatBoundaryLeft r (r^2*t) (r*x)=(r^2)⁻¹*heatBoundaryLeft 1 t x := by
  unfold heatBoundaryLeft
  simpa only [mul_zero,Nat.reduceAdd] using heatSpatialSeries_width_scaling hr 0 1 t x 0

theorem heatBoundaryRight_width_scaling {r : ℝ} (hr : r ≠ 0) (t x : ℝ) :
    heatBoundaryRight r (r^2*t) (r*x)=(r^2)⁻¹*heatBoundaryRight 1 t x := by
  unfold heatBoundaryRight
  have h := heatSpatialSeries_width_scaling hr 0 1 t x 1
  simp only [mul_one,Nat.reduceAdd] at h
  rw [h,mul_neg]

theorem heatCrossBoundary_width_scaling {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    heatCrossBoundary r (r^2*t)=(r^3)⁻¹*heatCrossBoundary 1 t := by
  unfold heatCrossBoundary
  have h := heatSpatialSeries_width_scaling hr 1 1 t 1 0
  simp only [mul_one,mul_zero,Nat.reduceAdd] at h
  rw [h,mul_neg]

end BrownianAffine
