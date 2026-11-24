import PLAStochastic.Index.KEP.Poisson.ArrivalTransform

/-!
# Exact Model K window coordinates of the actual Poisson arrival transform

Inside the original interval the extended intensity primitive is the original
CDF, up to an additive constant. Residual uniform coordinates therefore map
to exactly the same physical keys as the actual Poisson arrival construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepExtendedDensity_primitive_cdf {f : ℝ → ℝ} {A B flo fhi L : ℝ}
    (hf : DensityK f A B flo fhi L) {x : ℝ} (hx : x ∈ Icc A B) :
    kepIntensityPrimitive (kepExtendedDensity f A B) x -
        kepIntensityPrimitive (kepExtendedDensity f A B) A = cdfK f A x := by
  rw [kepIntensityPrimitive_sub (kepExtendedDensity_profile hf)]
  unfold cdfK
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hx.1] at ht
  exact kepExtendedDensity_eq ⟨ht.1, ht.2.trans hx.2⟩

theorem kepExtendedDensity_primitive_quantile {f : ℝ → ℝ} {A B flo fhi L : ℝ}
    (hf : DensityK f A B flo fhi L) {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    kepIntensityPrimitive (kepExtendedDensity f A B) (quantK f A B v) -
        kepIntensityPrimitive (kepExtendedDensity f A B) (quantK f A B u) = v - u := by
  have h1 := kepExtendedDensity_primitive_cdf hf (quantK_mem hf u)
  have h2 := kepExtendedDensity_primitive_cdf hf (quantK_mem hf v)
  rw [cdfK_quantK hf hu] at h1
  rw [cdfK_quantK hf hv] at h2
  linarith only [h1, h2]

theorem kepPoissonArrival_modelK_window {f : ℝ → ℝ} {A B flo fhi L M u w : ℝ}
    (hf : DensityK f A B flo fhi L) (hM : 0 < M)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hw : w ∈ Icc (0 : ℝ) 1) :
    kepPoissonArrival (kepExtendedDensity_profile hf) (M / (1 - u))
      (quantK f A B u) (M * w) = quantK f A B (u + (1 - u) * w) := by
  have hrem : 0 < 1 - u := sub_pos.mpr hu1
  have hw0 := hw.1
  have hv : u + (1 - u) * w ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith only [hw.2, hu1]
  have hc := kepExtendedDensity_primitive_quantile hf ⟨hu0, hu1.le⟩ hv
  apply (kepIntensityOrderIso (kepExtendedDensity_profile hf)).injective
  change kepIntensityPrimitive (kepExtendedDensity f A B)
      (kepPoissonArrival (kepExtendedDensity_profile hf) (M / (1 - u)) (quantK f A B u) (M * w)) =
    kepIntensityPrimitive (kepExtendedDensity f A B) (quantK f A B (u + (1 - u) * w))
  rw [kepPoissonArrival_intensity]
  have he : M * w / (M / (1 - u)) = (1 - u) * w := by
    field_simp [hM.ne']
  rw [he]
  linarith only [hc]

end

end PGM
