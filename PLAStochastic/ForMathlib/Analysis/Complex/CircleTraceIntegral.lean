import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.ContinuousMap.Compact

/-! # Genuine continuous linear circle integration of compact traces -/

noncomputable section
open Complex Set Metric MeasureTheory
namespace PGM

def circleTraceExtend (X : C(Circle, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ sphere (0 : ℂ) 1 then X (⟨z, hz⟩ : Circle) else 0

theorem circleTraceExtend_apply (X : C(Circle, ℂ)) (z : Circle) : circleTraceExtend X z = X z := by
  have hz : (z : ℂ) ∈ sphere (0 : ℂ) 1 := by
    simpa only [mem_sphere_zero_iff_norm] using Circle.norm_coe z
  rw [circleTraceExtend, dif_pos hz]
  exact congrArg X (Circle.ext rfl)

theorem circleTraceExtend_continuousOn (X : C(Circle, ℂ)) :
    ContinuousOn (circleTraceExtend X) (sphere (0 : ℂ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact X.continuous.congr (fun z => (circleTraceExtend_apply X z).symm)

theorem circleTraceExtend_circleIntegrable (X : C(Circle, ℂ)) :
    CircleIntegrable (circleTraceExtend X) 0 1 :=
  (circleTraceExtend_continuousOn X).circleIntegrable (by norm_num)

def circleTraceIntegralCLM : C(Circle, ℂ) →L[ℂ] ℂ :=
  (show C(Circle, ℂ) →ₗ[ℂ] ℂ from
    { toFun := fun X => ∮ z in C(0, 1), circleTraceExtend X z
      map_add' := by
        intro X Y
        have he : circleTraceExtend (X + Y) = fun z => circleTraceExtend X z + circleTraceExtend Y z := by
          funext z
          by_cases hz : z ∈ sphere (0 : ℂ) 1
          · simpa only [circleTraceExtend, dif_pos hz] using!
              ContinuousMap.add_apply X Y (⟨z, hz⟩ : Circle)
          · simp only [circleTraceExtend, dif_neg hz, add_zero]
        rw [he]
        exact circleIntegral.integral_add (circleTraceExtend_circleIntegrable X)
          (circleTraceExtend_circleIntegrable Y)
      map_smul' := by
        intro c X
        have he : circleTraceExtend (c • X) = fun z => c • circleTraceExtend X z := by
          funext z
          by_cases hz : z ∈ sphere (0 : ℂ) 1
          · simpa only [circleTraceExtend, dif_pos hz] using!
              ContinuousMap.smul_apply c X (⟨z, hz⟩ : Circle)
          · simp only [circleTraceExtend, dif_neg hz, smul_zero]
        rw [he]
        exact circleIntegral.integral_smul c _ _ _ }).mkContinuous (2 * Real.pi) (by
    intro X
    have h := circleIntegral.norm_integral_le_of_norm_le_const
      (c := (0 : ℂ)) (R := (1 : ℝ)) (C := ‖X‖) (f := circleTraceExtend X) (by norm_num)
      (fun z hz => by
        simpa only [circleTraceExtend, dif_pos hz] using X.norm_coe_le_norm ⟨z, hz⟩)
    change ‖∮ z in C(0, 1), circleTraceExtend X z‖ ≤ (2 * Real.pi) * ‖X‖
    simpa only [mul_one] using! h)

theorem circleTraceIntegralCLM_eq_integral (X : C(Circle, ℂ)) (f : ℂ → ℂ)
    (he : ∀ z : Circle, X z = f z) :
    circleTraceIntegralCLM X = ∮ z in C(0, 1), f z := by
  apply circleIntegral.integral_congr (by norm_num)
  intro z hz
  exact (circleTraceExtend_apply X ⟨z, hz⟩).trans (he ⟨z, hz⟩)

def circleTraceCoord : C(Circle, ℂ) := ⟨fun z => (z : ℂ), continuous_subtype_val⟩

def circleTraceInvCoord : C(Circle, ℂ) :=
  ⟨fun z => (z : ℂ)⁻¹, continuous_subtype_val.inv₀ (fun z : Circle => Circle.coe_ne_zero z)⟩

theorem circleTraceCoord_norm : ‖circleTraceCoord‖ = 1 := by
  apply le_antisymm
  · exact (ContinuousMap.norm_le _ (by norm_num)).mpr (fun z => le_of_eq z.norm_coe)
  · have h := circleTraceCoord.norm_coe_le_norm (1 : Circle)
    change ‖((1 : Circle) : ℂ)‖ ≤ ‖circleTraceCoord‖ at h
    simpa only [Circle.coe_one, norm_one] using h

end PGM
