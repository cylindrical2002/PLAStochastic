import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Analytic compact integration through a continuous-function Banach space -/

noncomputable section
open Complex Set MeasureTheory
namespace PGM

abbrev UnitSegment := Set.Icc (0 : ℝ) 1

def unitSegmentExtend {F : Type*} [TopologicalSpace F] (f : C(UnitSegment, F)) : ℝ → F :=
  fun s => f (Set.projIcc 0 1 zero_le_one s)

theorem unitSegmentExtend_continuous {F : Type*} [TopologicalSpace F]
    (f : C(UnitSegment, F)) : Continuous (unitSegmentExtend f) :=
  f.continuous.comp continuous_projIcc

/-- Integration on the unit segment is a complex continuous linear operator. -/
def unitSegmentIntegralCLM {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] : C(UnitSegment, F) →L[ℂ] F :=
  ({ toFun := fun f => ∫ s in (0 : ℝ)..1, unitSegmentExtend f s
     map_add' := fun f g => by
       exact intervalIntegral.integral_add
         ((unitSegmentExtend_continuous f).intervalIntegrable 0 1)
         ((unitSegmentExtend_continuous g).intervalIntegrable 0 1)
     map_smul' := fun c f => by
       exact intervalIntegral.integral_smul c (unitSegmentExtend f) } :
    C(UnitSegment, F) →ₗ[ℂ] F).mkContinuous 1 (by
      intro f
      change ‖∫ s in (0 : ℝ)..1, unitSegmentExtend f s‖ ≤ 1 * ‖f‖
      simpa only [unitSegmentExtend, one_mul, sub_zero, abs_one, mul_one] using
        (intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := 1) (C := ‖f‖)
          (fun s _ => f.norm_coe_le_norm (Set.projIcc 0 1 zero_le_one s))))

/-- Evaluation equality on the segment identifies the bundled integral with the usual one. -/
theorem unitSegmentIntegralCLM_eq_integral {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (f : C(UnitSegment, F)) (g : ℝ → F)
    (h : ∀ s : UnitSegment, f s = g s) :
    unitSegmentIntegralCLM f = ∫ s in (0 : ℝ)..1, g s := by
  change (∫ s in (0 : ℝ)..1, unitSegmentExtend f s) = _
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le zero_le_one] at hs
  simp only [unitSegmentExtend, Set.projIcc_of_mem zero_le_one hs]
  exact h ⟨s, hs⟩

/-- Currying continuous functions on a compact square preserves the supremum norm. -/
def compactCurryCLM {K L F : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace L] [CompactSpace L] [NormedAddCommGroup F] [NormedSpace ℂ F] :
    C(K × L, F) →L[ℂ] C(K, C(L, F)) :=
  ({ toFun := ContinuousMap.curry
     map_add' := fun _ _ => by ext x y; rfl
     map_smul' := fun _ _ => by ext x y; rfl } :
    C(K × L, F) →ₗ[ℂ] C(K, C(L, F))).mkContinuous 1 (by
      intro f
      change ‖f.curry‖ ≤ 1 * ‖f‖
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro y
      exact f.norm_coe_le_norm (x, y))

/-- The double segment integral is also a continuous linear operator. -/
def doubleUnitSegmentIntegralCLM : C(UnitSegment × UnitSegment, ℂ) →L[ℂ] ℂ :=
  unitSegmentIntegralCLM.comp
    ((ContinuousLinearMap.compLeftContinuous ℂ UnitSegment
      (unitSegmentIntegralCLM (F := ℂ))).comp compactCurryCLM)

theorem doubleUnitSegmentIntegralCLM_eq_integral (f : C(UnitSegment × UnitSegment, ℂ))
    (g : ℝ → ℝ → ℂ) (h : ∀ t s : UnitSegment, f (t, s) = g t s) :
    doubleUnitSegmentIntegralCLM f = ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, g t s := by
  change unitSegmentIntegralCLM
    ((ContinuousLinearMap.compLeftContinuous ℂ UnitSegment
      (unitSegmentIntegralCLM (F := ℂ))) (f.curry)) = _
  apply unitSegmentIntegralCLM_eq_integral
  intro t
  change unitSegmentIntegralCLM (f.curry t) = _
  exact unitSegmentIntegralCLM_eq_integral (f.curry t) (g t) (h t)

theorem analyticAt_unitSegmentIntegral {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {x : E} {H : E → C(UnitSegment, F)} (hH : AnalyticAt ℂ H x) :
    AnalyticAt ℂ (fun x => ∫ s in (0 : ℝ)..1, unitSegmentExtend (H x) s) x := by
  change AnalyticAt ℂ ((unitSegmentIntegralCLM (F := F)) ∘ H) x
  exact ((unitSegmentIntegralCLM (F := F)).analyticAt _).comp hH

/-- Pointwise exponential is the genuine exponential of the continuous-function algebra. -/
theorem continuousMap_exp_apply_algebra {K A : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (f : C(K, A)) (s : K) : (NormedSpace.exp f) s = NormedSpace.exp (f s) := by
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (ContinuousMap.evalAlgHom ℂ A s)
    (ContinuousMap.evalCLM ℂ s).continuous f
      ((NormedSpace.expSeries_radius_eq_top ℂ C(K, A)).symm ▸ edist_lt_top _ _)

theorem continuousMap_exp_apply {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (f : C(K, ℂ)) (s : K) : (NormedSpace.exp f) s = Complex.exp (f s) := by
  simpa only [← Complex.exp_eq_exp_ℂ] using continuousMap_exp_apply_algebra f s

/-- Scalar analytic parameter functions lift to constant continuous functions. -/
theorem _root_.AnalyticAt.continuousMap_const {E K F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {x : E} {a : E → F} (ha : AnalyticAt ℂ a x) :
    AnalyticAt ℂ (fun x => ContinuousMap.const K (a x)) x :=
  (ContinuousLinearMap.const K (R := ℂ) (M := F)).analyticAt _ |>.comp ha

/-- Analyticity of the Banach-algebra exponential can be used before compact integration. -/
theorem _root_.AnalyticAt.continuousMap_exp {E K A : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace K] [CompactSpace K]
    [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    {x : E} {H : E → C(K, A)} (hH : AnalyticAt ℂ H x) :
    AnalyticAt ℂ (fun x => NormedSpace.exp (H x)) x :=
  (NormedSpace.exp_analytic (𝕂 := ℂ) (H x)).comp hH

end PGM
