import PLAStochastic.ForMathlib.Analysis.Complex.CompactIntegralAnalytic
import PLAStochastic.ForMathlib.Analysis.Complex.QuadraticExpUnit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Entire exponential and quadratic units in continuous-function Banach algebras -/

noncomputable section
open Complex Set MeasureTheory
namespace PGM

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

def unitSegmentAlgebraCoord : C(UnitSegment, A) :=
  ⟨fun s => (s.val : ℂ) • (1 : A), by fun_prop⟩

/-- The entire unit `(exp T - 1) / T`, with its genuine value at zero. -/
def expUnitAlgebra (T : A) : A :=
  unitSegmentIntegralCLM (NormedSpace.exp
    (unitSegmentAlgebraCoord * ContinuousMap.const UnitSegment T))

/-- This definition is analytic in the Banach algebra, including its origin. -/
theorem expUnitAlgebra_analyticAt (T : A) : AnalyticAt ℂ expUnitAlgebra T := by
  have ha : AnalyticAt ℂ (fun T : A =>
      unitSegmentAlgebraCoord * ContinuousMap.const UnitSegment T) T :=
    analyticAt_const.mul (analyticAt_id.continuousMap_const)
  change AnalyticAt ℂ ((unitSegmentIntegralCLM (F := A)) ∘
    (fun T => NormedSpace.exp (unitSegmentAlgebraCoord * ContinuousMap.const UnitSegment T))) T
  exact ((unitSegmentIntegralCLM (F := A)).analyticAt _).comp ha.continuousMap_exp

theorem expUnitAlgebra_apply {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (T : C(K, ℂ)) (s : K) : expUnitAlgebra T s = expUnitAlgebra (T s) := by
  let H : C(UnitSegment, C(K, ℂ)) := NormedSpace.exp
    (unitSegmentAlgebraCoord * ContinuousMap.const UnitSegment T)
  change (unitSegmentIntegralCLM H) s = _
  rw [show (unitSegmentIntegralCLM H) s =
      ∫ r in (0 : ℝ)..1, (unitSegmentExtend H r) s by
    exact ((ContinuousMap.evalCLM ℂ s).intervalIntegral_comp_comm
      ((unitSegmentExtend_continuous H).intervalIntegrable (μ := volume) 0 1)).symm]
  unfold expUnitAlgebra
  change _ = ∫ r in (0 : ℝ)..1,
    unitSegmentExtend (NormedSpace.exp
      (unitSegmentAlgebraCoord * ContinuousMap.const UnitSegment (T s))) r
  apply intervalIntegral.integral_congr
  intro r _
  simp only [unitSegmentExtend, H, continuousMap_exp_apply_algebra,
    ContinuousMap.mul_apply, ContinuousMap.const_apply, unitSegmentAlgebraCoord,
    ContinuousMap.coe_mk, Algebra.smul_def, mul_one, ← Complex.exp_eq_exp_ℂ]
  rfl

theorem dslope_exp_zero_eq_integral (x : ℂ) :
    dslope Complex.exp 0 x = ∫ s in (0 : ℝ)..1, Complex.exp ((s : ℂ) * x) := by
  by_cases hx : x = 0
  · subst x; simp [dslope_same]
  · have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
      (z₀ := (0 : ℂ)) (z₁ := x)
      (f := Complex.exp) (f' := Complex.exp)
      (by fun_prop : ContinuousOn (fun s : ℝ => Complex.exp (0 + s • x)) (Icc 0 1))
      (fun s _ => Complex.hasDerivAt_exp (0 + s • x))
    simp only [zero_add, Complex.real_smul, smul_eq_mul, Complex.exp_zero] at h
    rw [dslope_of_ne _ hx, slope_def_field, sub_zero, Complex.exp_zero]
    exact (div_eq_iff hx).mpr (by simpa only [mul_comm] using h.symm)

theorem expUnitAlgebra_complex (x : ℂ) : expUnitAlgebra x = dslope Complex.exp 0 x := by
  rw [dslope_exp_zero_eq_integral]
  apply unitSegmentIntegralCLM_eq_integral
  intro s
  rw [continuousMap_exp_apply]
  simp [unitSegmentAlgebraCoord]

/-- The quadratic removable unit is lifted without a singular scale quotient. -/
def quadraticExpUnitAlgebra (b : ℂ) (T : A) : A := T * expUnitAlgebra ((b ^ 2) • T)

theorem quadraticExpUnitAlgebra_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {x : E} {b : E → ℂ} {T : E → A}
    (hb : AnalyticAt ℂ b x) (hT : AnalyticAt ℂ T x) :
    AnalyticAt ℂ (fun x => quadraticExpUnitAlgebra (b x) (T x)) x :=
  hT.mul ((expUnitAlgebra_analyticAt _).comp ((hb.pow 2).smul hT))

theorem quadraticExpUnitAlgebra_apply {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (b : ℂ) (T : C(K, ℂ)) (s : K) :
    quadraticExpUnitAlgebra b T s = quadraticExpUnit b (T s) := by
  simp only [quadraticExpUnitAlgebra, ContinuousMap.mul_apply, expUnitAlgebra_apply,
    ContinuousMap.smul_apply, smul_eq_mul, expUnitAlgebra_complex, quadraticExpUnit]

end PGM
