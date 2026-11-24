import PLAStochastic.Index.CEPS.Normal.BanachMovingSlopes
import PLAStochastic.ForMathlib.Analysis.Complex.ExpUnitAlgebra

/-! # Genuine analytic compact-function lifts of the removable second spatial slope -/

noncomputable section
open Complex Set MeasureTheory
namespace PGM

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace K] [CompactSpace K]

abbrev CompactSlopeSquare (K : Type*) := K × (UnitSegment × UnitSegment)

def compactSlopePullbackCLM : C(K, ℂ) →L[ℂ] C(CompactSlopeSquare K, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ ⟨Prod.fst, continuous_fst⟩

def compactSlopeSquareIntegralCLM : C(CompactSlopeSquare K, ℂ) →L[ℂ] C(K, ℂ) :=
  (ContinuousLinearMap.compLeftContinuous ℂ K doubleUnitSegmentIntegralCLM).comp compactCurryCLM

def compactSlopeInnerCoord : C(CompactSlopeSquare K, ℂ) :=
  ⟨fun q => (q.2.2.val : ℂ), by fun_prop⟩

def compactSlopeOuterCoord : C(CompactSlopeSquare K, ℂ) :=
  ⟨fun q => (q.2.1.val : ℂ), by fun_prop⟩

def compactSecondSlopeSegment (a b : E → ℂ) (X : E → C(K, ℂ)) (u : E) :
    C(CompactSlopeSquare K, ℂ) :=
  ContinuousMap.const _ (a u) + compactSlopeInnerCoord *
    (ContinuousMap.const _ (b u) + compactSlopeOuterCoord *
      (compactSlopePullbackCLM (X u) - ContinuousMap.const _ (b u)) - ContinuousMap.const _ (a u))

def compactSecondSlopeLift
    (H : E × C(CompactSlopeSquare K, ℂ) → C(CompactSlopeSquare K, ℂ))
    (a b : E → ℂ) (X : E → C(K, ℂ)) (u : E) : C(K, ℂ) :=
  compactSlopeSquareIntegralCLM (compactSlopeInnerCoord *
    compactSpatialDeriv (compactSpatialDeriv H) (u, compactSecondSlopeSegment a b X u))

theorem compactSecondSlopeLift_analyticAt
    {H : E × C(CompactSlopeSquare K, ℂ) → C(CompactSlopeSquare K, ℂ)}
    {a b : E → ℂ} {X : E → C(K, ℂ)} {x : E}
    (hH : AnalyticAt ℂ H (x, compactSecondSlopeSegment a b X x))
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x) (hX : AnalyticAt ℂ X x) :
    AnalyticAt ℂ (compactSecondSlopeLift H a b X) x := by
  have hXp := ((compactSlopePullbackCLM (K := K)).analyticAt _).comp hX
  have hs : AnalyticAt ℂ (compactSecondSlopeSegment a b X) x :=
    ha.continuousMap_const.add (analyticAt_const.mul
      ((hb.continuousMap_const.add (analyticAt_const.mul (hXp.sub hb.continuousMap_const))).sub
        ha.continuousMap_const))
  have hD := (compactSpatialDeriv_analyticAt (compactSpatialDeriv_analyticAt hH)).comp
    (x := x) (f := fun u => (u, compactSecondSlopeSegment a b X u)) (analyticAt_id.prod hs)
  exact ((compactSlopeSquareIntegralCLM (K := K)).analyticAt _).comp
    ((analyticAt_const (v := compactSlopeInnerCoord)).mul hD)

/-- The Banach-space construction evaluates to the actual scalar removable slope. -/
theorem compactSecondSlopeLift_apply
    {H : E × C(CompactSlopeSquare K, ℂ) → C(CompactSlopeSquare K, ℂ)}
    {f : E → ℂ → ℂ} {a b : E → ℂ} {X : E → C(K, ℂ)} {u : E}
    (hH : ∀ S, AnalyticAt ℂ H (u, S))
    (he : ∀ S : C(CompactSlopeSquare K, ℂ), ∀ q, H (u, S) q = f u (S q))
    (hf : Differentiable ℂ (f u)) (k : K) :
    compactSecondSlopeLift H a b X u k = dslope (dslope (f u) (a u)) (b u) (X u k) := by
  let S := compactSecondSlopeSegment a b X u
  have hH' : ∀ S, AnalyticAt ℂ (compactSpatialDeriv H) (u, S) :=
    fun S => compactSpatialDeriv_analyticAt (hH S)
  have he' : ∀ S : C(CompactSlopeSquare K, ℂ), ∀ q,
      compactSpatialDeriv H (u, S) q = deriv (f u) (S q) :=
    fun S q => compactSpatialDeriv_apply (hH S) he hf q
  change doubleUnitSegmentIntegralCLM
    ((compactSlopeInnerCoord * compactSpatialDeriv (compactSpatialDeriv H) (u, S)).curry k) = _
  rw [second_dslope_entire_eq_integral hf]
  apply doubleUnitSegmentIntegralCLM_eq_integral
  intro t s
  rw [ContinuousMap.curry_apply, ContinuousMap.mul_apply,
    compactSpatialDeriv_apply (f := fun u => deriv (f u)) (hH' S) he' hf.deriv]
  rfl

end PGM
