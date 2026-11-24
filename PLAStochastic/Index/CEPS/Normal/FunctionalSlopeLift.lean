import PLAStochastic.Index.CEPS.Normal.BanachSlopeLift

/-! # Genuine second divided differences with three compact-function-valued nodes -/

noncomputable section
open Complex Set MeasureTheory
namespace PGM

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace K] [CompactSpace K]

def functionalSecondSlopeSegment (a b X : E → C(K, ℂ)) (u : E) :
    C(CompactSlopeSquare K, ℂ) :=
  compactSlopePullbackCLM (a u) + compactSlopeInnerCoord *
    (compactSlopePullbackCLM (b u) + compactSlopeOuterCoord *
      (compactSlopePullbackCLM (X u) - compactSlopePullbackCLM (b u)) -
        compactSlopePullbackCLM (a u))

def functionalSecondSlopeLift
    (H : E × C(CompactSlopeSquare K, ℂ) → C(CompactSlopeSquare K, ℂ))
    (a b X : E → C(K, ℂ)) (u : E) : C(K, ℂ) :=
  compactSlopeSquareIntegralCLM (compactSlopeInnerCoord *
    compactSpatialDeriv (compactSpatialDeriv H) (u, functionalSecondSlopeSegment a b X u))

theorem functionalSecondSlopeLift_analyticAt
    {H : E × C(CompactSlopeSquare K, ℂ) → C(CompactSlopeSquare K, ℂ)}
    {a b X : E → C(K, ℂ)} {x : E}
    (hH : AnalyticAt ℂ H (x, functionalSecondSlopeSegment a b X x))
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x) (hX : AnalyticAt ℂ X x) :
    AnalyticAt ℂ (functionalSecondSlopeLift H a b X) x := by
  have ha' := ((compactSlopePullbackCLM (K := K)).analyticAt _).comp ha
  have hb' := ((compactSlopePullbackCLM (K := K)).analyticAt _).comp hb
  have hX' := ((compactSlopePullbackCLM (K := K)).analyticAt _).comp hX
  have hs : AnalyticAt ℂ (functionalSecondSlopeSegment a b X) x :=
    ha'.add (analyticAt_const.mul ((hb'.add (analyticAt_const.mul (hX'.sub hb'))).sub ha'))
  have hD := (compactSpatialDeriv_analyticAt (compactSpatialDeriv_analyticAt hH)).comp
    (x := x) (f := fun u => (u, functionalSecondSlopeSegment a b X u)) (analyticAt_id.prod hs)
  exact ((compactSlopeSquareIntegralCLM (K := K)).analyticAt _).comp
    ((analyticAt_const (v := compactSlopeInnerCoord)).mul hD)

/-- Every evaluation is the actual scalar removable second divided difference;
the three nodes may vary independently with the compact index. -/
theorem functionalSecondSlopeLift_apply
    {H : E × C(CompactSlopeSquare K, ℂ) → C(CompactSlopeSquare K, ℂ)}
    {f : E → ℂ → ℂ} {a b X : E → C(K, ℂ)} {u : E}
    (hH : ∀ S, AnalyticAt ℂ H (u, S))
    (he : ∀ S : C(CompactSlopeSquare K, ℂ), ∀ q, H (u, S) q = f u (S q))
    (hf : Differentiable ℂ (f u)) (k : K) :
    functionalSecondSlopeLift H a b X u k =
      dslope (dslope (f u) (a u k)) (b u k) (X u k) := by
  let S := functionalSecondSlopeSegment a b X u
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
