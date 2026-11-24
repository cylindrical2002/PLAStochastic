import PLAStochastic.Index.CEPS.Scaled.ComplexJetSpatial
import PLAStochastic.Index.CEPS.Scaled.QuotientUnit
import PLAStochastic.Index.CEPS.Normal.BanachMovingSlopes

/-! # Joint finite-jet analyticity of the genuine removable cumulant quotient -/

noncomputable section
open Complex Set
namespace PGM

def cepsComplexCumulantJetQuotient (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  dslope (dslope (cepsComplexCumulantQuotientSpatialUnit p N lam z b)
    (cepsComplexCumulantRootModel p N lam z 1 N b))
      (cepsComplexCumulantRootModel p N lam z (-1) N b) ξ

theorem cepsComplexCumulantJetQuotient_real (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) :
    cepsComplexCumulantJetQuotient (fun i => (p i : ℂ)) N lam z b ξ =
      cepsCumulantJetQuotient p N lam z b ξ := by
  simp only [cepsComplexCumulantJetQuotient, cepsCumulantJetQuotient,
    cepsComplexCumulantRootModel_real]
  rfl

/-- No node separation is needed: the functional lift retains the genuine second slope. -/
theorem cepsComplexCumulantQuotientSpatialUnit_moving_slopes_analyticAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    {p : E → ℕ → ℂ} {b z a d t : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (ha : AnalyticAt ℂ a x) (hd : AnalyticAt ℂ d x) (ht : AnalyticAt ℂ t x)
    (N : ℕ) (lam : ℝ) :
    AnalyticAt ℂ (fun x => dslope (dslope
      (cepsComplexCumulantQuotientSpatialUnit (p x) N lam (z x) (b x)) (a x)) (d x) (t x)) x := by
  apply analyticAt_moving_second_dslope_of_compact_lift hU hx
    (H := fun v : E × C(UnitSegment × UnitSegment, ℂ) =>
      cepsContinuousCumulantQuotientSpatialUnit (p v.1) N lam (z v.1) (b v.1) v.2)
    (ha := ha) (hb := hd) (hc := ht)
  · intro v hv
    exact cepsContinuousCumulantQuotientSpatialUnit_analyticAt
      (fun i => (hp i v.1 hv.1).comp (x := v) (f := Prod.fst) analyticAt_fst)
      ((hb v.1 hv.1).comp (x := v) (f := Prod.fst) analyticAt_fst)
      ((hz v.1 hv.1).comp (x := v) (f := Prod.fst) analyticAt_fst)
      analyticAt_snd N lam
  · intro u _ X s
    exact cepsContinuousCumulantQuotientSpatialUnit_apply (p u) N lam (z u) (b u) X s
  · intro u _
    exact cepsComplexCumulantQuotientSpatialUnit_differentiable (p u) N lam (z u) (b u)

/-- Complex finite jets, frequency and scale are jointly analytic in the genuine root charts,
including every collision of the marker with either root. -/
theorem cepsComplexCumulantJetQuotient_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    {p : E → ℕ → ℂ} {b z ξ : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U) (hξ : AnalyticAt ℂ ξ x)
    (N : ℕ) (lam : ℝ) (hv : p x (cepsJetCode (.inl 0)) ≠ 0)
    (hsv : 2 / p x (cepsJetCode (.inl 0)) ∈ slitPlane)
    (hsz : z x + (lam : ℂ) ^ 2 / (2 * p x (cepsJetCode (.inl 0))) ∈ slitPlane)
    (hgapP : cepsComplexCumulantRootGap (p x) lam (z x) 1 ≠ 0)
    (hgapM : cepsComplexCumulantRootGap (p x) lam (z x) (-1) ≠ 0) :
    AnalyticAt ℂ (fun x => cepsComplexCumulantJetQuotient (p x) N lam (z x) (b x) (ξ x)) x := by
  have hp' : ∀ i, AnalyticAt ℂ (fun x => p x i) x := fun i => hp i x hx
  have hP := cepsComplexCumulantRootModel_analyticAt hp' (hb x hx) (hz x hx)
    N lam 1 hv hsv hsz hgapP N
  have hM := cepsComplexCumulantRootModel_analyticAt hp' (hb x hx) (hz x hx)
    N lam (-1) hv hsv hsz hgapM N
  exact cepsComplexCumulantQuotientSpatialUnit_moving_slopes_analyticAt hU hx hp hb hz hP hM hξ N lam

end PGM
