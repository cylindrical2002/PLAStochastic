import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuotient
import PLAStochastic.Index.CEPS.Normal.BanachSlopeLift

/-! # Genuine compact spatial-function lift of the finite complex cumulant quotient -/

noncomputable section
open Complex Set
namespace PGM

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace K] [CompactSpace K]

def cepsContinuousCumulantJetQuotient (p : E → ℕ → ℂ) (N : ℕ) (lam : ℝ)
    (z b : E → ℂ) (X : E → C(K, ℂ)) : E → C(K, ℂ) :=
  compactSecondSlopeLift
    (fun v : E × C(CompactSlopeSquare K, ℂ) =>
      cepsContinuousCumulantQuotientSpatialUnit (p v.1) N lam (z v.1) (b v.1) v.2)
    (fun u => cepsComplexCumulantRootModel (p u) N lam (z u) 1 N (b u))
    (fun u => cepsComplexCumulantRootModel (p u) N lam (z u) (-1) N (b u)) X

/-- This is a Banach-space lift of the original scalar second slope, not a formal coefficient. -/
theorem cepsContinuousCumulantJetQuotient_apply {p : E → ℕ → ℂ} (N : ℕ) (lam : ℝ)
    {z b : E → ℂ} (X : E → C(K, ℂ)) {x : E}
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x)
    (hb : AnalyticAt ℂ b x) (hz : AnalyticAt ℂ z x) (k : K) :
    cepsContinuousCumulantJetQuotient p N lam z b X x k =
      cepsComplexCumulantJetQuotient (p x) N lam (z x) (b x) (X x k) := by
  unfold cepsContinuousCumulantJetQuotient cepsComplexCumulantJetQuotient
  apply compactSecondSlopeLift_apply
  · intro S
    exact cepsContinuousCumulantQuotientSpatialUnit_analyticAt
      (fun i => (hp i).comp (x := (x, S)) (f := Prod.fst) analyticAt_fst)
      (hb.comp (x := (x, S)) (f := Prod.fst) analyticAt_fst)
      (hz.comp (x := (x, S)) (f := Prod.fst) analyticAt_fst)
      analyticAt_snd N lam
  · intro S q
    exact cepsContinuousCumulantQuotientSpatialUnit_apply (p x) N lam (z x) (b x) S q
  · exact cepsComplexCumulantQuotientSpatialUnit_differentiable (p x) N lam (z x) (b x)

set_option maxHeartbeats 800000 in
/-- Finite complex jets give an actual analytic compact-function quotient, with no collision
restriction on the spatial evaluation curve. -/
theorem cepsContinuousCumulantJetQuotient_analyticAt {p : E → ℕ → ℂ} (N : ℕ) (lam : ℝ)
    {z b : E → ℂ} {X : E → C(K, ℂ)} {x : E}
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x)
    (hb : AnalyticAt ℂ b x) (hz : AnalyticAt ℂ z x) (hX : AnalyticAt ℂ X x)
    (hv : p x (cepsJetCode (.inl 0)) ≠ 0)
    (hsv : 2 / p x (cepsJetCode (.inl 0)) ∈ slitPlane)
    (hsz : z x + (lam : ℂ) ^ 2 / (2 * p x (cepsJetCode (.inl 0))) ∈ slitPlane)
    (hgapP : cepsComplexCumulantRootGap (p x) lam (z x) 1 ≠ 0)
    (hgapM : cepsComplexCumulantRootGap (p x) lam (z x) (-1) ≠ 0) :
    AnalyticAt ℂ (cepsContinuousCumulantJetQuotient p N lam z b X) x := by
  let H : E × C(CompactSlopeSquare K, ℂ) → C(CompactSlopeSquare K, ℂ) := fun v =>
    cepsContinuousCumulantQuotientSpatialUnit (p v.1) N lam (z v.1) (b v.1) v.2
  let a : E → ℂ := fun u => cepsComplexCumulantRootModel (p u) N lam (z u) 1 N (b u)
  let d : E → ℂ := fun u => cepsComplexCumulantRootModel (p u) N lam (z u) (-1) N (b u)
  have ha : AnalyticAt ℂ a x :=
    cepsComplexCumulantRootModel_analyticAt hp hb hz N lam 1 hv hsv hsz hgapP N
  have hd : AnalyticAt ℂ d x :=
    cepsComplexCumulantRootModel_analyticAt hp hb hz N lam (-1) hv hsv hsz hgapM N
  have hHH : AnalyticAt ℂ H (x, compactSecondSlopeSegment a d X x) :=
    cepsContinuousCumulantQuotientSpatialUnit_analyticAt
      (fun i => (hp i).comp (x := (x, compactSecondSlopeSegment a d X x))
        (f := Prod.fst) analyticAt_fst)
      (hb.comp (x := (x, compactSecondSlopeSegment a d X x)) (f := Prod.fst) analyticAt_fst)
      (hz.comp (x := (x, compactSecondSlopeSegment a d X x)) (f := Prod.fst) analyticAt_fst)
      analyticAt_snd N lam
  exact compactSecondSlopeLift_analyticAt (H := H) (a := a) (b := d) (X := X) hHH ha hd hX

end PGM
