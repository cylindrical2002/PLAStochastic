import PLAStochastic.Index.CEPS.Scaled.ComplexJetKernel
import PLAStochastic.Index.CEPS.Normal.MovingEntireSlopeContinuity

/-! # Genuine continuity of finite complex-jet spatial units with independent nodes -/

noncomputable section
open Complex Finset
namespace PGM

theorem cepsCgfComplexJetPolynomial_continuous {E : Type*} [TopologicalSpace E]
    {p : E → ℕ → ℂ} {s : E → ℂ} (hp : ∀ i, Continuous (fun x => p x i))
    (hs : Continuous s) (N : ℕ) :
    Continuous (fun x => cepsCgfComplexJetPolynomial (p x) N (s x)) := by
  unfold cepsCgfComplexJetPolynomial
  apply continuous_finsetSum
  intro j _
  exact (continuous_const.mul (hs.pow j)).mul (hp _)

theorem cepsCanonComplexJetPolynomial_continuous {E : Type*} [TopologicalSpace E]
    {p : E → ℕ → ℂ} {μ q ζ : E → ℂ} (hp : ∀ i, Continuous (fun x => p x i))
    (hμ : Continuous μ) (hq : Continuous q) (hζ : Continuous ζ) (N : ℕ) :
    Continuous (fun x => cepsCanonComplexJetPolynomial (p x) N (μ x) (q x) (ζ x)) := by
  unfold cepsCanonComplexJetPolynomial
  apply continuous_finsetSum
  intro j _
  apply (continuous_const.mul (hμ.pow j)).mul
  apply continuous_finsetSum
  intro m _
  apply (continuous_const.mul (hζ.pow m)).mul
  apply continuous_finsetSum
  intro n _
  exact (continuous_const.mul (hq.pow n)).mul (hp _)

theorem cepsComplexCumulantQuotientSpatialUnit_continuous {E : Type*} [TopologicalSpace E]
    {p : E → ℕ → ℂ} {lam : E → ℝ} {z b ξ : E → ℂ}
    (hp : ∀ i, Continuous (fun x => p x i)) (hl : Continuous lam)
    (hz : Continuous z) (hb : Continuous b) (hξ : Continuous ξ) (N : ℕ) :
    Continuous (fun x => cepsComplexCumulantQuotientSpatialUnit (p x) N (lam x) (z x) (b x) (ξ x)) := by
  have hlc : Continuous (fun x => (lam x : ℂ)) := Complex.continuous_ofReal.comp hl
  have hP := cepsCgfComplexJetPolynomial_continuous hp (hb.mul hξ) N
  have hT : Continuous (fun x => cepsComplexCumulantQuadraticEquation (p x) N (lam x) (z x) (b x) (ξ x)) :=
    (((hξ.pow 2).mul hP).add (hlc.mul hξ)).sub
      (hz.mul (continuous_const.add (hb.mul hlc)))
  have hU : Continuous (fun x : ℂ × ℂ => quadraticExpUnit x.1 x.2) :=
    continuous_iff_continuousAt.mpr fun x => (quadraticExpUnit_joint_analyticAt x).continuousAt
  exact hU.comp (hb.prodMk hT)

/-- Independent spatial nodes allow a common compact parameter budget without any root
branch condition. Every diagonal is the actual derivative value of the divided difference. -/
theorem cepsComplexCumulantQuotientSpatialUnit_moving_second_slope_continuous
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {p : E → ℕ → ℂ} {lam : E → ℝ} {z b a d ξ : E → ℂ}
    (hp : ∀ i, Continuous (fun x => p x i)) (hl : Continuous lam)
    (hz : Continuous z) (hb : Continuous b) (ha : Continuous a) (hd : Continuous d)
    (hξ : Continuous ξ) (N : ℕ) :
    Continuous (fun x => dslope (dslope
      (cepsComplexCumulantQuotientSpatialUnit (p x) N (lam x) (z x) (b x)) (a x)) (d x) (ξ x)) := by
  exact cepsNormal_continuous_moving_second_dslope_entire
    (cepsComplexCumulantQuotientSpatialUnit_continuous
      (fun i => (hp i).comp continuous_fst) (hl.comp continuous_fst)
      (hz.comp continuous_fst) (hb.comp continuous_fst) continuous_snd N)
    (fun x => cepsComplexCumulantQuotientSpatialUnit_differentiable (p x) N (lam x) (z x) (b x)) ha hd hξ

end PGM
