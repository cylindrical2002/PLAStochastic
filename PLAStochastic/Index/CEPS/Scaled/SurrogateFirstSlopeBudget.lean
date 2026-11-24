import PLAStochastic.Index.CEPS.Scaled.WeightedFirstSlope
import PLAStochastic.Index.CEPS.Scaled.SurrogateSecondSlopeBudget

/-! # Weighted first slopes from the positive root to the actual marker -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.surrogateSpatialFirstBound {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  Real.exp 2 * (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) / (1 / 2 : ℝ)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateG_first_dslope_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖dslope (cepsScaledSurrogateG dom ρW N lam z b)
      (cepsScaledSignedRoot D θ ρW lam z 1 b) (b * z)‖ ≤
        dom.surrogateSpatialFirstBound N M *
          (Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re) +
            Real.exp (-((b * z) * (1 + b * lam)).re)) := by
  let R := dom.entranceSpatialScaleRadius lam z
  let G := cepsScaledSurrogateG dom ρW N lam z b
  have hR := (entranceScale_constants dom hW hθ hD N M lam z).2
  have hdJ := cepsScaledSurrogateG_differentiableOn_joint dom hW hθ hD (M := M) hf hη N hN lam hz
  have hG : DifferentiableOn ℂ G (ball 0 R) := fun ξ hξ =>
    (differentiableAt_slice_snd (isOpen_ball.prod isOpen_ball) hdJ
      (show (b, ξ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z) ×ˢ ball (0 : ℂ) R from ⟨hb, hξ⟩)).differentiableWithinAt
  have hC : 0 ≤ dom.surrogateSpatialFirstBound N M := by
    unfold CepsCanonDomain.surrogateSpatialFirstBound
    have := CepsCanonDomain.v_pos hW hθ hD
    positivity
  have hderiv : ∀ ξ : ℂ, ‖ξ‖ ≤ R / 2 → ‖deriv G ξ‖ ≤
      dom.surrogateSpatialFirstBound N M * Real.exp (-(ξ * (1 + b * lam)).re) := by
    intro ξ hξ
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial_one, Nat.cast_one,
      one_mul, pow_one, G, CepsCanonDomain.surrogateSpatialFirstBound] using!
      cepsScaledSurrogateG_spatial_deriv_budget dom hW hθ hD hf hη hM N hN lam hz hb 1 hξ
  have hsub : dom.entranceScaleRadius N M lam z ≤ dom.actualRootScaleRadius lam z :=
    (min_le_right _ _).trans ((div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num)).trans (min_le_left _ _))
  have hp : ‖cepsScaledSignedRoot D θ ρW lam z 1 b‖ ≤ R / 2 := by
    have hn := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).2 b (ball_subset_ball hsub hb)
    dsimp [R, CepsCanonDomain.entranceSpatialScaleRadius]
    nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hC0 : 0 ≤ dom.actualScaledRootBound lam z := (norm_nonneg _).trans
    ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).2 0
      (mem_ball_self (actualRootScaleRadius_pos dom hW hθ hD lam z)))
  have ht : ‖b * z‖ ≤ R / 2 := by
    have hn := cepsScaledMark_norm_le_frequency dom hW hθ hD N M lam hz hb
    dsimp [R, CepsCanonDomain.entranceSpatialScaleRadius]
    nlinarith [abs_nonneg lam]
  exact cepsNormal_norm_dslope_le_weighted hR hC hG hderiv hp ht

end PGM
