import PLAStochastic.Index.CEPS.Scaled.SignedBridgeJoint
import PLAStochastic.Index.CEPS.Normal.JointSqrtDescent

/-! # Holomorphic bridge descent to the squared signed coordinate -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsScaledMorseChart cepsScaledSignedSurrogateBridge

def cepsScaledDescendedSurrogateBridge {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam σ b : ℂ) : ℂ :=
  cepsScaledSignedSurrogateBridge dom ρW N lam (sqrt σ) b

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledDescendedSurrogateBridge_differentiableOn_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledDescendedSurrogateBridge dom ρW N lam x.2 x.1)
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M ^ 2)) :=
  cepsNormal_differentiableOn_joint_comp_sqrt (G := fun b r => cepsScaledSignedSurrogateBridge dom ρW N lam r b)
    isOpen_ball (centralCoordinateRadius_pos dom hW hθ hD N M)
    (cepsScaledSignedSurrogateBridge_differentiableOn_joint dom hW hθ hD hf hη hM N hN hlam)
    (fun b _ r _ => cepsScaledSignedSurrogateBridge_neg dom N lam r b)

include hW hθ hD in
theorem cepsScaledDescendedSurrogateBridge_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) {lam b : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M)) :
    DifferentiableOn ℂ (fun σ => cepsScaledDescendedSurrogateBridge dom ρW N lam σ b)
      (ball 0 (dom.centralCoordinateRadius N M ^ 2)) ∧
      ∀ σ ∈ ball (0 : ℂ) (dom.centralCoordinateRadius N M ^ 2),
        ‖cepsScaledDescendedSurrogateBridge dom ρW N lam σ b‖ ≤ dom.centralBridgeBound N M := by
  have hj := cepsScaledDescendedSurrogateBridge_differentiableOn_joint dom hW hθ hD hf hη hM N hN hlam
  refine ⟨hj.comp (f := fun σ : ℂ => (b, σ))
    ((differentiableOn_const b).prodMk differentiableOn_id) (fun _ hσ => ⟨hb, hσ⟩), ?_⟩
  intro σ hσ
  have hs := norm_sqrt_lt (centralCoordinateRadius_pos dom hW hθ hD N M) (mem_ball_zero_iff.mp hσ)
  exact cepsScaledSignedSurrogateBridge_central_bound dom hW hθ hD hf hη hM N hN hlam hs.le hb

include hW hθ hD in
theorem cepsScaledDescendedSurrogateBridge_deriv_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) {lam b σ : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M))
    (hσ : σ ∈ ball (0 : ℂ) (dom.centralCoordinateRadius N M ^ 2 / 2)) :
    ‖deriv (fun σ => cepsScaledDescendedSurrogateBridge dom ρW N lam σ b) σ‖ ≤
      dom.centralBridgeBound N M / (dom.centralCoordinateRadius N M ^ 2 / 4) := by
  obtain ⟨hd, hbound⟩ := cepsScaledDescendedSurrogateBridge_budget dom hW hθ hD hf hη hM N hN hlam hb
  have hR : 0 < dom.centralCoordinateRadius N M ^ 2 := sq_pos_of_pos (centralCoordinateRadius_pos dom hW hθ hD N M)
  simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] using
    norm_iteratedDeriv_le_of_ball_half 1 hR hd hbound hσ

end PGM
