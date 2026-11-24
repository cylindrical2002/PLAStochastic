import PLAStochastic.Index.CEPS.Scaled.PositiveCorrectionWidth
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridge

/-! # Exact half-line subtraction for the regular scaled surrogate bridge -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogateHalfBridge {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  (cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b) *
    cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)

def cepsScaledSurrogateBridgeCorrection {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  cepsScaledSurrogateBridge dom ρW N lam z b - cepsScaledSurrogateHalfBridge dom ρW N lam z b

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateBridgeCorrection_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateBridgeCorrection dom ρW N lam z)
      (ball 0 (dom.surrogateRegularScaleRadius N M lam z)) := by
  have hsub : ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z) ⊆
      ball 0 (dom.canonScaleRadius lam z) :=
    ball_subset_ball ((min_le_left _ _).trans ((min_le_left _ _).trans
      (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)))
  have hrootSub := hsub.trans (ball_subset_ball (min_le_left _ _))
  have hp := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).1.mono hrootSub
  have hm := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)).1.mono hrootSub
  have hG := (cepsScaledSurrogateGRoot_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).mono hsub
  exact (cepsScaledSurrogateBridge_differentiableOn dom hW hθ hD hf hη hM N hN lam hz).sub
    ((hp.sub hm).mul hG)

include hW hθ hD in
theorem cepsScaledSurrogateBridgeCorrection_mul_delta {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z)) :
    cepsScaledSurrogateBridgeCorrection dom ρW N lam z b * cepsScaledSurrogateDelta dom ρW N lam z b =
      (cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b) *
        cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b) *
          exp (-cepsScaledEffectiveGap D θ ρW lam z b) * cepsScaledSurrogatePi dom ρW N lam z b := by
  rw [cepsScaledSurrogateBridgeCorrection, sub_mul,
    cepsScaledSurrogateBridge_mul_delta dom hW hθ hD hf hη hM N hN lam hz hb,
    cepsScaledSurrogateHalfBridge, cepsScaledSurrogateDelta]
  ring

theorem cepsScaledSurrogateG_mul_decay (N : ℕ) (lam : ℝ) (z b : ℂ) :
    cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b) *
        exp (-cepsScaledEffectiveGap D θ ρW lam z b) =
      exp (-(2 * cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b) *
        (1 + b * lam)) *
          cepsCanonSurrogateWeight dom ρW N (b * lam) (cepsComplexScaledDiscount lam z b)
            (b * cepsScaledSignedRoot D θ ρW lam z 1 b) := by
  unfold cepsScaledSurrogateG cepsScaledEffectiveGap
  rw [mul_right_comm, ← exp_add]
  congr 2
  ring

include hW hθ hD in
theorem cepsScaledSurrogateBridgeCorrection_joint_origin (N : ℕ) (b : ℂ) :
    cepsScaledSurrogateBridgeCorrection dom ρW N 0 0 b = cepsScaledSurrogateBridge dom ρW N 0 0 b := by
  simp only [cepsScaledSurrogateBridgeCorrection, cepsScaledSurrogateHalfBridge,
    cepsScaledSignedRoot_joint_origin hW hθ hD, sub_self, zero_mul, sub_zero]

end PGM
