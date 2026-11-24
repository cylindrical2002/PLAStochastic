import PLAStochastic.Index.CEPS.Scaled.SurrogateEntrance
import PLAStochastic.Index.CEPS.Normal.DividedDifferenceSymmetry

/-! # Half-line entrance subtraction without a positive-root marker denominator -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogateHalfEntrance {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  exp (cepsCanonDriftTaylor dom ρW N (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) /
    (cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z) *
      (b * z - cepsScaledSignedRoot D θ ρW lam z (-1) b))

def cepsScaledSurrogateEntranceCorrection {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  cepsScaledSurrogateEntrance dom ρW N lam z b - cepsScaledSurrogateHalfEntrance dom ρW N lam z b

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateEntranceCorrection_eq_firstSlope {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z))
    (ht : b * z ≠ cepsScaledSignedRoot D θ ρW lam z (-1) b) :
    cepsScaledSurrogateEntranceCorrection dom ρW N lam z b =
      -cepsScaledSurrogateHalfEntrance dom ρW N lam z b *
        dslope (cepsScaledSurrogateG dom ρW N lam z b)
          (cepsScaledSignedRoot D θ ρW lam z 1 b) (b * z) /
            cepsScaledSurrogateDenominator dom ρW N lam z b := by
  let G := cepsScaledSurrogateG dom ρW N lam z b
  let p := cepsScaledSignedRoot D θ ρW lam z 1 b
  let m := cepsScaledSignedRoot D θ ρW lam z (-1) b
  let t := b * z
  let R := dom.entranceSpatialScaleRadius lam z
  have hdJ := cepsScaledSurrogateG_differentiableOn_joint dom hW hθ hD (M := M) hf hη N hN lam hz
  have hG : ∀ ξ ∈ ball (0 : ℂ) R, DifferentiableAt ℂ G ξ := fun ξ hξ =>
    differentiableAt_slice_snd (isOpen_ball.prod isOpen_ball) hdJ
      (show (b, ξ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z) ×ˢ ball (0 : ℂ) R from ⟨hb, hξ⟩)
  have hp := hG p (entranceScaleCurve_roots_mem dom hW hθ hD N M lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hb)
  have hm := hG m (entranceScaleCurve_roots_mem dom hW hθ hD N M lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hb)
  have hswap := cepsNormal_second_dslope_swap hp hm t
  have hid := sub_smul_dslope (dslope G p) m t
  rw [smul_eq_mul, ← hswap, cepsNormal_dslope_swap G p m] at hid
  change (t - m) * dslope (dslope G m) p t =
    dslope G p t - cepsScaledSurrogateDenominator dom ρW N lam z b at hid
  have hS0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz
    (ball_subset_ball (min_le_left _ _) hb)
  have hQ := (cepsScaledSurrogateMarkQuotient_budget dom hW hθ hD N M lam hz).2 b hb
  have hQ0 := norm_pos_iff.mp ((div_pos (cepsVarLo_pos hD) (by norm_num : (0 : ℝ) < 4)).trans_le hQ)
  have ht0 : t - m ≠ 0 := sub_ne_zero.mpr ht
  unfold cepsScaledSurrogateEntranceCorrection cepsScaledSurrogateEntrance cepsScaledSurrogateHalfEntrance
  change -_ * dslope (dslope G m) p t / (_ * _) - _ / (_ * (t - m)) =
    -(_ / (_ * (t - m))) * dslope G p t / _
  field_simp
  linear_combination -hid

end PGM
