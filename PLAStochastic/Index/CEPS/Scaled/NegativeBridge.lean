import PLAStochastic.Index.CEPS.Scaled.ComplexWidthDirections
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeBudget

/-! # Exponentially decaying complex-scale bridges on the negative-drift side -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.negativeSurrogateBridgeBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M lam : ℝ) (z : ℂ) : ℝ :=
  ((dom.scaledGapBound * dom.scaledRootCoordinateBound lam z) *
      (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
        dom.surrogateDeltaInverseBound lam z +
    8 * v ^ 2 / cepsVarLo D * Real.exp (6 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
      Real.exp (-dom.scaledCoordinateLower lam z / (8 * Real.sqrt v))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateBridge_negative_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : lam ≤ 0) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateBridge dom ρW N lam z)
      (ball 0 (dom.complexDirectionScaleRadius N M lam z)) ∧
      ∀ b ∈ ball (0 : ℂ) (dom.complexDirectionScaleRadius N M lam z),
        ‖cepsScaledSurrogateBridge dom ρW N lam z b‖ ≤ dom.negativeSurrogateBridgeBound N M lam z := by
  have hsub : ball (0 : ℂ) (dom.complexDirectionScaleRadius N M lam z) ⊆
      ball 0 (dom.surrogateRegularScaleRadius N M lam z) := ball_subset_ball (min_le_left _ _)
  refine ⟨(cepsScaledSurrogateBridge_differentiableOn dom hW hθ hD hf hη hM N hN lam hz).mono hsub,
    fun b hb => ?_⟩
  have hbReg := hsub hb
  have hbS : b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z) := ball_subset_ball (min_le_left _ _) hbReg
  have hsubC : dom.surrogateScaleRadius N M lam z ≤ dom.canonScaleRadius lam z :=
    (min_le_left _ _).trans (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)
  have hbC := ball_subset_ball hsubC hbS
  by_cases hne : 0 < lam ^ 2 + ‖z‖
  · have hgap0 := cepsScaledRootGap_ne_zero dom hW hθ hD N M lam hz hne hbS
    have hS0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz hbReg
    have hid := cepsScaledSurrogateDelta_mul_rootG dom hW hθ hD hf hη hM N hN lam hz hbC
    have hΔ0 : cepsScaledSurrogateDelta dom ρW N lam z b ≠ 0 := by
      intro he
      rw [he, zero_mul] at hid
      exact mul_ne_zero (neg_ne_zero.mpr hgap0) hS0 hid.symm
    have he : cepsScaledSurrogateBridge dom ρW N lam z b =
        (cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b) *
          cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b) /
            cepsScaledSurrogateDelta dom ρW N lam z b :=
      (eq_div_iff hΔ0).mpr (cepsScaledSurrogateBridge_mul_delta dom hW hθ hD hf hη hM N hN lam hz hbReg)
    have hbRad : b ∈ ball (0 : ℂ) (dom.radicandScaleRadius lam) :=
      ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hbC)
    have hK := (cepsScaledSurrogate_constants dom hW hθ hD N M).1.le
    have hgap := (cepsScaledRootGap_norm_le dom hW hθ hD lam hz hbC).trans
      (mul_le_mul_of_nonneg_left ((cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbRad) hK)
    obtain ⟨hμ, hq, hζ⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbC
    have hWgt := (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ.le hq.le hζ.le).2
    have hExp := cepsScaledRootPlus_complex_exp_decay dom hW hθ hD N M lam hlam hz hb
    have hGp : ‖cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)‖ ≤
        Real.exp (-dom.scaledCoordinateLower lam z / (8 * Real.sqrt v)) *
          (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) := by
      rw [cepsScaledSurrogateG, norm_mul]
      exact mul_le_mul hExp hWgt (norm_nonneg _) (Real.exp_pos _).le
    have hInv := (cepsScaledSurrogateDelta_inverse_budget dom hW hθ hD hf hη hM N hN lam hz hne).2 b hbS
    have hconst : 0 ≤ 8 * v ^ 2 / cepsVarLo D *
        Real.exp (6 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) := by
      have := cepsVarLo_pos hD
      positivity
    rw [he, div_eq_mul_inv, norm_mul, norm_mul]
    apply (mul_le_mul
      (mul_le_mul hgap hGp (norm_nonneg _) ((norm_nonneg _).trans hgap)) hInv
        (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hgap) ((norm_nonneg _).trans hGp))).trans
    unfold CepsCanonDomain.negativeSurrogateBridgeBound
    dsimp only [CepsCanonDomain.scaledGapBound]
    have hn := mul_nonneg hconst (Real.exp_pos (-dom.scaledCoordinateLower lam z / (8 * Real.sqrt v))).le
    nlinarith
  · have hl : lam = 0 := by nlinarith [sq_nonneg lam, norm_nonneg z]
    have hz0 : z = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg lam, norm_nonneg z])
    subst lam
    subst z
    simpa [CepsCanonDomain.negativeSurrogateBridgeBound, CepsCanonDomain.scaledRootCoordinateBound,
      CepsCanonDomain.scaledCoordinateLower] using
      cepsScaledSurrogateBridge_origin_bound dom hW hθ hD hf hη hM N hN hbReg

include hW hθ hD in
theorem cepsScaledSurrogateBridge_negative_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : lam ≤ 0) {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.complexDirectionScaleRadius N M lam z / 2)) :
    ‖cepsScaledSurrogateBridge dom ρW N lam z b -
      complexTaylorSum (cepsScaledSurrogateBridge dom ρW N lam z) n 0 b‖ ≤
      ((n.factorial : ℝ) * dom.negativeSurrogateBridgeBound N M lam z /
        (dom.complexDirectionScaleRadius N M lam z / 4) ^ n) * ‖b‖ ^ n := by
  obtain ⟨hd, hm⟩ := cepsScaledSurrogateBridge_negative_budget dom hW hθ hD hf hη hM N hN lam hlam hz
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (complexDirectionScaleRadius_pos dom hW hθ hD N M lam z) hd hm hb

end PGM
