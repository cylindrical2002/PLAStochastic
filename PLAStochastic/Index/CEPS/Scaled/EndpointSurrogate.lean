import PLAStochastic.Index.CEPS.Scaled.SurrogateMarkHolomorphy
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeSquareBudget
import PLAStochastic.Index.CEPS.Scaled.RootDriftDirection
import PLAStochastic.Index.CEPS.Scaled.EntranceBridgeDecay

/-! # A marked endpoint with a genuine zero-scale value

The half-line amplitude is written after cancellation of the positive-root
marker factor. Its only root-marker denominator is separated on the
positive endpoint drift. No pole removal is needed in this scaled formula.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogateMarkedEndpoint {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (z b : ℂ) : ℂ :=
  exp ((b * z) * (1 + b)) *
    exp (cepsCanonDriftTaylor dom ρW N b (cepsComplexScaledDiscount 1 z b) (b ^ 2 * z)) *
      cepsScaledSurrogateHalfEntrance dom ρW N 1 z b * cepsScaledSurrogateHalfBridge dom ρW N 1 z b

def CepsCanonDomain.endpointSurrogateConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  Real.exp (dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) *
    dom.surrogateHalfEntranceBound N M * dom.surrogateHalfBridgeWeightedConstant N M *
      Real.exp (2 / cepsVarLo D)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateHalfBridge_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateHalfBridge dom ρW N lam z)
      (ball 0 (dom.canonScaleRadius lam z)) := by
  have hsub : ball (0 : ℂ) (dom.canonScaleRadius lam z) ⊆ ball 0 (dom.actualRootScaleRadius lam z) :=
    ball_subset_ball (min_le_left _ _)
  have hp := ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).1).mono hsub
  have hm := ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)).1).mono hsub
  exact (hp.sub hm).mul (cepsScaledSurrogateGRoot_differentiableOn dom hW hθ hD hf hη hM N hN
    lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1))

include hW hθ hD in
theorem cepsScaledSurrogateMarkedEndpoint_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M)
    (N : ℕ) (hN : N + 1 ≤ m) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateMarkedEndpoint dom ρW N z)
      (ball 0 (dom.pairPolynomialScaleBase N M / (2 + Real.sqrt ‖z‖))) := by
  have hR := pairPolynomialScaleRadius_le dom hW hθ hD N M 1 z
  simp only [abs_one, one_add_one_eq_two] at hR
  have hsubE : ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (2 + Real.sqrt ‖z‖)) ⊆
      ball 0 (dom.entranceScaleRadius N M 1 z) := ball_subset_ball hR.2
  have hsubC : ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (2 + Real.sqrt ‖z‖)) ⊆
      ball 0 (dom.canonScaleRadius 1 z) := ball_subset_ball (hR.2.trans ((min_le_right _ _).trans
    (div_le_self (canonScaleRadius_pos dom hW hθ hD 1 z).le (by norm_num))))
  have hL := (cepsScaledSurrogateMarkLog_differentiableOn dom hW hθ hD hf hη N hN 1 hz).mono hsubE
  simp only [ofReal_one, mul_one] at hL
  have hH := cepsScaledSurrogateHalfEntrance_differentiableOn dom hW hθ hD (M := M) hf hη N hN
    1 le_rfl hz
  simp only [abs_one, one_add_one_eq_two] at hH
  have hU := (cepsScaledSurrogateHalfBridge_differentiableOn dom hW hθ hD hf hη hM N hN 1 hz).mono hsubC
  have hE : DifferentiableOn ℂ (fun b : ℂ => exp ((b * z) * (1 + b)))
      (ball 0 (dom.pairPolynomialScaleBase N M / (2 + Real.sqrt ‖z‖))) := by fun_prop
  exact ((hE.mul hL.cexp).mul hH).mul hU

include hW hθ hD in
theorem cepsScaledRootPlus_marker_drift_loss (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) :
    dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) - 2 / cepsVarLo D * |lam| ≤
      ((cepsScaledSignedRoot D θ ρW lam z 1 b - b * z) * (1 + b * lam)).re := by
  have hRadii := pairPolynomialScaleRadius_le dom hW hθ hD N M lam z
  have hbP := ball_subset_ball hRadii.1 hb
  have hbE := ball_subset_ball hRadii.2 hb
  have hbReg := ball_subset_ball (min_le_left _ _) hbE
  have hp := cepsScaledRootPlus_width_drift_loss dom hW hθ hD N M lam hz
    (ball_subset_ball (min_le_left _ _) hbP)
  have ht := (re_le_norm _).trans (cepsScaledMarker_width_small dom hW hθ hD N M lam hz hb)
  have hRc := (scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z).trans
    (cepsScaledRootCoordinate_lower dom hW hθ hD N M lam hz
      (ball_subset_ball (min_le_left _ _) hbReg))
  have hsmall : dom.entranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖) ≤
      ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (32 * Real.sqrt v) := by
    unfold CepsCanonDomain.entranceBridgeDecayRate
    convert! div_le_div_of_nonneg_right hRc (by positivity : (0 : ℝ) ≤ 32 * Real.sqrt v) using 1
    ring
  have hpos : 0 ≤ ‖cepsScaledRootCoordinate D θ ρW lam z b‖ * (Real.sqrt v)⁻¹ :=
    mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  rw [sub_mul, sub_re]
  ring_nf at hp ht hsmall ⊢
  linarith

end PGM
