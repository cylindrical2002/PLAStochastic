import PLAStochastic.Index.CEPS.Scaled.PositiveCorrectionDirection
import PLAStochastic.Index.CEPS.Scaled.ComplexWidthDirections

/-! # Complex-width decay of the positive-drift correction root -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.positiveCorrectionScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M lam : ℝ) (z : ℂ) : ℝ :=
  min (dom.complexDirectionScaleRadius N M lam z)
    ((1 / (48 * Real.sqrt v * dom.complexIndividualRootBound)) / (1 + |lam|))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem positiveCorrectionScaleRadius_pos (N : ℕ) (M lam : ℝ) (z : ℂ) :
    0 < dom.positiveCorrectionScaleRadius N M lam z := by
  have hH := complexIndividualRootBound_pos dom hW hθ hD
  have hv := CepsCanonDomain.v_pos hW hθ hD
  exact lt_min (complexDirectionScaleRadius_pos dom hW hθ hD N M lam z) (by positivity)

include hW hθ hD in
theorem cepsScaledPositiveCorrectionRoot_width_lower (N : ℕ) (M lam : ℝ) (hlam : 0 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.positiveCorrectionScaleRadius N M lam z)) :
    ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (16 * Real.sqrt v) ≤
      ((2 * cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b) *
        (1 + b * lam)).re := by
  have hbD := ball_subset_ball (min_le_left _ _) hb
  obtain ⟨hbC, hμ, _⟩ := complexDirectionScaleCurve_bounds dom N M lam hbD
  let a := 2 * cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b
  let R := ‖cepsScaledRootCoordinate D θ ρW lam z b‖
  let H := dom.complexIndividualRootBound
  have hH : 0 < H := complexIndividualRootBound_pos dom hW hθ hD
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hre : R / (8 * Real.sqrt v) ≤ a.re := cepsScaledPositiveCorrectionRoot_real_lower dom hW hθ hD lam hlam hz hbC hμ
  have hn : ‖a‖ ≤ 3 * H * R := cepsScaledPositiveCorrectionRoot_norm_le dom hW hθ hD lam hz hbC hμ
  have ht : ‖b‖ * (1 + |lam|) < 1 / (48 * Real.sqrt v * H) :=
    (lt_div_iff₀ (by positivity : 0 < 1 + |lam|)).mp
      ((mem_ball_zero_iff.mp hb).trans_le (min_le_right _ _))
  have hu : ‖b * (lam : ℂ)‖ ≤ 1 / (48 * Real.sqrt v * H) := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg b]
  have hprod : ‖a * (b * lam)‖ ≤ R / (16 * Real.sqrt v) := by
    rw [norm_mul]
    calc
      _ ≤ (3 * H * R) * (1 / (48 * Real.sqrt v * H)) :=
        mul_le_mul hn hu (norm_nonneg _) (by dsimp [R]; positivity)
      _ = _ := by field_simp; ring
  have hneg := (neg_le_abs (a * (b * lam)).re).trans ((abs_re_le_norm _).trans hprod)
  change _ ≤ (a * (1 + b * lam)).re
  rw [mul_add, mul_one, add_re]
  ring_nf at hre hneg ⊢
  linarith

include hW hθ hD in
theorem cepsScaledPositiveCorrectionRoot_exp_decay (N : ℕ) (M lam : ℝ) (hlam : 0 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.positiveCorrectionScaleRadius N M lam z)) :
    ‖exp (-(2 * cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b) *
      (1 + b * lam))‖ ≤ Real.exp (-dom.scaledCoordinateLower lam z / (16 * Real.sqrt v)) := by
  have hd := cepsScaledPositiveCorrectionRoot_width_lower dom hW hθ hD N M lam hlam hz hb
  have hbS : b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z) :=
    ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _)
      (ball_subset_ball (min_le_left _ _) hb))
  have hcoord := cepsScaledRootCoordinate_lower dom hW hθ hD N M lam hz hbS
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hlo := (div_le_div_of_nonneg_right hcoord (by positivity : 0 ≤ 16 * Real.sqrt v)).trans hd
  rw [norm_exp, neg_mul, neg_re]
  exact Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hlo)

end PGM
