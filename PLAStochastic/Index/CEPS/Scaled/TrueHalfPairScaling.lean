import PLAStochastic.Index.CEPS.Scaled.TrueHalfDiscount
import PLAStochastic.Index.CEPS.Scaled.TrueSubtractedPair

/-! # Cubic physical scaling of the actual subtracted complete pair -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueHalfPhysicalPair {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  let μ : ℂ := (b : ℂ) * lam
  let q := cepsComplexScaledDiscount lam z b
  let l : ℂ := (1 + (b : ℂ) * lam) / b
  let t : ℂ := (b : ℂ) ^ 2 * z
  let H := (cepsWHNormalData D θ ρW μ q).regularHalfEntrance (dom.canonL ρW) μ q t
  let U : ℂ → ℂ := fun q => (cepsWHNormalData D θ ρW μ q).halfBridge (dom.canonL ρW) μ q l
  exp (t * l) * H ^ 2 * (-deriv U q - (b : ℂ)⁻¹ * U q)

def cepsScaledTrueSubtractedPhysicalPair {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  if 1 ≤ lam then cepsScaledTruePhysicalPair dom ρW lam z b - cepsScaledTrueHalfPhysicalPair dom ρW lam z b
  else cepsScaledTruePhysicalPair dom ρW lam z b

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueHalfPair_eq_physical (M lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : 0 < b) (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    (b : ℂ) ^ 3 * cepsScaledTrueHalfPhysicalPair dom ρW lam z b = cepsScaledTrueHalfPair dom ρW lam z b := by
  let μ : ℂ := (b : ℂ) * lam
  let q := cepsComplexScaledDiscount lam z b
  let w : ℂ := 1 + (b : ℂ) * lam
  let l : ℂ := w / b
  let t : ℂ := (b : ℂ) ^ 2 * z
  let H := (cepsWHNormalData D θ ρW μ q).regularHalfEntrance (dom.canonL ρW) μ q t
  let U : ℂ → ℂ := fun q => (cepsWHNormalData D θ ρW μ q).halfBridge (dom.canonL ρW) μ q l
  obtain ⟨hμ, hq, _, _, hwlo, _, _⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hqdom := hq.trans (half_le_self dom.q₀_pos.le)
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hw0 : w ≠ 0 := by
    have hwr : w.re = 1 + b * lam := by simp [w, mul_re]
    intro he
    rw [he, zero_re] at hwr
    linarith [hwlo]
  have hH : cepsScaledTrueHalfEntrance dom ρW lam z b = (b : ℂ) * H :=
    cepsScaledTrueHalfEntrance_eq_actual_on_discount_disc dom hW hθ hD hb hμ hqdom
  have hU : U q = (b : ℂ) * cepsScaledTrueHalfBridge dom ρW lam z b :=
    (cepsScaledTrueHalfBridge_eq_actual_on_discount_disc dom hW hθ hD hb hμ hqdom).symm
  have hderiv : deriv (fun z => cepsScaledTrueHalfBridge dom ρW lam z b) z = (b : ℂ) * w * deriv U q := by
    simpa only [w, U, μ, q, l, ofReal_mul, ofReal_div, ofReal_add, ofReal_one] using!
      cepsScaledTrueHalfBridge_deriv_frequency dom hW hθ hD M lam hlam hz hb hbs
  have he : t * l = ((b : ℂ) * z) * w := by dsimp [t, l]; field_simp
  change (b : ℂ) ^ 3 * (exp (t * l) * H ^ 2 * (-deriv U q - (b : ℂ)⁻¹ * U q)) =
    exp (((b : ℂ) * z) * w) * (cepsScaledTrueHalfEntrance dom ρW lam z b) ^ 2 *
      (-(1 / w) * deriv (fun z => cepsScaledTrueHalfBridge dom ρW lam z b) z -
        (b : ℂ) * cepsScaledTrueHalfBridge dom ρW lam z b)
  rw [he, hH, hderiv, hU]
  field_simp

theorem cepsScaledTrueHalfPhysicalPair_eq_regularHalfPair (lam : ℝ) (z : ℂ) (b : ℝ) :
    cepsScaledTrueHalfPhysicalPair dom ρW lam z b =
      cepsNormalRegularHalfPairAt (cepsWHNormalData D θ ρW) (dom.canonL ρW)
        ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z) (b : ℂ)⁻¹ := by
  unfold cepsScaledTrueHalfPhysicalPair cepsNormalRegularHalfPairAt
  rw [show (b : ℂ)⁻¹ * (1 + (b : ℂ) * lam) = (1 + (b : ℂ) * lam) / b by
    rw [div_eq_mul_inv, mul_comm]]

include hW hθ hD in
theorem cepsScaledTrueSubtractedPair_eq_physical (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : 0 < b) (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    (b : ℂ) ^ 3 * cepsScaledTrueSubtractedPhysicalPair dom ρW lam z b =
      cepsScaledTrueSubtractedPair dom ρW lam z b := by
  have hP := cepsScaledTruePair_eq_physical dom hW hθ hD M lam hz hb
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  unfold cepsScaledTrueSubtractedPhysicalPair cepsScaledTrueSubtractedPair
  split_ifs with hlam
  · rw [mul_sub, hP, cepsScaledTrueHalfPair_eq_physical dom hW hθ hD M lam hlam hz hb hbs]
  · exact hP

end PGM
