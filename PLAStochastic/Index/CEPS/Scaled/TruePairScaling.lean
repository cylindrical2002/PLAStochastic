import PLAStochastic.Index.CEPS.Scaled.TruePairRadius

/-! # Exact scaling of the full actual regular pair

The physical time operator is minus the fixed-discount derivative minus
the physical width parameter `1 / b`. The scaled expression retains both
terms; a marked-frequency derivative is not substituted for that operator.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTruePair {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  exp (((b : ℂ) * z) * (1 + (b : ℂ) * lam)) * (cepsScaledTrueEntrance dom ρW lam z b) ^ 2 *
    (-(1 / (1 + (b : ℂ) * lam)) * deriv (fun z => cepsScaledTrueBridge dom ρW lam z b) z -
      (b : ℂ) * cepsScaledTrueBridge dom ρW lam z b)

def cepsScaledSurrogatePair {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  exp ((b * z) * (1 + b * lam)) * (cepsScaledSurrogateEntrance dom ρW N lam z b) ^ 2 *
    (-(1 / (1 + b * lam)) * deriv (fun z => cepsScaledSurrogateBridge dom ρW N lam z b) z -
      b * cepsScaledSurrogateBridge dom ρW N lam z b)

def cepsScaledTruePhysicalPair {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  let μ : ℂ := (b : ℂ) * lam
  let q := cepsComplexScaledDiscount lam z b
  let l : ℂ := (1 + (b : ℂ) * lam) / b
  let t : ℂ := (b : ℂ) ^ 2 * z
  let H := (cepsWHNormalData D θ ρW μ q).regularEntrance (dom.canonL ρW) μ q l t
  let U : ℂ → ℂ := fun q => (cepsWHNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l
  exp (t * l) * H ^ 2 * (-deriv U q - (b : ℂ)⁻¹ * U q)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTruePair_eq_physical (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : 0 < b) (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.truePairScaleRadius M lam z)) :
    (b : ℂ) ^ 3 * cepsScaledTruePhysicalPair dom ρW lam z b = cepsScaledTruePair dom ρW lam z b := by
  let μ : ℂ := (b : ℂ) * lam
  let q := cepsComplexScaledDiscount lam z b
  let w : ℂ := 1 + (b : ℂ) * lam
  let l : ℂ := w / b
  let t : ℂ := (b : ℂ) ^ 2 * z
  let H := (cepsWHNormalData D θ ρW μ q).regularEntrance (dom.canonL ρW) μ q l t
  let U : ℂ → ℂ := fun q => (cepsWHNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l
  obtain ⟨hμ, hq, hre, hl, hw⟩ := cepsScaledTruePair_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hw0 : w ≠ 0 := by
    have hwr : w.re = 1 + b * lam := by simp [w, mul_re]
    intro he
    rw [he, zero_re] at hwr
    linarith
  have hH : cepsScaledTrueEntrance dom ρW lam z b = (b : ℂ) * H :=
    cepsScaledTrueEntrance_eq_actual_on_discount_disc dom hW hθ hD hb hμ hq.le
  have hU : U q = (b : ℂ) * cepsScaledTrueBridge dom ρW lam z b :=
    (cepsScaledTrueBridge_eq_actual_on_discount_disc dom hW hθ hD hb hμ hq.le).symm
  have hderiv : deriv (fun z => cepsScaledTrueBridge dom ρW lam z b) z = (b : ℂ) * w * deriv U q := by
    simpa only [w, U, μ, q, l, ofReal_mul, ofReal_div, ofReal_add, ofReal_one] using!
      cepsScaledTrueBridge_deriv_frequency dom hW hθ hD hb hμ hq hre hl
  have he : t * l = ((b : ℂ) * z) * w := by dsimp [t, l]; field_simp
  change (b : ℂ) ^ 3 * (exp (t * l) * H ^ 2 * (-deriv U q - (b : ℂ)⁻¹ * U q)) =
    exp (((b : ℂ) * z) * w) * (cepsScaledTrueEntrance dom ρW lam z b) ^ 2 *
      (-(1 / w) * deriv (fun z => cepsScaledTrueBridge dom ρW lam z b) z -
        (b : ℂ) * cepsScaledTrueBridge dom ρW lam z b)
  rw [he, hH, hderiv, hU]
  field_simp

theorem cepsScaledTruePair_zero (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (N : ℕ) (lam : ℝ) (z : ℂ) :
    cepsScaledTruePair dom ρW lam z 0 = cepsScaledSurrogatePair dom ρW N lam z 0 := by
  have he : (fun z => cepsScaledTrueBridge dom ρW lam z 0) =
      fun z => cepsScaledSurrogateBridge dom ρW N lam z 0 :=
    funext (cepsScaledTrueBridge_zero dom ρW N lam)
  unfold cepsScaledTruePair cepsScaledSurrogatePair
  rw [cepsScaledTrueEntrance_zero dom ρW N lam z, he, cepsScaledTrueBridge_zero dom ρW N lam z]
  simp only [ofReal_zero]

end PGM
