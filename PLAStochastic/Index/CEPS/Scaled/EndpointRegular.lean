import PLAStochastic.Index.CEPS.Scaled.EndpointSurrogateBudget
import PLAStochastic.Index.CEPS.Scaled.EndpointPhysical
import PLAStochastic.Index.CEPS.Scaled.TruePhysicalDisc
import PLAStochastic.Index.CEPS.Normal.ActualHalfLineIdentity

/-! # The true marked endpoint after exact pole cancellation -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueRegularEndpoint {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  exp (((b : ℂ) * z) * (1 + (b : ℂ))) *
    exp (dom.canonL ρW b (cepsComplexScaledDiscount 1 z b) ((b : ℂ) ^ 2 * z)) *
      cepsScaledTrueMarkPrefactor dom ρW 1 z b *
        cepsScaledTrueG dom ρW 1 z b (cepsScaledSignedRoot D θ ρW 1 z 1 b) *
          (cepsScaledSignedRoot D θ ρW 1 z 1 b - cepsScaledSignedRoot D θ ρW 1 z (-1) b) /
            ((b : ℂ) * z - cepsScaledSignedRoot D θ ρW 1 z (-1) b)

theorem cepsScaledSurrogateMarkedEndpoint_eq_product {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (N : ℕ) (z b : ℂ) :
    cepsScaledSurrogateMarkedEndpoint dom ρW N z b =
      exp ((b * z) * (1 + b)) *
        exp (cepsCanonDriftTaylor dom ρW N b (cepsComplexScaledDiscount 1 z b) (b ^ 2 * z)) *
          cepsScaledSurrogateMarkPrefactor dom ρW N 1 z b *
            cepsScaledSurrogateG dom ρW N 1 z b (cepsScaledSignedRoot D θ ρW 1 z 1 b) *
              (cepsScaledSignedRoot D θ ρW 1 z 1 b - cepsScaledSignedRoot D θ ρW 1 z (-1) b) /
                (b * z - cepsScaledSignedRoot D θ ρW 1 z (-1) b) := by
  unfold cepsScaledSurrogateMarkedEndpoint cepsScaledSurrogateHalfEntrance
    cepsScaledSurrogateHalfBridge cepsScaledSurrogateMarkPrefactor
  simp only [ofReal_one, mul_one, div_eq_mul_inv, mul_inv]
  ring

theorem cepsScaledTrueRegularEndpoint_zero {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (N : ℕ) (z : ℂ) :
    cepsScaledTrueRegularEndpoint dom ρW z 0 = cepsScaledSurrogateMarkedEndpoint dom ρW N z 0 := by
  rw [cepsScaledSurrogateMarkedEndpoint_eq_product]
  unfold cepsScaledTrueRegularEndpoint
  rw [cepsScaledTrueG_eq_surrogate_of_drift_zero dom ρW N 1 z (by simp),
    cepsScaledTrueMarkPrefactor_eq_surrogate_of_drift_zero dom ρW N 1 z (by simp)]
  simp only [ofReal_zero, cepsCanonDriftTaylor_zero]

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueRegularEndpoint_eq_filled {b : ℝ} (hb : 0 < b)
    (hμ : |b| ≤ dom.μ₀) {z : ℂ} (hz : z ≠ 0)
    (hq : ‖cepsComplexScaledDiscount 1 z b‖ ≤ dom.q₀)
    (ht : (b : ℂ) ^ 2 * z ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ)) :
    cepsScaledTrueRegularEndpoint dom ρW z b = cepsScaledMarkedEndpoint dom ρW b z := by
  let q := cepsComplexScaledDiscount 1 z b
  let t := (b : ℂ) ^ 2 * z
  let l : ℂ := (1 + (b : ℂ)) / b
  let p := cepsRootPlus D θ ρW b q
  let m := cepsRootMinus D θ ρW b q
  let rp := cepsScaledSignedRoot D θ ρW 1 z 1 b
  let rm := cepsScaledSignedRoot D θ ρW 1 z (-1) b
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hμn : ‖(b : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hμc : ‖((b * 1 : ℝ) : ℂ)‖ < cepsChartMu D θ := by
    simpa only [mul_one] using dom.μ_lt_chart hμn
  have hqeq : q = cepsScaledDiscount b 1 z := by
    simp only [q, cepsComplexScaledDiscount, cepsScaledDiscount, ofReal_one, mul_one]
  have hp : (b : ℂ) * rp = p := by
    dsimp only [rp, p]
    rw [hqeq, cepsScaledSignedRoot_plus_actual hW hθ hD hb hμc]
    simp only [mul_one]
    exact mul_div_cancel₀ _ hb0
  have hm : (b : ℂ) * rm = m := by
    dsimp only [rm, m]
    rw [hqeq, cepsScaledSignedRoot_minus_actual hW hθ hD hb hμc]
    simp only [mul_one]
    exact mul_div_cancel₀ _ hb0
  have hdt : cepsD ρW b q t = cepsMarkedDiscount ρW t := by
    change cepsD ρW b ((b : ℂ) ^ 2 * z * (1 + (b : ℂ) * 1)) t = _
    simp only [mul_one]
    exact cepsD_marked_eq ρW b t
  have hd0 : cepsD ρW b q t ≠ 0 := by
    rw [hdt]
    exact cepsMarkedDiscount_ne_zero_on_unit hW hθ hD (mul_ne_zero (pow_ne_zero 2 hb0) hz) ht
  have hd := CepsC6.cepsD_eq_mul_cepsQ dom hW hθ hD hμn hq t
  change cepsD ρW b q t = (p - t) * (t - m) * cepsQ D θ ρW b q t at hd
  have hpt : p - t ≠ 0 := by intro he; rw [he, zero_mul, zero_mul] at hd; exact hd0 hd
  have htm : t - m ≠ 0 := by intro he; rw [he, mul_zero, zero_mul] at hd; exact hd0 hd
  have hQt : cepsQ D θ ρW b q t ≠ 0 := by intro he; rw [he, mul_zero] at hd; exact hd0 hd
  have hψ := CepsC6.cepsQ_rootPlus_mul dom hW hθ hD hμn hq
  change cepsQ D θ ρW b q p * (p - m) = deriv (cepsCgfShift ρW b) p at hψ
  have hprim := dom.actual_halfPrimitive_eq_amplitude hW hθ hD
    (t := t) (w := (b : ℂ)⁻¹) (dom.mem_SPRegion hW hθ hD hμn hq)
  have hqform : cepsComplexScaledDiscount 1 z b = (b : ℂ) ^ 2 * z * (1 + (b : ℂ)) := by
    simp only [cepsComplexScaledDiscount, ofReal_one, mul_one]
  rw [hqform] at hprim
  have hwidth : (b : ℂ)⁻¹ * (1 + (b : ℂ)) = l := by dsimp [l]; ring
  have hmark : cepsScaledMarkedEndpoint dom ρW b z =
      deriv (cepsCgfShift ρW b) p / ((t - m) * cepsQ D θ ρW b q t) *
        exp (2 * dom.canonL ρW b q t - 2 * dom.canonL ρW b q p) * exp (-(p - t) * l) := by
    rw [cepsScaledMarkedEndpoint_eq_physical dom hW hθ hD hb hz ht]
    change cepsMarkedDiscount ρW t * _ = _
    rw [hprim, ← hdt, CepsNormalData.amplitude]
    dsimp only [cepsNormalData]
    rw [hwidth, ← hqform]
    change cepsD ρW b q t * ((p - t) * deriv (cepsCgfShift ρW b) p /
      cepsD ρW b q t * exp (2 * dom.canonL ρW b q t - 2 * dom.canonL ρW b q p) *
        exp (-(p - t) * l) / cepsD ρW b q t) = _
    rw [hd]
    field_simp
  have hgp : cepsScaledTrueG dom ρW 1 z b rp =
      exp (-rp * (1 + (b : ℂ))) * cepsQ D θ ρW b q p * exp (-2 * dom.canonL ρW b q p) := by
    unfold cepsScaledTrueG cepsCanonTrueWeight
    simp only [mul_one, ofReal_one]
    rw [hp]
    ring
  have hexp : exp (((b : ℂ) * z) * (1 + (b : ℂ))) * exp (dom.canonL ρW b q t) ^ 2 *
      exp (-rp * (1 + (b : ℂ))) * exp (-2 * dom.canonL ρW b q p) =
        exp (2 * dom.canonL ρW b q t - 2 * dom.canonL ρW b q p) * exp (-(p - t) * l) := by
    rw [← exp_nat_mul, ← exp_add, ← exp_add, ← exp_add, ← exp_add]
    congr 1
    rw [← hp]
    dsimp only [t, l]
    field_simp
    ring
  rw [hmark, ← hψ]
  unfold cepsScaledTrueRegularEndpoint cepsScaledTrueMarkPrefactor
  simp only [mul_one, ofReal_one]
  change exp (((b : ℂ) * z) * (1 + (b : ℂ))) * exp (dom.canonL ρW b q t) *
    (exp (dom.canonL ρW b q t) / cepsQ D θ ρW b q t) *
      cepsScaledTrueG dom ρW 1 z b rp * (rp - rm) / ((b : ℂ) * z - rm) = _
  rw [hgp, mul_assoc (cepsQ D θ ρW b q p * (p - m) / ((t - m) * cepsQ D θ ρW b q t)),
    ← hexp, ← hp, ← hm]
  have htm_scaled : t - (b : ℂ) * rm ≠ 0 := by rwa [hm]
  have hgap0 : (b : ℂ) * z - rm ≠ 0 := by
    intro he
    apply htm
    rw [← hm]
    dsimp [t]
    linear_combination (b : ℂ) * he
  field_simp [htm_scaled]
  dsimp only [t]
  ring

end PGM
