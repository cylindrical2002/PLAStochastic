import PLAStochastic.Index.CEPS.Scaled.MinimumBudget

/-! # The genuine scaled radicand and its Brownian value at zero scale -/

noncomputable section
open Complex MeasureTheory Set Metric
open PGM.WienerHopf
namespace PGM

def cepsScaledMorseRadicand (D θ : ℝ) (ρW : Measure ℝ) (lam z b : ℂ) : ℂ :=
  z * (1 + b * lam) - lam ^ 2 * cepsMorseMinUnit D θ ρW (b * lam)

def CepsCanonDomain.minimumScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (lam : ℂ) : ℝ := dom.μ₀ / (2 * (1 + ‖lam‖))

def CepsCanonDomain.scaledRadicandBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (lam z : ℂ) : ℝ := ‖z‖ * (1 + dom.μ₀ / 2) + ‖lam‖ ^ 2 * dom.morseMinUnitBound

theorem CepsCanonDomain.minimumScaleRadius_pos {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (lam : ℂ) : 0 < dom.minimumScaleRadius lam :=
  div_pos dom.μ₀_pos (by positivity)

theorem CepsCanonDomain.minimumScale_mapsTo {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (lam : ℂ) : MapsTo (fun b : ℂ => b * lam) (ball 0 (dom.minimumScaleRadius lam))
      (ball 0 (dom.μ₀ / 2)) := by
  intro b hb
  have hn := (lt_div_iff₀ (by positivity : 0 < 2 * (1 + ‖lam‖))).mp (mem_ball_zero_iff.mp hb)
  rw [mem_ball, dist_zero_right, norm_mul]
  have : 2 * (‖b‖ * ‖lam‖) ≤ ‖b‖ * (2 * (1 + ‖lam‖)) := by nlinarith [norm_nonneg b]
  linarith

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledMorseRadicand_zero (lam z : ℂ) : cepsScaledMorseRadicand D θ ρW lam z 0 =
    z + lam ^ 2 / (2 * (cepsStepVar ρW : ℂ)) := by
  rw [cepsScaledMorseRadicand, zero_mul, cepsMorseMinUnit_zero hW hθ hD]
  ring

include hW hθ hD in
theorem cepsScaledMorseRadicand_actual {lam b z : ℂ}
    (hμ : ‖b * lam‖ < cepsChartMu D θ) :
    b ^ 2 * z * (1 + b * lam) - cepsMorseMin D θ ρW (b * lam) =
      b ^ 2 * cepsScaledMorseRadicand D θ ρW lam z b := by
  rw [cepsMorseMin_eq_sq_mul_unit hW hθ hD hμ, cepsScaledMorseRadicand]
  ring

include hW hθ hD in
theorem cepsScaledMorseRadicand_budget (lam z : ℂ) :
    DifferentiableOn ℂ (cepsScaledMorseRadicand D θ ρW lam z)
      (ball 0 (dom.minimumScaleRadius lam)) ∧
    ∀ b ∈ ball (0 : ℂ) (dom.minimumScaleRadius lam),
      ‖cepsScaledMorseRadicand D θ ρW lam z b‖ ≤ dom.scaledRadicandBound lam z := by
  obtain ⟨hd, hb⟩ := cepsMorseMinUnit_class_budget dom hW hθ hD
  have hmap := dom.minimumScale_mapsTo lam
  have hu := hd.comp (differentiableOn_id.mul_const lam) hmap
  refine ⟨((differentiableOn_const (1 : ℂ)).add (differentiableOn_id.mul_const lam)).const_mul z
    |>.sub (hu.const_mul (lam ^ 2)), ?_⟩
  intro b hbr
  have hmu : ‖b * lam‖ ≤ dom.μ₀ / 2 := (mem_ball_zero_iff.mp (hmap hbr)).le
  calc
    _ ≤ ‖z * (1 + b * lam)‖ + ‖lam ^ 2 * cepsMorseMinUnit D θ ρW (b * lam)‖ := norm_sub_le _ _
    _ = ‖z‖ * ‖1 + b * lam‖ + ‖lam‖ ^ 2 * ‖cepsMorseMinUnit D θ ρW (b * lam)‖ := by
      rw [norm_mul, norm_mul, norm_pow]
    _ ≤ ‖z‖ * (1 + dom.μ₀ / 2) + ‖lam‖ ^ 2 * dom.morseMinUnitBound := by
      gcongr
      · exact (norm_add_le (1 : ℂ) _).trans (by simpa only [norm_one] using add_le_add le_rfl hmu)
      · exact hb _ (hmap hbr)

include hW hθ hD in
theorem cepsScaledMorseRadicand_scale_jet_le (lam z : ℂ) (n : ℕ) :
    ‖iteratedDeriv n (cepsScaledMorseRadicand D θ ρW lam z) 0‖ ≤
      (n.factorial : ℝ) * dom.scaledRadicandBound lam z / (dom.minimumScaleRadius lam / 2) ^ n := by
  obtain ⟨hd, hb⟩ := cepsScaledMorseRadicand_budget dom hW hθ hD lam z
  exact norm_iteratedDeriv_le_of_ball n (dom.minimumScaleRadius_pos lam) hd hb

include hW hθ hD in
theorem cepsScaledMorseRadicand_taylor_le (lam z : ℂ) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.minimumScaleRadius lam / 2)) :
    ‖cepsScaledMorseRadicand D θ ρW lam z b -
        complexTaylorSum (cepsScaledMorseRadicand D θ ρW lam z) n 0 b‖ ≤
      ((n.factorial : ℝ) * dom.scaledRadicandBound lam z / (dom.minimumScaleRadius lam / 4) ^ n) *
        ‖b‖ ^ n := by
  obtain ⟨hd, hm⟩ := cepsScaledMorseRadicand_budget dom hW hθ hD lam z
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (dom.minimumScaleRadius_pos lam) hd hm hb

end PGM
