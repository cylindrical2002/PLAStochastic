import PLAStochastic.Index.CEPS.Scaled.MarkedDiscountUnit

/-! # The actual marked denominator at scale zero

The definitions retain their removable values at `b=0` and `z=0`.
The unit and its inverse are bounded on an explicit complex scale disc;
every scale derivative therefore has a class-controlled polynomial budget.
-/

noncomputable section
open Complex MeasureTheory Set Metric
open PGM.WienerHopf
namespace PGM

def cepsDiscountScaleRadius (D θ : ℝ) (z : ℂ) : ℝ :=
  min 1 (cepsMarkedUnitRadius D θ) / (1 + ‖z‖)

def cepsScaledDiscountUnit (ρW : Measure ℝ) (z b : ℂ) : ℂ :=
  cepsMarkedDiscountUnit ρW (b ^ 2 * z)

def cepsScaledMarkedDiscount (ρW : Measure ℝ) (z b : ℂ) : ℂ :=
  z * cepsScaledDiscountUnit ρW z b

theorem cepsDiscountScaleRadius_pos {D θ : ℝ} (hD : 0 < D) (hθ : 0 < θ) (z : ℂ) :
    0 < cepsDiscountScaleRadius D θ z :=
  div_pos (lt_min zero_lt_one (cepsMarkedUnitRadius_pos hD hθ)) (by positivity)

theorem cepsDiscountScale_mapsTo {D θ : ℝ} (z : ℂ) :
    MapsTo (fun b : ℂ => b ^ 2 * z) (ball 0 (cepsDiscountScaleRadius D θ z))
      (ball 0 (cepsMarkedUnitRadius D θ)) := by
  intro b hb
  have hn := mem_ball_zero_iff.mp hb
  have hp : 0 < 1 + ‖z‖ := by positivity
  have hm : ‖b‖ * (1 + ‖z‖) < min 1 (cepsMarkedUnitRadius D θ) := (lt_div_iff₀ hp).mp hn
  have hb1 : ‖b‖ ≤ 1 := by nlinarith [min_le_left 1 (cepsMarkedUnitRadius D θ), norm_nonneg z]
  rw [mem_ball, dist_zero_right, norm_mul, norm_pow]
  calc
    ‖b‖ ^ 2 * ‖z‖ ≤ ‖b‖ * (1 + ‖z‖) := by
      have := mul_le_mul_of_nonneg_right hb1 (mul_nonneg (norm_nonneg b) (norm_nonneg z))
      nlinarith [norm_nonneg b]
    _ < min 1 (cepsMarkedUnitRadius D θ) := hm
    _ ≤ cepsMarkedUnitRadius D θ := min_le_right _ _

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledDiscountUnit_zero (z : ℂ) : cepsScaledDiscountUnit ρW z 0 = 1 := by
  simp only [cepsScaledDiscountUnit, zero_pow (by norm_num : 2 ≠ 0), zero_mul,
    cepsMarkedDiscountUnit_zero hW hθ hD]

include hW hθ hD in
theorem cepsScaledMarkedDiscount_zero (z : ℂ) : cepsScaledMarkedDiscount ρW z 0 = z := by
  rw [cepsScaledMarkedDiscount, cepsScaledDiscountUnit_zero hW hθ hD, mul_one]

theorem cepsScaledDiscountUnit_even (ρW : Measure ℝ) (z b : ℂ) :
    cepsScaledDiscountUnit ρW z (-b) = cepsScaledDiscountUnit ρW z b := by
  simp only [cepsScaledDiscountUnit, neg_sq]

include hW hθ hD in
theorem cepsScaledMarkedDiscount_eq_div (z : ℂ) {b : ℂ} (hb : b ≠ 0) :
    cepsScaledMarkedDiscount ρW z b = cepsMarkedDiscount ρW (b ^ 2 * z) / b ^ 2 := by
  by_cases hz : z = 0
  · simp only [hz, cepsScaledMarkedDiscount, zero_mul, mul_zero,
      (cepsMarkedDiscount_zero_jets hW hθ hD).1, zero_div]
  · rw [cepsScaledMarkedDiscount, cepsScaledDiscountUnit,
      cepsMarkedDiscountUnit_eq_div hW hθ hD (mul_ne_zero (pow_ne_zero _ hb) hz)]
    field_simp

include hW hθ hD in
theorem cepsScaledDiscountUnit_budget (z : ℂ) :
    DifferentiableOn ℂ (cepsScaledDiscountUnit ρW z) (ball 0 (cepsDiscountScaleRadius D θ z)) ∧
    (∀ b ∈ ball (0 : ℂ) (cepsDiscountScaleRadius D θ z),
      ‖cepsScaledDiscountUnit ρW z b‖ ≤ cepsMarkedDiscountBound D θ / (θ / 2)) ∧
    DifferentiableOn ℂ (fun b => (cepsScaledDiscountUnit ρW z b)⁻¹)
      (ball 0 (cepsDiscountScaleRadius D θ z)) ∧
    (∀ b ∈ ball (0 : ℂ) (cepsDiscountScaleRadius D θ z),
      1 / 2 ≤ ‖cepsScaledDiscountUnit ρW z b‖ ∧ ‖(cepsScaledDiscountUnit ρW z b)⁻¹‖ ≤ 2) := by
  obtain ⟨hd, hb, hi, hbi⟩ := cepsMarkedDiscountUnit_budget hW hθ hD
  have hg : DifferentiableOn ℂ (fun b : ℂ => b ^ 2 * z)
      (ball 0 (cepsDiscountScaleRadius D θ z)) := (differentiableOn_id.pow 2).mul_const z
  have hm := cepsDiscountScale_mapsTo (D := D) (θ := θ) z
  exact ⟨hd.comp hg hm, fun b hb' => hb _ (hm hb'), hi.comp hg hm,
    fun b hb' => hbi _ (hm hb')⟩

include hW hθ hD in
theorem cepsScaledDiscountUnit_scale_jet_le (z : ℂ) (n : ℕ) :
    ‖iteratedDeriv n (cepsScaledDiscountUnit ρW z) 0‖ ≤
      (n.factorial : ℝ) * (cepsMarkedDiscountBound D θ / (θ / 2)) /
        (cepsDiscountScaleRadius D θ z / 2) ^ n := by
  obtain ⟨hd, hb, _, _⟩ := cepsScaledDiscountUnit_budget hW hθ hD z
  exact norm_iteratedDeriv_le_of_ball n (cepsDiscountScaleRadius_pos hD hθ z) hd hb

include hW hθ hD in
theorem cepsScaledDiscountUnit_inverse_scale_jet_le (z : ℂ) (n : ℕ) :
    ‖iteratedDeriv n (fun b => (cepsScaledDiscountUnit ρW z b)⁻¹) 0‖ ≤
      (n.factorial : ℝ) * 2 / (cepsDiscountScaleRadius D θ z / 2) ^ n := by
  obtain ⟨_, _, hi, hb⟩ := cepsScaledDiscountUnit_budget hW hθ hD z
  exact norm_iteratedDeriv_le_of_ball n (cepsDiscountScaleRadius_pos hD hθ z) hi
    (fun b hb' => (hb b hb').2)

end PGM
