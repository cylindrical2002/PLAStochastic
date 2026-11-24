import PLAStochastic.Index.CEPS.Scaled.DiscountScale
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound

/-! # Actual marked-discount frequency Taylor estimate on a fixed disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledMarkedDiscount_zero_frequency_budget {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    DifferentiableOn ℂ (fun z => cepsScaledMarkedDiscount ρW z b)
      (ball 0 (cepsMarkedUnitRadius D θ)) ∧
    (∀ z ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ),
      ‖cepsScaledMarkedDiscount ρW z b‖ ≤ (cepsMarkedDiscountBound D θ / (θ / 2)) * ‖z‖) ∧
    HasDerivAt (fun z => cepsScaledMarkedDiscount ρW z b) 1 0 := by
  have hR := cepsMarkedUnitRadius_pos hD hθ
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hg : DifferentiableOn ℂ (fun z : ℂ => (b : ℂ) ^ 2 * z)
      (ball 0 (cepsMarkedUnitRadius D θ)) := by fun_prop
  have hmap : MapsTo (fun z : ℂ => (b : ℂ) ^ 2 * z)
      (ball 0 (cepsMarkedUnitRadius D θ)) (ball 0 (cepsMarkedUnitRadius D θ)) := by
    intro z hz
    rw [mem_ball_zero_iff, norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
    exact (mul_le_mul_of_nonneg_right hb2 (norm_nonneg z)).trans_lt
      (by simpa only [one_mul] using mem_ball_zero_iff.mp hz)
  have hu := (cepsMarkedDiscountUnit_budget hW hθ hD).1.comp hg hmap
  have hd := differentiableOn_id.mul hu
  refine ⟨hd, ?_, ?_⟩
  · intro z hz
    unfold cepsScaledMarkedDiscount cepsScaledDiscountUnit
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left ((cepsMarkedDiscountUnit_budget hW hθ hD).2.1 _ (hmap hz))
      (norm_nonneg z)).trans_eq (by ring)
  · have hu0 := (hu 0 (mem_ball_self hR)).differentiableAt (ball_mem_nhds 0 hR)
    have hu0' : DifferentiableAt ℂ (fun z : ℂ => cepsMarkedDiscountUnit ρW ((b : ℂ) ^ 2 * z)) 0 := hu0
    have hh := (hasDerivAt_id (0 : ℂ)).mul hu0'.hasDerivAt
    change HasDerivAt (fun z : ℂ => z * cepsMarkedDiscountUnit ρW ((b : ℂ) ^ 2 * z))
      (1 * cepsMarkedDiscountUnit ρW ((b : ℂ) ^ 2 * 0) +
        0 * deriv (fun z : ℂ => cepsMarkedDiscountUnit ρW ((b : ℂ) ^ 2 * z)) 0) 0 at hh
    simpa only [cepsScaledMarkedDiscount, cepsScaledDiscountUnit, mul_zero,
      cepsMarkedDiscountUnit_zero hW hθ hD, mul_one, zero_mul, add_zero] using hh

include hW hθ hD in
theorem cepsScaledMarkedDiscount_zero_frequency_taylor {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    {z : ℂ} (hz : z ∈ ball 0 (cepsMarkedUnitRadius D θ / 2)) :
    ‖cepsScaledMarkedDiscount ρW z b - z‖ ≤
      (32 * (cepsMarkedDiscountBound D θ / (θ / 2)) / cepsMarkedUnitRadius D θ) * ‖z‖ ^ 2 := by
  obtain ⟨hd, hbound, hder⟩ := cepsScaledMarkedDiscount_zero_frequency_budget hW hθ hD hb hb1
  have hM : 0 ≤ cepsMarkedDiscountBound D θ / (θ / 2) :=
    div_nonneg (cepsMarkedDiscountBound_pos hD hθ).le (half_pos hθ).le
  have ht := norm_sub_sub_deriv_le_of_ball (cepsMarkedUnitRadius_pos hD hθ) hd
    (fun z hz => (hbound z hz).trans (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hz).le hM)) hz
  rw [hder.deriv] at ht
  simp only [cepsScaledMarkedDiscount, zero_mul, sub_zero, one_mul] at ht
  exact ht.trans_eq (by field_simp [(cepsMarkedUnitRadius_pos hD hθ).ne'])

end PGM
