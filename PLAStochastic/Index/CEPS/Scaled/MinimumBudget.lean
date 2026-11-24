import PLAStochastic.Index.CEPS.Scaled.MorseMinimum
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorDisc

/-! # Uniform budgets for the second-order Morse minimum unit -/

noncomputable section
open Complex MeasureTheory Set Metric
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.morseMinUnitBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  (dom.rmax ^ 2 / 4) / (dom.μ₀ / 4) ^ 2

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMorseMinUnit_differentiableOn :
    DifferentiableOn ℂ (cepsMorseMinUnit D θ ρW) (ball 0 (cepsChartMu D θ)) := by
  have hd := differentiableOn_hadamard2 (differentiableOn_cepsMorseMin hW hθ hD)
  exact hd.comp ((differentiableOn_const (0 : ℂ)).prodMk differentiableOn_id)
    (fun μ hμ => by
      change ‖(0 : ℂ)‖ + ‖μ‖ < cepsChartMu D θ
      simpa only [norm_zero, zero_add] using mem_ball_zero_iff.mp hμ)

include hW hθ hD in
theorem cepsMorseMinUnit_class_budget :
    DifferentiableOn ℂ (cepsMorseMinUnit D θ ρW) (ball 0 (dom.μ₀ / 2)) ∧
    ∀ μ ∈ ball (0 : ℂ) (dom.μ₀ / 2), ‖cepsMorseMinUnit D θ ρW μ‖ ≤ dom.morseMinUnitBound := by
  have hf : DifferentiableOn ℂ (cepsMorseMin D θ ρW) (ball 0 dom.μ₀) :=
    (differentiableOn_cepsMorseMin hW hθ hD).mono
      (fun μ hμ => mem_ball_zero_iff.mpr (dom.μ_lt_chart (mem_ball_zero_iff.mp hμ).le))
  have hb : ∀ μ ∈ ball (0 : ℂ) dom.μ₀, ‖cepsMorseMin D θ ρW μ‖ ≤ dom.rmax ^ 2 / 4 :=
    fun μ hμ => cepsMorseMin_norm_le_class dom hW hθ hD (mem_ball_zero_iff.mp hμ).le
  have hd2 : ∀ μ ∈ ball (0 : ℂ) (dom.μ₀ / 2),
      ‖deriv (deriv (cepsMorseMin D θ ρW)) μ‖ ≤ 2 * dom.morseMinUnitBound := by
    intro μ hμ
    have ht := norm_iteratedDeriv_le_of_ball_half 2 dom.μ₀_pos hf hb hμ
    simpa only [CepsCanonDomain.morseMinUnitBound, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero,
      Nat.factorial_two, Nat.cast_ofNat, mul_div_assoc] using ht
  refine ⟨(cepsMorseMinUnit_differentiableOn hW hθ hD).mono
    (fun μ hμ => mem_ball_zero_iff.mpr (dom.μ_lt_chart
      ((mem_ball_zero_iff.mp hμ).le.trans (half_le_self dom.μ₀_pos.le)))), ?_⟩
  intro μ hμ
  have hs : ∀ t ∈ Icc (0 : ℝ) 1, (0 : ℂ) + t * μ ∈ ball (0 : ℂ) (dom.μ₀ / 2) := by
    intro t ht
    rw [mem_ball, dist_zero_right, zero_add, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg μ) ht.2).trans_lt (mem_ball_zero_iff.mp hμ)
  have ht := norm_hadamard2_sub_le isOpen_ball
    (hf.mono (ball_subset_ball (half_le_self dom.μ₀_pos.le))) (c := (0 : ℂ)) hs
      (fun t ht => by simpa only [sub_zero] using hd2 _ (hs t ht))
  simpa only [cepsMorseMinUnit, zero_div, sub_zero, mul_div_cancel_left₀
    dom.morseMinUnitBound (by norm_num : (2 : ℝ) ≠ 0)] using ht

end PGM
