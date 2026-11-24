import PLAStochastic.Index.CEPS.Total.LevelClose
import PLAStochastic.Index.CEPS.Scaled.TrueMidBand

/-! # The normal-transform mid-frequency estimate on each fixed level -/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsLevelDomain

set_option maxHeartbeats 800000 in
theorem ceps_mid_level (n : ℕ) :
    ∃ K c R eps₀ : ℝ, 0 ≤ K ∧ 0 < c ∧ 0 < R ∧ 1 ≤ eps₀ ∧
      ∀ eps : ℝ, eps₀ ≤ eps → ∀ ν : ProbabilityMeasure ℝ, CepsLevel n ν →
        ∀ y : ℝ, |y| ≤ R * eps ^ 2 →
          ‖cepsScaledTrueNormalExpression (cepsLevelDomain n)
            ((ν : Measure ℝ).map fun x => 1 - x) (2 * eps)⁻¹ (cepsLevelCutoff n)
            (I * y)‖ ≤ K * (1 + |y|) ^ 3 * Real.exp (-c * Real.sqrt |y|) := by
  by_cases hex : ∃ ν, CepsLevel n ν
  · obtain ⟨ν₀, hν₀⟩ := hex
    obtain ⟨f₀, -, -, -, hW₀, -, -⟩ := hν₀.stepLaw
    let dom := cepsLevelDomain n
    let M := cepsLevelScale n
    have hθ := cepsLevelRate_pos n
    have hD := cepsLevelStepD_pos n
    have hM := (cepsLevelScale_pos n).le
    have hδ := (cepsLevelCutoff_le n).2.2.1
    let B := dom.trueTransformFrequencyBase M
    have hB : 0 < B := trueTransformFrequencyBase_pos dom hW₀ hθ hD hM
    refine ⟨8 * dom.trueTransformFrequencyConstant M, dom.entranceBridgeDecayRate,
      B ^ 2 / 4, max 1 (2 / B), mul_nonneg (by norm_num)
        (trueTransformFrequencyConstant_nonneg dom hθ hD M),
      (entranceBridgePolynomial_constants dom hW₀ hθ hD 0 M).2,
      by positivity, le_max_left _ _, ?_⟩
    intro eps heps ν hν y hy
    obtain ⟨f, -, -, -, hW, hf, hfM⟩ := hν.stepLaw
    have heps1 : 1 ≤ eps := (le_max_left _ _).trans heps
    have heps0 : 0 < eps := zero_lt_one.trans_le heps1
    have hepsB : 2 / B ≤ eps := (le_max_right _ _).trans heps
    have hbeps : 2 ≤ B * eps := by
      have := (div_le_iff₀ hB).mp hepsB
      nlinarith
    have hyroot : Real.sqrt |y| ≤ B * eps / 2 := by
      have hysq := Real.sq_sqrt (abs_nonneg y)
      have hys := Real.sqrt_nonneg |y|
      nlinarith [mul_pos hB heps0]
    have hsmall : (2 * eps)⁻¹ * (1 + Real.sqrt |y|) < B := by
      rw [inv_mul_lt_iff₀ (mul_pos (by norm_num) heps0)]
      nlinarith
    have hz : (I * (y : ℂ)).re = 0 := by simp
    have hn : ‖I * (y : ℂ)‖ = |y| := by
      rw [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]
    have hb := cepsScaledTrueNormalExpression_polynomial_frequency_budget dom hW hθ hD
      hf (cepsLevelDomain_two_c₀_le n) hfM (by norm_num [cepsLevelOrder])
      (b := (2 * eps)⁻¹) (δ := cepsLevelCutoff n) (z := I * (y : ℂ))
      (inv_pos.2 (mul_pos (by norm_num) heps0)) hδ hz (by simpa only [hn] using hsmall)
    simpa only [hn, dom, M] using hb
  · exact ⟨0, 1, 1, 1, le_rfl, one_pos, one_pos, le_rfl,
      fun _ _ ν hν => False.elim (hex ⟨ν, hν⟩)⟩

end PGM
