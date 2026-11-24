import PLAStochastic.Index.CEPS.Total.LevelClose
import PLAStochastic.Index.CEPS.Scaled.NormalFixedTaylor

/-! # The fixed-window normal Taylor bound on each canonical level -/

noncomputable section
open Complex MeasureTheory Set Metric
open PGM.WienerHopf
namespace PGM

def cepsNormalDn (eps : ℝ) (ν : ProbabilityMeasure ℝ) : ℂ :=
  cepsScaledTrueNormalSlope (cepsLevelDomain (cepsLevelIndex ν))
    ((ν : Measure ℝ).map fun x => 1 - x) (2 * eps)⁻¹ (cepsLevelCutoff (cepsLevelIndex ν))

attribute [local irreducible] cepsLevelDomain

set_option maxHeartbeats 800000 in
theorem ceps_taylor_level (n : ℕ) :
    ∃ K eps₀ : ℝ, 0 ≤ K ∧ 1 ≤ eps₀ ∧
      ∀ eps : ℝ, eps₀ ≤ eps → ∀ ν : ProbabilityMeasure ℝ, CepsLevel n ν →
        ∀ y : ℝ, |y| ≤ 1 →
          ‖cepsScaledTrueNormalExpression (cepsLevelDomain n)
            ((ν : Measure ℝ).map fun x => 1 - x) (2 * eps)⁻¹ (cepsLevelCutoff n) (I * y) - 1 -
              (I * y) * cepsScaledTrueNormalSlope (cepsLevelDomain n)
                ((ν : Measure ℝ).map fun x => 1 - x) (2 * eps)⁻¹ (cepsLevelCutoff n)‖ ≤
            K * eps ^ 5 * y ^ 2 := by
  by_cases hex : ∃ ν, CepsLevel n ν
  · obtain ⟨ν₀, hν₀⟩ := hex
    obtain ⟨f₀, -, -, -, hW₀, -, -⟩ := hν₀.stepLaw
    let dom := cepsLevelDomain n
    let M := cepsLevelScale n
    have hθ := cepsLevelRate_pos n
    have hD := cepsLevelStepD_pos n
    have hM := (cepsLevelScale_pos n).le
    have hδ0 : 0 ≤ cepsLevelCutoff n := by
      have hdecay := trueDecayScaleBase_pos dom hW₀ hθ hD hM
      unfold cepsLevelCutoff
      have := dom.renewalMu_pos hD
      have := dom.μ₀_pos
      change 0 ≤ min (min dom.renewalMu (dom.μ₀ / 8))
        (min (dom.trueDecayScaleBase M / 4) (1 / 2))
      positivity
    let B := min 1 (min (dom.trueFrequencyScaleRadius M 1 0) (dom.trueTransformFrequencyBase M / 2))
    have hB : 0 < B := lt_min one_pos (lt_min
      (trueFrequencyScaleRadius_pos dom hW₀ hθ hD hM 1 0)
        (half_pos (trueTransformFrequencyBase_pos dom hW₀ hθ hD hM)))
    refine ⟨32 * dom.trueNormalFixedTaylorConstant M (cepsLevelCutoff n), max 1 (1 / B),
      mul_nonneg (by norm_num) (trueNormalFixedTaylorConstant_nonneg dom hW₀ hθ hD M hδ0),
      le_max_left _ _, ?_⟩
    intro eps heps ν hν y hy
    obtain ⟨f, -, -, -, hW, hf, hfM⟩ := hν.stepLaw
    have heps1 : 1 ≤ eps := (le_max_left _ _).trans heps
    have heps0 : 0 < eps := zero_lt_one.trans_le heps1
    have hepsB : 1 / B ≤ eps := (le_max_right _ _).trans heps
    have hepsmul : 1 ≤ B * eps := by have ht := (div_le_iff₀ hB).mp hepsB; nlinarith
    have hb : 0 < (2 * eps)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) heps0)
    have hbB : (2 * eps)⁻¹ < B := by
      rw [inv_eq_one_div]
      exact (div_lt_iff₀ (mul_pos (by norm_num) heps0)).mpr (by nlinarith)
    have hb1 : (2 * eps)⁻¹ ≤ 1 := hbB.le.trans (min_le_left _ _)
    have hbs1 : (((2 * eps)⁻¹ : ℝ) : ℂ) ∈ ball 0 (dom.trueFrequencyScaleRadius M 1 0) := by
      rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos hb]
      exact hbB.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hbband : 2 * (2 * eps)⁻¹ < dom.trueTransformFrequencyBase M := by
      have ht := hbB.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      linarith
    have hn : ‖I * (y : ℂ)‖ = |y| := by
      rw [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]
    have ht := cepsScaledTrueNormalExpression_fixed_zero_window_taylor dom hW hθ hD hf
      (cepsLevelDomain_two_c₀_le n) hfM (by norm_num [cepsLevelOrder]) hb hb1 hδ0
      (cepsLevelCutoff_le n).2.2.1 hbs1 hbband (by simp : (I * (y : ℂ)).re = 0)
      (by simpa only [hn] using hy)
    rw [hn, sq_abs] at ht
    have he : dom.trueNormalFixedTaylorConstant M (cepsLevelCutoff n) / ((2 * eps)⁻¹) ^ 5 * y ^ 2 =
        (32 * dom.trueNormalFixedTaylorConstant M (cepsLevelCutoff n)) * eps ^ 5 * y ^ 2 := by
      rw [inv_pow, div_inv_eq_mul]
      ring
    exact ht.trans_eq he
  · exact ⟨0, 1, le_rfl, le_rfl, fun _ _ ν hν => False.elim (hex ⟨ν, hν⟩)⟩

end PGM
