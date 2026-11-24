import PLAStochastic.Index.CEPS.Total.LevelTaylor
import PLAStochastic.Index.CEPS.Scaled.ContourLowClass

/-! # Class-uniform raw low-band series on each fixed canonical level -/

noncomputable section
open Complex MeasureTheory PowerSeries Finset
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsLevelDomain

theorem ceps_low_level (n P : ℕ) {η' M' : ℝ} (hη' : 0 < η') (hM' : 0 ≤ M') :
    ∃ K R eps₀ : ℝ, 0 ≤ K ∧ 0 < R ∧ 1 ≤ eps₀ ∧
      ∀ eps : ℝ, eps₀ ≤ eps → ∀ ν : ProbabilityMeasure ℝ, ∀ f : ℝ → ℝ,
        CepsLevelDensity n ν f → CepsSobolevClass (P + 3) η' (fun x => f (1 - x)) →
        cepsSobolev (P + 3) η' (fun x => f (1 - x)) ≤ M' →
          ∀ y : ℝ, |y| ≤ R * eps ^ 2 →
          ‖cepsScaledTrueNormalExpression (cepsLevelDomain n)
              ((ν : Measure ℝ).map fun x => 1 - x) (2 * eps)⁻¹ (cepsLevelCutoff n) (I * y) -
            ∑ j ∈ range (P + 1), ((((2 * eps)⁻¹) ^ j : ℝ) : ℂ) *
              coeff j (cepsScaledNormalSeries ((cepsLevelDomain n).contour η' hη')
                ((ν : Measure ℝ).map fun x => 1 - x) P (I * y))‖ ≤
            K * (eps⁻¹) ^ (P + 1) * (1 + |y|) ^ (P + 4) := by
  by_cases hex : ∃ ν, CepsLevel n ν
  · obtain ⟨ν₀, hν₀⟩ := hex
    obtain ⟨f₀, -, -, -, hW₀, -, -⟩ := hν₀.stepLaw
    let dom := cepsLevelDomain n
    let M := cepsLevelScale n
    have hθ := cepsLevelRate_pos n
    have hD := cepsLevelStepD_pos n
    have hM := (cepsLevelScale_pos n).le
    have hδ : 0 < cepsLevelCutoff n := by
      have hbase := trueDecayScaleBase_pos dom hW₀ hθ hD hM
      unfold cepsLevelCutoff
      change 0 < min (min dom.renewalMu (dom.μ₀ / 8))
        (min (dom.trueDecayScaleBase M / 4) (1 / 2))
      exact lt_min (lt_min (dom.renewalMu_pos hD) (by have := dom.μ₀_pos; positivity))
        (lt_min (by positivity) (by norm_num))
    obtain ⟨K, R, E, hK, hR, hE, H⟩ := cepsScaledTrueNormalExpression_contour_low_band_class
      dom hW₀ hθ hD P hη' hM hM' hδ (cepsLevelCutoff_le n).2.2.1
    refine ⟨K, R, E, hK, hR, hE, fun eps heps ν f hν hf hMf y hy => ?_⟩
    obtain ⟨-, -, hW, hf6, hM6⟩ := hν.stepLaw
    exact H eps heps hW hf6 (cepsLevelDomain_two_c₀_le n) hM6
      (by norm_num [cepsLevelOrder]) hf hMf le_rfl y hy
  · refine ⟨0, 1, 1, le_rfl, one_pos, le_rfl, fun _ _ ν f hν _ _ _ _ => ?_⟩
    exact False.elim (hex ⟨ν, f, hν⟩)

end PGM
