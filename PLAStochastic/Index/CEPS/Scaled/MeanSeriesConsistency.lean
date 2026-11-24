import PLAStochastic.Index.CEPS.Scaled.ContourMean
import PLAStochastic.ForMathlib.Analysis.Asymptotics.SeriesApproxUnique

/-! # Order and contour consistency of genuine normal mean coefficients -/

noncomputable section
open Complex Set Metric MeasureTheory PowerSeries
open PGM.WienerHopf
namespace PGM

def cepsScaledMeanCoeff {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (j : ℕ) : ℂ := coeff j (cepsScaledMeanSeries dom ρW j)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledMeanSeries_coeff_eq_of_order {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N Q : ℕ) (hN : N + 3 ≤ m) (hQ : Q + 3 ≤ m)
    (j : ℕ) (hjN : j ≤ N) (hjQ : j ≤ Q) :
    coeff j (cepsScaledMeanSeries dom ρW N) = coeff j (cepsScaledMeanSeries dom ρW Q) := by
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  let δ := dom.trueDecayScaleBase M / 8
  have hδ : 0 < δ := div_pos (trueDecayScaleBase_pos dom hW hθ hD hM0) (by norm_num)
  have hδactual : δ ≤ dom.trueDecayScaleBase M / 4 := by
    have := trueDecayScaleBase_pos dom hW hθ hD hM0
    dsimp [δ]
    linarith
  exact seriesApprox_coeff_eq_of_small_scale
    (f := fun b => -cepsScaledTrueNormalSlope dom ρW b δ)
    (meanSeriesScaleBase_pos dom hW hθ hD N hM0)
    (meanSeriesScaleBase_pos dom hW hθ hD Q hM0)
    (fun b hb hbR => cepsScaledTrueNormalSlope_seriesApprox dom hW hθ hD
      hf hη hM N hN hδ hδactual hb hbR)
    (fun b hb hbS => cepsScaledTrueNormalSlope_seriesApprox dom hW hθ hD
      hf hη hM Q hQ hδ hδactual hb hbS) hjN hjQ

include hW hθ hD in
theorem cepsScaledMeanSeries_coeff_eq_diagonal {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (j : ℕ) (hj : j ≤ N) :
    coeff j (cepsScaledMeanSeries dom ρW N) = cepsScaledMeanCoeff dom ρW j :=
  cepsScaledMeanSeries_coeff_eq_of_order dom hW hθ hD hf hη hM N j hN (by omega) j hj le_rfl

include hW hθ hD in
theorem cepsScaledMeanSeries_coeff_eq_of_contours {m m₁ m₂ : ℕ} {η η₁ η₂ M M₁ M₂ δ : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    (hη₁ : 0 < η₁) (hη₂ : 0 < η₂)
    (hf₁ : CepsSobolevClass m₁ η₁ fW) (hM₁ : cepsSobolev m₁ η₁ fW ≤ M₁)
    (hf₂ : CepsSobolevClass m₂ η₂ fW) (hM₂ : cepsSobolev m₂ η₂ fW ≤ M₂)
    (hδ : 0 < δ) (hδactual : δ ≤ dom.trueDecayScaleBase M / 4)
    (N Q : ℕ) (hN : N + 3 ≤ m₁) (hQ : Q + 3 ≤ m₂)
    (j : ℕ) (hjN : j ≤ N) (hjQ : j ≤ Q) :
    coeff j (cepsScaledMeanSeries (dom.contour η₁ hη₁) ρW N) =
      coeff j (cepsScaledMeanSeries (dom.contour η₂ hη₂) ρW Q) := by
  obtain ⟨C₁, B₁, _, hB₁, hbudget₁⟩ := cepsScaledTrueNormalSlope_contour_series_budget
    dom hW hθ hD N hη₁ ((cepsSobolev_nonneg m η fW).trans hM)
      ((cepsSobolev_nonneg m₁ η₁ fW).trans hM₁) hδ hδactual
  obtain ⟨C₂, B₂, _, hB₂, hbudget₂⟩ := cepsScaledTrueNormalSlope_contour_series_budget
    dom hW hθ hD Q hη₂ ((cepsSobolev_nonneg m η fW).trans hM)
      ((cepsSobolev_nonneg m₂ η₂ fW).trans hM₂) hδ hδactual
  exact seriesApprox_coeff_eq_of_small_scale
    (f := fun b => -cepsScaledTrueNormalSlope dom ρW b δ) hB₁ hB₂
    (fun b hb hbR => hbudget₁ hW hf hη hM hm hf₁ hM₁ hN hb hbR)
    (fun b hb hbS => hbudget₂ hW hf hη hM hm hf₂ hM₂ hQ hb hbS) hjN hjQ

end PGM
