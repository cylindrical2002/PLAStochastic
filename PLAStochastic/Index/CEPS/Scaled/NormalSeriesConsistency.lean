import PLAStochastic.Index.CEPS.Scaled.ContourLowBand
import PLAStochastic.ForMathlib.Analysis.Asymptotics.SeriesApproxUnique

/-! # Order and contour consistency of genuine normal-expansion coefficients -/

noncomputable section
open Complex Set Metric MeasureTheory PowerSeries
open PGM.WienerHopf
namespace PGM

def cepsScaledNormalCoeff {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (j : ℕ) (z : ℂ) : ℂ := coeff j (cepsScaledNormalSeries dom ρW j z)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledNormalSeries_coeff_eq_of_order {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N Q : ℕ) (hN : N + 3 ≤ m) (hQ : Q + 3 ≤ m)
    {z : ℂ} (hz : z.re = 0) (j : ℕ) (hjN : j ≤ N) (hjQ : j ≤ Q) :
    coeff j (cepsScaledNormalSeries dom ρW N z) = coeff j (cepsScaledNormalSeries dom ρW Q z) := by
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  let δ := dom.trueDecayScaleBase M / 8
  let H := 1 + Real.sqrt ‖z‖
  have hδ : 0 < δ := div_pos (trueDecayScaleBase_pos dom hW hθ hD hM0) (by norm_num)
  have hδactual : δ ≤ dom.trueDecayScaleBase M / 4 := by
    have := trueDecayScaleBase_pos dom hW hθ hD hM0
    dsimp [δ]
    linarith
  have hH : 0 < H := by dsimp [H]; positivity
  apply seriesApprox_coeff_eq_of_small_scale
    (f := fun b => cepsScaledTrueNormalExpression dom ρW b δ z)
    (R := dom.normalSeriesScaleBase N M / H) (S := dom.normalSeriesScaleBase Q M / H)
    (div_pos (normalSeriesScaleBase_pos dom hW hθ hD N hM0) hH)
    (div_pos (normalSeriesScaleBase_pos dom hW hθ hD Q hM0) hH)
    (fun b hb hbR => cepsScaledTrueNormalExpression_seriesApprox dom hW hθ hD
      hf hη hM N hN hδ hδactual hb hz ((lt_div_iff₀ hH).mp hbR))
    (fun b hb hbS => cepsScaledTrueNormalExpression_seriesApprox dom hW hθ hD
      hf hη hM Q hQ hδ hδactual hb hz ((lt_div_iff₀ hH).mp hbS)) hjN hjQ

include hW hθ hD in
theorem cepsScaledNormalSeries_coeff_eq_diagonal {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    {z : ℂ} (hz : z.re = 0) (j : ℕ) (hj : j ≤ N) :
    coeff j (cepsScaledNormalSeries dom ρW N z) = cepsScaledNormalCoeff dom ρW j z :=
  cepsScaledNormalSeries_coeff_eq_of_order dom hW hθ hD hf hη hM N j hN (by omega) hz j hj le_rfl

include hW hθ hD in
theorem cepsScaledNormalSeries_coeff_eq_of_contours {m m₁ m₂ : ℕ} {η η₁ η₂ M M₁ M₂ δ : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    (hη₁ : 0 < η₁) (hη₂ : 0 < η₂)
    (hf₁ : CepsSobolevClass m₁ η₁ fW) (hM₁ : cepsSobolev m₁ η₁ fW ≤ M₁)
    (hf₂ : CepsSobolevClass m₂ η₂ fW) (hM₂ : cepsSobolev m₂ η₂ fW ≤ M₂)
    (hδ : 0 < δ) (hδactual : δ ≤ dom.trueDecayScaleBase M / 4)
    (N Q : ℕ) (hN : N + 3 ≤ m₁) (hQ : Q + 3 ≤ m₂)
    {z : ℂ} (hz : z.re = 0) (j : ℕ) (hjN : j ≤ N) (hjQ : j ≤ Q) :
    coeff j (cepsScaledNormalSeries (dom.contour η₁ hη₁) ρW N z) =
      coeff j (cepsScaledNormalSeries (dom.contour η₂ hη₂) ρW Q z) := by
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  have hM₁0 := (cepsSobolev_nonneg m₁ η₁ fW).trans hM₁
  have hM₂0 := (cepsSobolev_nonneg m₂ η₂ fW).trans hM₂
  obtain ⟨C₁, B₁, _, hB₁, hbudget₁⟩ := cepsScaledTrueNormalExpression_contour_series_budget
    dom hW hθ hD N hη₁ hM0 hM₁0 hδ hδactual
  obtain ⟨C₂, B₂, _, hB₂, hbudget₂⟩ := cepsScaledTrueNormalExpression_contour_series_budget
    dom hW hθ hD Q hη₂ hM0 hM₂0 hδ hδactual
  let H := 1 + Real.sqrt ‖z‖
  have hH : 0 < H := by dsimp [H]; positivity
  exact seriesApprox_coeff_eq_of_small_scale
    (f := fun b => cepsScaledTrueNormalExpression dom ρW b δ z)
    (R := B₁ / H) (S := B₂ / H) (div_pos hB₁ hH) (div_pos hB₂ hH)
    (fun b hb hbR => hbudget₁ hf hη hM hm hf₁ hM₁ hN hb hz ((lt_div_iff₀ hH).mp hbR))
    (fun b hb hbS => hbudget₂ hf hη hM hm hf₂ hM₂ hQ hb hz ((lt_div_iff₀ hH).mp hbS)) hjN hjQ

end PGM
