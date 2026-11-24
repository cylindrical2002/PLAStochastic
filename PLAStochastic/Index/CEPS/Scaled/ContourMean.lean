import PLAStochastic.Index.CEPS.Scaled.MeanSeries
import PLAStochastic.Index.CEPS.Scaled.ContourCanon
import PLAStochastic.Index.CEPS.Scaled.ContourCutoff

/-! # Expansion of the fixed normal slope using any positive Sobolev contour -/

noncomputable section
open Complex Set Metric MeasureTheory Finset PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)
variable {σ : ℝ} (hσ : 0 < σ) (hσc : σ ≤ dom.c₀)

include hW hθ hD in
theorem cepsScaledZeroEndpoint_shrink_eq {b : ℝ}
    (hb : |b| ≤ (dom.shrink σ hσ hσc).μ₀) :
    cepsScaledZeroEndpoint (dom.shrink σ hσ hσc) ρW b =
      cepsScaledZeroEndpoint dom ρW b := by
  have hq : ‖(0 : ℂ)‖ ≤ (dom.shrink σ hσ hσc).q₀ :=
    by simpa using (dom.shrink σ hσ hσc).q₀_pos.le
  have hζ : (0 : ℂ).re < σ := by simpa using hσ
  have hd := (dom.canonL_zeta_eventuallyEq_shrink hW hθ hD hσ hσc hb hq hζ).deriv_eq
  unfold cepsScaledZeroEndpoint
  rw [hd]
  rfl

include hW hθ hD in
theorem cepsScaledSurrogateZeroEndpoint_shrink_eq (N : ℕ) :
    cepsScaledSurrogateZeroEndpoint (dom.shrink σ hσ hσc) ρW N =
      cepsScaledSurrogateZeroEndpoint dom ρW N := by
  funext b
  unfold cepsScaledSurrogateZeroEndpoint
  rw [cepsCanonSpatialDriftTaylor_shrink_eq dom hW hθ hD hσ hσc N b
    (by simpa using (dom.shrink σ hσ hσc).q₀_pos.le)]

include hW hθ hD in
theorem cepsScaledTrueNormalSlope_contour_series_budget (N : ℕ)
    {η' M M' δ : ℝ} (hη' : 0 < η') (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hδ : 0 < δ) (hδactual : δ ≤ dom.trueDecayScaleBase M / 4) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ {ρW' : Measure ℝ} {fW' : ℝ → ℝ},
      IsStepLaw ρW' fW' D θ v → ∀ {m m' : ℕ} {η : ℝ},
      CepsSobolevClass m η fW' → 2 * dom.c₀ ≤ η → cepsSobolev m η fW' ≤ M → 2 ≤ m →
      CepsSobolevClass m' η' fW' → cepsSobolev m' η' fW' ≤ M' → N + 3 ≤ m' →
      ∀ {b : ℝ}, 0 < b → b < B →
        SeriesApprox (-cepsScaledTrueNormalSlope dom ρW' b δ)
          (cepsScaledMeanSeries (dom.contour η' hη') ρW' N) N b C := by
  let dom' := dom.contour η' hη'
  let δ' := min δ (dom'.trueDecayScaleBase M' / 8)
  let B := min (dom.trueDecayScaleBase M / 4)
    (min (dom'.trueDecayScaleBase M' / 4)
      (min (dom'.meanSeriesScaleBase N M') dom'.μ₀))
  let C := |dom'.meanSeriesBudgetConstant N M' δ'| +
    dom.trueCutoffTailIntegralConstant M δ' (N + 1)
  have hBase := trueDecayScaleBase_pos dom hW hθ hD hM
  have hBase' := trueDecayScaleBase_pos dom' hW hθ hD hM'
  have hSer := meanSeriesScaleBase_pos dom' hW hθ hD N hM'
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  have hδle : δ' ≤ δ := min_le_left _ _
  have hδsmall : δ' ≤ dom'.trueDecayScaleBase M' / 4 :=
    (min_le_right _ _).trans (by linarith)
  have hT := trueCutoffTailIntegralConstant_nonneg dom M hδ' (N + 1)
  have hB : 0 < B := by
    dsimp [B]
    exact lt_min (by positivity) (lt_min (by positivity) (lt_min hSer dom'.μ₀_pos))
  refine ⟨C, B, add_nonneg (abs_nonneg _) hT, hB, ?_⟩
  intro ρW' fW' hW' m m' η hf hη hMf hm hf' hMf' hm' b hb hsmall
  have hbz := hsmall.trans_le (min_le_left _ _)
  have hbz' := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hbSer := hsmall.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hbμ := hsmall.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hA := cepsScaledTrueNormalSlope_seriesApprox dom' hW' hθ hD hf'
    (dom.two_contour_c₀_le hη') hMf' N hm' hδ' hδsmall hb hbSer
  have hA' := hA.mono hb.le (le_abs_self _)
  have hI := cepsScaledTrueCutoffPair_shrink_integral_le dom hW' hθ hD
    (lt_min dom.c₀_pos (half_pos hη')) (min_le_left _ _) hf hη hMf hm hM'
    hb hδ' hδle hδactual hδsmall (z := 0) rfl
    (by simpa using hbz)
    (by simpa only [dom', CepsCanonDomain.contour, norm_zero, Real.sqrt_zero, add_zero,
      mul_one] using hbz') (N + 1)
  simp only [norm_zero, Real.sqrt_zero, add_zero, one_pow, mul_one, mul_zero,
    Real.exp_zero] at hI
  have hEnd := cepsScaledZeroEndpoint_shrink_eq dom hW' hθ hD
    (lt_min dom.c₀_pos (half_pos hη')) (min_le_left _ _)
    (b := b) (by simpa only [dom', CepsCanonDomain.contour, abs_of_pos hb] using hbμ.le)
  apply hA'.of_close hT
  rw [show -cepsScaledTrueNormalSlope dom ρW' b δ -
      -cepsScaledTrueNormalSlope dom' ρW' b δ' =
      (∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW' b δ 0 lam) -
        ∫ lam : ℝ, cepsScaledTrueCutoffPair dom' ρW' b δ' 0 lam by
      unfold cepsScaledTrueNormalSlope
      dsimp only [dom', CepsCanonDomain.contour]
      rw [hEnd]
      ring]
  exact hI

end PGM
