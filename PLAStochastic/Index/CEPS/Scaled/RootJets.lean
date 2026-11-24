import PLAStochastic.Index.CEPS.Scaled.RootJetBase
import PLAStochastic.Index.CEPS.Normal.MovingSlopeAt
import PLAStochastic.ForMathlib.Analysis.Complex.ImplicitQuadraticJet

/-! # Genuine scaled-root Taylor coefficients read only finite cumulant jets -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v D' θ' v' : ℝ} {ρW ρW' : Measure ℝ} {fW fW' f f' : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (dom' : CepsCanonDomain D' θ' v')
  (hW : IsStepLaw ρW fW D θ v) (hW' : IsStepLaw ρW' fW' D' θ' v')
  (hθ : 0 < θ) (hD : 0 < D) (hθ' : 0 < θ') (hD' : 0 < D')

include dom hW hθ hD in
theorem cepsScaledSignedRoot_analyticAt_zero (lam : ℝ) {z sign : ℂ}
    (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1) :
    AnalyticAt ℂ (cepsScaledSignedRoot D θ ρW lam z sign) 0 := by
  have hs : ‖sign‖ ≤ 1 := by
    have hn := congrArg norm hsign
    rw [norm_pow, norm_one] at hn
    nlinarith [norm_nonneg sign]
  exact ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz hs).1.analyticOnNhd isOpen_ball) 0
    (mem_ball_self (actualRootScaleRadius_pos dom hW hθ hD lam z))

include dom dom' hW hW' hθ hD hθ' hD' in
theorem cepsScaledSignedRoot_taylorJets_congr (hfW : ∀ y, fW y = f (1 - y))
    (hfW' : ∀ y, fW' y = f' (1 - y)) (N : ℕ)
    (hp : ∀ i, i < cepsJetDim N → cepsJet f i = cepsJet f' i)
    (lam : ℝ) {z sign : ℂ} (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (cepsScaledSignedRoot D θ ρW lam z sign) 0) =
      coeff j (complexTaylorSeries (cepsScaledSignedRoot D' θ' ρW' lam z sign) 0) := by
  by_cases hne : lam ≠ 0 ∨ z ≠ 0
  · let ξ := cepsScaledSignedRoot D θ ρW lam z sign
    let ξ' := cepsScaledSignedRoot D' θ' ρW' lam z sign
    have ha := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz hsign
    have ha' := cepsScaledSignedRoot_analyticAt_zero dom' hW' hθ' hD' lam hz hsign
    have hH : AnalyticAt ℂ (cepsCgfUnit ρW) 0 :=
      (cepsCgfUnit_differentiableOn hW hθ hD).analyticOnNhd isOpen_ball 0
        (mem_ball_self (cepsCgfRadius_pos hD hθ))
    have hslope := cepsNormal_continuousAt_moving_dslope_of_analyticAt hH
      ((analyticAt_id (𝕜 := ℂ)).mul ha') ((analyticAt_id (𝕜 := ℂ)).mul ha)
      (by simp) (by simp)
    have hv := cepsStepVar_eq_of_cumulantJet_eq hW hθ hD hW' hθ' hD' hfW hfW'
      (hp _ (cepsJetCode_lt_cepsJetDim (by simp [cepsJetWeight])))
    have hzero : ξ 0 = ξ' 0 := by
      dsimp [ξ, ξ']
      rw [cepsScaledSignedRoot_zero dom hW hθ hD lam hz sign,
        cepsScaledSignedRoot_zero dom' hW' hθ' hD' lam hz sign, hv]
    have hgap := cepsScaledSignedRoot_zero_gap_ne dom hW hθ hD lam hz hne hsign
    have he : ∀ᶠ b : ℂ in 𝓝 0,
        ξ b ^ 2 * cepsCgfUnit ρW (b * ξ b) + (lam : ℂ) * ξ b =
        ξ' b ^ 2 * cepsCgfUnit ρW' (b * ξ' b) + (lam : ℂ) * ξ' b := by
      filter_upwards [cepsScaledSignedRoot_unit_equation_eventually dom hW hθ hD lam hz hsign,
        cepsScaledSignedRoot_unit_equation_eventually dom' hW' hθ' hD' lam hz hsign] with b hb hb'
      exact hb.trans hb'.symm
    obtain ⟨K, R, hK, hR, hunit⟩ := cepsCgfUnit_difference_le_of_cumulantJets hW hθ hD
      hW' hθ' hD' hfW hfW' N hp
    obtain ⟨C, B, hC, hB, hroot⟩ := implicitQuadraticRoot_difference_budget
      ha.continuousAt ha'.continuousAt hH.continuousAt hslope hzero hgap he N hR hK hunit
    apply complexTaylorSeries_coeff_eq_of_difference_le ha ha' N hB hC
    intro b hb hbB
    simpa only [norm_real, Real.norm_eq_abs, abs_of_pos hb] using
      hroot (b : ℂ) (by simpa only [norm_real, Real.norm_eq_abs, abs_of_pos hb] using hbB)
  · have hlam : lam = 0 := not_ne_iff.mp (fun h => hne (Or.inl h))
    have hz0 : z = 0 := not_ne_iff.mp (fun h => hne (Or.inr h))
    subst lam
    subst z
    rw [cepsScaledSignedRoot_zero_origin hW hθ hD,
      cepsScaledSignedRoot_zero_origin hW' hθ' hD']
    exact fun _ _ => rfl

end PGM
