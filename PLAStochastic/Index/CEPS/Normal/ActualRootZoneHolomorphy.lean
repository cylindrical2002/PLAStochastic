import PLAStochastic.Index.CEPS.Normal.ActualHolomorphy
import PLAStochastic.Index.CEPS.Normal.ActualEquality

/-! # Local canonical holomorphy for the original normal data -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

theorem cepsNormalData_canonical_holomorphic_near_morseMinimum
    {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
    (hθ : 0 < θ) (hD : 0 < D) {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {t : ℂ} (ht : ‖t‖ < dom.c₀ / 2) {l : ℝ} (hl : dom.normalDerivativeBudget < l) :
    ∃ ε > 0,
      DifferentiableOn ℂ (fun q =>
        (cepsNormalData D θ ρW μ q).regularEntrance (dom.canonL ρW) μ q l t)
        (ball (cepsMorseMin D θ ρW μ) ε) ∧
      DifferentiableOn ℂ (fun q =>
        (cepsNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l)
        (ball (cepsMorseMin D θ ρW μ) ε) := by
  obtain ⟨ρ, hρ, hE, hB⟩ := cepsNormal_actual_holomorphic_near_morseMinimum
    dom hW hθ hD hμ ht hl
  let m := cepsMorseMin D θ ρW (μ : ℂ)
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hm := cepsMorseMin_norm_le_class dom hW hθ hD hμ'
  have hmargin : 0 < dom.q₀ - ‖m‖ := by
    dsimp [m]
    rw [dom.q₀_def]
    nlinarith [sq_pos_of_pos dom.rmax_pos]
  let ε := min (ρ ^ 2) ((dom.q₀ - ‖m‖) / 2)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hsub : ball m ε ⊆ ball m (ρ ^ 2) := ball_subset_ball (min_le_left _ _)
  have hqbound : ∀ q ∈ ball m ε, ‖q‖ ≤ dom.q₀ := by
    intro q hq
    have hdist := mem_ball.mp hq
    rw [dist_eq_norm] at hdist
    have ht' := norm_add_le (q - m) m
    rw [sub_add_cancel] at ht'
    have heps := min_le_right (ρ ^ 2) ((dom.q₀ - ‖m‖) / 2)
    linarith
  have htA : t ∈ ball (0 : ℂ) dom.ρA := by
    apply mem_ball_zero_iff.mpr
    have := dom.c₀_le; have := dom.ρA_pos; linarith
  refine ⟨ε, hε, ?_, ?_⟩
  · apply (hE.mono hsub).congr
    intro q hq
    exact (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμ' (hqbound q hq)
      (dom.canonL ρW) l htA).1.symm
  · apply (hB.mono hsub).congr
    intro q hq
    exact (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμ' (hqbound q hq)
      (dom.canonL ρW) l htA).2.symm

end PGM
