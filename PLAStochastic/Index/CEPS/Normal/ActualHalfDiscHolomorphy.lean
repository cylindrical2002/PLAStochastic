import PLAStochastic.Index.CEPS.Normal.ActualDenominator
import PLAStochastic.Index.CEPS.Normal.HolomorphyNonzero
import PLAStochastic.Index.CEPS.Normal.ActualRootZoneHolomorphy

/-! # Canonical regular normal forms throughout the discount half-disc

The genuine divided-slope denominator is paid on the entire half-disc.
Every point in its radial interior has a full complex neighborhood where
both regular forms are holomorphic, including imaginary-axis points and
the root merger. No uniform neighborhood radius is claimed here.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

set_option maxHeartbeats 800000 in
theorem cepsNormal_actual_holomorphic_near_halfDisc
    {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
    (hθ : 0 < θ) (hD : 0 < D) {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q₀' t : ℂ} (hq : ‖q₀'‖ < dom.q₀) (hre : 0 ≤ q₀'.re)
    (ht : ‖t‖ < dom.c₀ / 2) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    ∃ ε > 0,
      DifferentiableOn ℂ (fun q =>
        (cepsWHNormalData D θ ρW μ q).regularEntrance (dom.canonL ρW) μ q l t)
        (ball q₀' ε) ∧
      DifferentiableOn ℂ (fun q =>
        (cepsWHNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l)
        (ball q₀' ε) := by
  let m := cepsMorseMin D θ ρW (μ : ℂ)
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hM := (cepsNormal_width_properties dom hW hθ hD hl).2.1
  by_cases hmerge : q₀' = m
  · obtain ⟨ε, hε, hE, hB⟩ := cepsNormal_actual_holomorphic_near_morseMinimum
      dom hW hθ hD hμ ht hM
    exact ⟨ε ^ 2, by positivity, hmerge ▸ hE, hmerge ▸ hB⟩
  let U : Set ℂ := ball 0 dom.q₀ ∩ {q | q - m ∈ slitPlane}
  let A : ℂ → CepsNormalData := fun q => cepsWHNormalData D θ ρW μ q
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_slitPlane.preimage (continuous_id.sub continuous_const))
  have hqmem : q₀' ∈ U := by
    refine ⟨mem_ball_zero_iff.mpr hq, ?_⟩
    have hnonneg : 0 ≤ (q₀' - m).re := by
      rw [sub_re]; linarith [re_cepsMorseMin_nonpos hW hθ hD (dom.μ_lt_chart hμ')]
    rcases eq_or_lt_of_le hnonneg with he | he
    · apply Or.inr
      intro hi
      apply hmerge
      apply sub_eq_zero.mp
      apply Complex.ext <;> simp_all
    · exact Or.inl he
  have hqnorm : ∀ q ∈ U, ‖q‖ ≤ dom.q₀ := fun q hq' =>
    (mem_ball_zero_iff.mp hq'.1).le
  have hsq : DifferentiableOn ℂ (fun q : ℂ => Complex.sqrt (q - m)) U := by
    intro q hq'
    exact ((differentiableAt_sqrt hq'.2).comp q (differentiableAt_id.sub_const m)).differentiableWithinAt
  have hΘ : DifferentiableOn ℂ (cepsMorseRoot D θ ρW (μ : ℂ))
      (ball 0 (cepsChartRho D θ)) := by
    exact (differentiableOn_cepsMorseRoot hW hθ hD).comp
      (f := fun r : ℂ => ((μ : ℂ), r))
      ((differentiableOn_const (μ : ℂ)).prodMk differentiableOn_id)
      (fun r hr => ⟨mem_ball_zero_iff.mpr (dom.μ_lt_chart hμ'), hr⟩)
  have hbp : DifferentiableOn ℂ (fun q => (A q).βp) U := hΘ.comp
    (f := fun q => Complex.sqrt (q - m)) hsq
    (fun q hq' => mem_ball_zero_iff.mpr (dom.norm_cepsRootR_lt hW hθ hD hμ' (hqnorm q hq')))
  have hbm : DifferentiableOn ℂ (fun q => (A q).βm) U := hΘ.comp
    (f := fun q => -Complex.sqrt (q - m)) hsq.neg
    (fun q hq' => mem_ball_zero_iff.mpr (by
      rw [norm_neg]
      exact dom.norm_cepsRootR_lt hW hθ hD hμ' (hqnorm q hq')))
  have hbpmap : MapsTo (fun q => (A q).βp) U (ball 0 (dom.c₀ / 2)) := by
    intro q hq'
    apply mem_ball_zero_iff.mpr
    change ‖cepsRootPlus D θ ρW μ q‖ < dom.c₀ / 2
    have := dom.norm_rootPlus_le hW hθ hD hμ' (hqnorm q hq')
    linarith [dom.c₀_pos]
  have hbmmap : MapsTo (fun q => (A q).βm) U (ball 0 (dom.c₀ / 2)) := by
    intro q hq'
    apply mem_ball_zero_iff.mpr
    change ‖cepsRootMinus D θ ρW μ q‖ < dom.c₀ / 2
    have := dom.norm_rootMinus_le hW hθ hD hμ' (hqnorm q hq')
    linarith [dom.c₀_pos]
  have hQ : DifferentiableOn ℂ (fun x : ℂ × ℂ => (A x.1).Q x.2)
      (U ×ˢ ball 0 (dom.c₀ / 2)) := by
    refine (cepsQ_differentiableOn_joint_q_spatial dom hW hθ hD hμ').mono ?_
    intro x hx
    refine ⟨?_, ?_⟩
    · have hn := norm_sub_le x.1 m
      have hm := cepsMorseMin_norm_le_class dom hW hθ hD hμ'
      have hqn := hqnorm x.1 hx.1
      rw [dom.q₀_def] at hqn
      change ‖x.1 - m‖ < dom.rmax ^ 2
      nlinarith [sq_pos_of_pos dom.rmax_pos]
    · apply mem_ball_zero_iff.mpr
      have := mem_ball_zero_iff.mp hx.2
      have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hLbase := dom.differentiableOn_cepsCanonL hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ' (ofReal_im μ)
  have hL : DifferentiableOn ℂ (fun x : ℂ × ℂ => dom.canonL ρW μ x.1 x.2)
      (U ×ˢ ball 0 (dom.c₀ / 2)) := by
    refine hLbase.comp (f := fun x : ℂ × ℂ => (x.2, x.1))
      (differentiableOn_snd.prodMk differentiableOn_fst) ?_
    intro x hx
    exact ⟨by have := mem_ball_zero_iff.mp hx.2; linarith [re_le_norm x.2, dom.c₀_pos],
      mem_ball_zero_iff.mp hx.1.1⟩
  have htA : t ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  exact cepsNormal_holomorphic_near_of_dslope_ne
    (A := A) (L := dom.canonL ρW) (μ := (μ : ℂ)) (q := fun q => q) (t := fun _ => t)
    (l := l) hU hQ hL hbp hbm (differentiableOn_const t) hbpmap hbmmap
    (fun _ _ => mem_ball_zero_iff.mpr ht) hqmem
    (cepsNormal_actual_dslope_ne_zero dom hW hθ hD hμ hq.le hre hl)
    (CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq.le htA)


/-- The original root-zone definitions inherit the full-neighborhood result. -/
theorem cepsNormalData_canonical_holomorphic_near_halfDisc
    {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
    (hθ : 0 < θ) (hD : 0 < D) {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q₀' t : ℂ} (hq : ‖q₀'‖ < dom.q₀) (hre : 0 ≤ q₀'.re)
    (ht : ‖t‖ < dom.c₀ / 2) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    ∃ ε > 0,
      DifferentiableOn ℂ (fun q =>
        (cepsNormalData D θ ρW μ q).regularEntrance (dom.canonL ρW) μ q l t)
        (ball q₀' ε) ∧
      DifferentiableOn ℂ (fun q =>
        (cepsNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l)
        (ball q₀' ε) := by
  obtain ⟨ρ, hρ, hE, hB⟩ := cepsNormal_actual_holomorphic_near_halfDisc
    dom hW hθ hD hμ hq hre ht hl
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  let ε := min ρ ((dom.q₀ - ‖q₀'‖) / 2)
  have hε : 0 < ε := lt_min hρ (by linarith)
  have hsub : ball q₀' ε ⊆ ball q₀' ρ := ball_subset_ball (min_le_left _ _)
  have hqbound : ∀ q ∈ ball q₀' ε, ‖q‖ ≤ dom.q₀ := by
    intro q hq'
    have hdist := mem_ball.mp hq'
    rw [dist_eq_norm] at hdist
    have hn := norm_add_le (q - q₀') q₀'
    rw [sub_add_cancel] at hn
    have heps := min_le_right ρ ((dom.q₀ - ‖q₀'‖) / 2)
    linarith
  have htA : t ∈ ball (0 : ℂ) dom.ρA := by
    apply mem_ball_zero_iff.mpr
    have := dom.c₀_le; have := dom.ρA_pos; linarith
  refine ⟨ε, hε, ?_, ?_⟩
  · apply (hE.mono hsub).congr
    intro q hq'
    exact (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμ' (hqbound q hq')
      (dom.canonL ρW) l htA).1.symm
  · apply (hB.mono hsub).congr
    intro q hq'
    exact (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμ' (hqbound q hq')
      (dom.canonL ρW) l htA).2.symm

/-- Holomorphy at each point includes the imaginary-axis boundary. -/
theorem cepsNormalData_canonical_analyticOnNhd_halfDisc
    {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
    (hθ : 0 < θ) (hD : 0 < D) {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {t : ℂ} (ht : ‖t‖ < dom.c₀ / 2) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    AnalyticOnNhd ℂ (fun q =>
      (cepsNormalData D θ ρW μ q).regularEntrance (dom.canonL ρW) μ q l t)
      {q : ℂ | ‖q‖ < dom.q₀ ∧ 0 ≤ q.re} ∧
    AnalyticOnNhd ℂ (fun q =>
      (cepsNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l)
      {q : ℂ | ‖q‖ < dom.q₀ ∧ 0 ≤ q.re} := by
  constructor
  · intro q hq
    obtain ⟨ε, hε, hE, -⟩ := cepsNormalData_canonical_holomorphic_near_halfDisc
      dom hW hθ hD hμ hq.1 hq.2 ht hl
    exact hE.analyticOnNhd isOpen_ball q (mem_ball_self hε)
  · intro q hq
    obtain ⟨ε, hε, -, hB⟩ := cepsNormalData_canonical_holomorphic_near_halfDisc
      dom hW hθ hD hμ hq.1 hq.2 ht hl
    exact hB.analyticOnNhd isOpen_ball q (mem_ball_self hε)

end PGM
