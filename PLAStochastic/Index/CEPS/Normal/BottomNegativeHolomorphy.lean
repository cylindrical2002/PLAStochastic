import PLAStochastic.Index.CEPS.Normal.BottomHolomorphic
import PLAStochastic.Index.CEPS.Normal.NegativeHolomorphy

/-! # The lower-end normal entrance is holomorphic across the common negative strip -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
set_option maxHeartbeats 800000 in
theorem cepsNormal_actual_bottom_holomorphicAt_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ < dom.q₀) {l : ℝ} (hl : dom.normalNegativeWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    DifferentiableAt ℂ (fun q' => (cepsWHNormalData D θ ρW μ q').regularBottomEntrance
      (dom.canonL ρW) μ q' l) q := by
  let m := cepsMorseMin D θ ρW (μ : ℂ)
  let A := cepsMorseNormalData D θ ρW (μ : ℂ)
  let Q := cepsMorseDiscount D θ ρW (μ : ℂ)
  let U := dom.normalMorseSet ρW (μ : ℂ)
  let Φ := fun r => (A r).regularBottomEntrance (dom.canonL ρW) μ (Q r) l
  let H := fun q' => (cepsWHNormalData D θ ρW μ q').regularBottomEntrance (dom.canonL ρW) μ q' l
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hU : IsOpen U := cepsNormal_morseSet_open (ρW := ρW) dom (μ : ℂ)
  have hK := cepsMorseNormalData_normalK_differentiableOn_full dom hW hθ hD hμ (l : ℂ)
  obtain ⟨hbpmap, hbmmap⟩ := cepsMorseNormalData_root_maps_full dom hW hθ hD hμ
  have hKjets : ∀ r ∈ U,
      DifferentiableAt ℂ ((A r).normalK (dom.canonL ρW) μ (Q r) l) (A r).βp ∧
      DifferentiableAt ℂ ((A r).normalK (dom.canonL ρW) μ (Q r) l) (A r).βm := by
    intro r hr
    exact ⟨differentiableAt_slice_snd (hU.prod isOpen_ball) hK ⟨hr, hbpmap hr⟩,
      differentiableAt_slice_snd (hU.prod isOpen_ball) hK ⟨hr, hbmmap hr⟩⟩
  have heven : ∀ r ∈ U, Φ (-r) = Φ r := by
    intro r hr
    dsimp only [Φ, A, Q]
    rw [cepsMorseNormalData_neg, cepsMorseDiscount_neg]
    exact (A r).regularBottomEntrance_swap (dom.canonL ρW) μ (Q r) l
      (hKjets r hr).1 (hKjets r hr).2
  have hidentify : ∀ q' : ℂ, Φ (sqrt (q' - m)) = H q' := by
    intro q'
    have hQ : Q (sqrt (q' - m)) = q' := by
      dsimp [Q, cepsMorseDiscount]; rw [sqrt_sq_eq, add_sub_cancel]
    dsimp only [Φ, H]
    rw [hQ]
    dsimp only [A]
    rw [cepsMorseNormalData_sqrt_eq]
  have hmember : ∀ r : ℂ, r ^ 2 = q - m → r ∈ U := by
    intro r hr
    have hn : ‖r‖ = ‖cepsRootR D θ ρW μ q‖ := by
      have he : ‖r‖ ^ 2 = ‖cepsRootR D θ ρW μ q‖ ^ 2 := by
        rw [← norm_pow, ← norm_pow, hr]
        change ‖q - m‖ = ‖(sqrt (q - m)) ^ 2‖
        rw [sqrt_sq_eq]
      nlinarith [norm_nonneg r, norm_nonneg (cepsRootR D θ ρW μ q)]
    refine ⟨mem_ball_zero_iff.mpr ?_, ?_⟩
    · rw [hn]
      exact actual_rootR_lt_rmax dom hW hθ hD hμ' hq.le
    · change ‖cepsMorseMin D θ ρW μ + r ^ 2‖ < dom.q₀
      rw [hr, add_sub_cancel]
      exact hq
  have hnear : ∀ r : ℂ, r ^ 2 = q - m →
      ∃ ε > 0, ball r ε ⊆ U ∧ DifferentiableOn ℂ Φ (ball r ε) := by
    intro r hr
    exact cepsMorseNormalData_bottom_holomorphic_near_of_dslope_ne dom hW hθ hD hμ
      (hmember r hr) (cepsMorseNormalData_dslope_ne_zero_negative dom hW hθ hD hμ hq.le hr hl hre)
  by_cases hmerge : q = m
  · have hpoint : q - m = 0 := by rw [hmerge, sub_self]
    obtain ⟨ε, hε, hsub, hB⟩ := hnear 0 (by rw [hpoint]; norm_num)
    have hd := cepsNormal_sqrt_of_locally_even hε hB (fun r hr => heven r (hsub hr))
    have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (ε ^ 2) := mem_ball_self (by positivity)
    have hp : DifferentiableAt ℂ (fun z => Φ (sqrt z)) (q - m) := by
      rw [hpoint]
      exact (hd 0 h0).differentiableAt (isOpen_ball.mem_nhds h0)
    have hc := hp.comp q (differentiableAt_id.sub_const m)
    change DifferentiableAt ℂ (fun q' => Φ (sqrt (q' - m))) q at hc
    have heq : (fun q' => Φ (sqrt (q' - m))) = H := funext hidentify
    rwa [heq] at hc
  · apply descend_actual_signed dom hW hθ hD hμ hq (sub_ne_zero.mpr hmerge)
      (Φ := Φ) (H := H) ?_ heven (fun q' _ => hidentify q')
    intro r hr
    obtain ⟨ε, hε, _, hB⟩ := hnear r hr
    exact (hB r (mem_ball_self hε)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hε))

end PGM
