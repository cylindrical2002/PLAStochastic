import PLAStochastic.Index.CEPS.Normal.ActualSignedFactors
import PLAStochastic.Index.CEPS.Normal.SignedNegativeDenominator
import PLAStochastic.Index.CEPS.Normal.ActualHalfDiscHolomorphy
import PLAStochastic.ForMathlib.Analysis.Complex.EvenSqrtPoint

/-! # Actual canonical holomorphy on a common negative-real extension

Signed-root holomorphy and root exchange remove the square-root branch cut.
The width-scaled negative strip is an explicit class domain, including the
Morse merger. Local neighborhoods at its points need not have a common radius.
-/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem actual_rootR_lt_rmax {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) :
    ‖cepsRootR D θ ρW μ q‖ < dom.rmax := by
  apply norm_sqrt_lt dom.rmax_pos
  have hm := cepsMorseMin_norm_le_class dom hW hθ hD hμ
  have hh := norm_sub_le q (cepsMorseMin D θ ρW μ)
  rw [dom.q₀_def] at hq
  nlinarith [sq_pos_of_pos dom.rmax_pos]

include hW hθ hD in
theorem descend_actual_signed {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ}
    (hq : ‖q‖ < dom.q₀) (hne : q - cepsMorseMin D θ ρW μ ≠ 0)
    {Φ H : ℂ → ℂ}
    (hΦ : ∀ r : ℂ, r ^ 2 = q - cepsMorseMin D θ ρW μ → DifferentiableAt ℂ Φ r)
    (heven : ∀ r ∈ dom.normalMorseSet ρW μ, Φ (-r) = Φ r)
    (hidentify : ∀ q' : ℂ, ‖q'‖ < dom.q₀ →
      Φ (sqrt (q' - cepsMorseMin D θ ρW μ)) = H q') :
    DifferentiableAt ℂ H q := by
  classical
  let m := cepsMorseMin D θ ρW (μ : ℂ)
  let U := dom.normalMorseSet ρW (μ : ℂ)
  let Ψ := fun r : ℂ => if r ∈ U then Φ r else 0
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hU : IsOpen U := cepsNormal_morseSet_open (ρW := ρW) dom (μ : ℂ)
  have hneg : ∀ r : ℂ, -r ∈ U ↔ r ∈ U := by
    intro r
    simp only [U, CepsCanonDomain.normalMorseSet, mem_inter_iff, mem_ball_zero_iff,
      norm_neg, mem_ofPred_eq, cepsMorseDiscount_neg]
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
  have hder : ∀ r : ℂ, r ^ 2 = q - m → DifferentiableAt ℂ Ψ r := by
    intro r hr
    have he : Ψ =ᶠ[𝓝 r] Φ := by
      filter_upwards [hU.mem_nhds (hmember r hr)] with r' hr'
      simp only [Ψ, if_pos hr']
    exact (hΦ r hr).congr_of_eventuallyEq he
  have he : ∀ r, Ψ (-r) = Ψ r := by
    intro r
    dsimp only [Ψ]
    rw [hneg]
    split_ifs with hr
    · exact heven r hr
    · rfl
  have hd := differentiableAt_comp_sqrt_of_even_of_ne_zero hne
    (hder _ (sqrt_sq_eq _)) (hder _ (I_mul_sqrt_neg_sq _)) he
  have hcomp := hd.comp q (differentiableAt_id.sub_const m)
  have heq : (fun q' => Ψ (sqrt (q' - m))) =ᶠ[𝓝 q] H := by
    have hqn : ∀ᶠ q' : ℂ in 𝓝 q, ‖q'‖ < dom.q₀ :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hq
    filter_upwards [hqn] with q' hq'
    have hr : sqrt (q' - m) ∈ U := by
      refine ⟨mem_ball_zero_iff.mpr ?_, ?_⟩
      · exact actual_rootR_lt_rmax dom hW hθ hD hμ' hq'.le
      · change ‖cepsMorseMin D θ ρW μ + (sqrt (q' - m)) ^ 2‖ < dom.q₀
        rw [sqrt_sq_eq, add_sub_cancel]
        exact hq'
    simp only [Ψ, if_pos hr]
    exact hidentify q' hq'
  exact hcomp.congr_of_eventuallyEq heq.symm

include hW hθ hD in
set_option maxHeartbeats 800000 in
theorem cepsNormal_actual_holomorphicAt_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q t : ℂ} (hq : ‖q‖ < dom.q₀) (ht : ‖t‖ < dom.c₀ / 2)
    {l : ℝ} (hl : dom.normalNegativeWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    DifferentiableAt ℂ (fun q' => (cepsWHNormalData D θ ρW μ q').regularEntrance
      (dom.canonL ρW) μ q' l t) q ∧
    DifferentiableAt ℂ (fun q' => (cepsWHNormalData D θ ρW μ q').regularBridge
      (dom.canonL ρW) μ q' l) q := by
  let m := cepsMorseMin D θ ρW (μ : ℂ)
  by_cases hmerge : q = m
  · have hlbase := (le_max_left dom.normalWidthThreshold (6 * dom.normalPiBound)).trans hl
    have hM := (cepsNormal_width_properties dom hW hθ hD hlbase).2.1
    obtain ⟨ε, hε, hE, hB⟩ := cepsNormal_actual_holomorphic_near_morseMinimum
      dom hW hθ hD hμ ht hM
    have hmem : q ∈ ball m (ε ^ 2) := hmerge ▸ mem_ball_self (by positivity)
    exact ⟨(hE q hmem).differentiableAt (isOpen_ball.mem_nhds hmem),
      (hB q hmem).differentiableAt (isOpen_ball.mem_nhds hmem)⟩
  have hne : q - m ≠ 0 := sub_ne_zero.mpr hmerge
  let A := cepsMorseNormalData D θ ρW (μ : ℂ)
  let Q := cepsMorseDiscount D θ ρW (μ : ℂ)
  let U := dom.normalMorseSet ρW (μ : ℂ)
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hU : IsOpen U := cepsNormal_morseSet_open (ρW := ρW) dom (μ : ℂ)
  have hG := cepsMorseNormalData_normalG_differentiableOn_full dom hW hθ hD hμ (l : ℂ)
  obtain ⟨hbpmap, hbmmap⟩ := cepsMorseNormalData_root_maps_full dom hW hθ hD hμ
  have hGjets : ∀ r ∈ U,
      DifferentiableAt ℂ ((A r).normalG (dom.canonL ρW) μ (Q r) l) (A r).βp ∧
      DifferentiableAt ℂ ((A r).normalG (dom.canonL ρW) μ (Q r) l) (A r).βm := by
    intro r hr
    exact ⟨differentiableAt_slice_snd (hU.prod isOpen_ball) hG ⟨hr, hbpmap hr⟩,
      differentiableAt_slice_snd (hU.prod isOpen_ball) hG ⟨hr, hbmmap hr⟩⟩
  have hder : ∀ r : ℂ, r ^ 2 = q - m →
      DifferentiableAt ℂ (fun r' => (A r').regularEntrance (dom.canonL ρW) μ (Q r') l t) r ∧
      DifferentiableAt ℂ (fun r' => (A r').regularBridge (dom.canonL ρW) μ (Q r') l) r := by
    intro r hr
    have hmember : r ∈ U := by
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
    exact cepsMorseNormalData_holomorphicAt_of_dslope_ne dom hW hθ hD hμ hmember ht
      (cepsMorseNormalData_dslope_ne_zero_negative dom hW hθ hD hμ hq.le hr hl hre)
  have hidentify : ∀ q' : ℂ, Q (sqrt (q' - m)) = q' := by
    intro q'
    dsimp [Q, cepsMorseDiscount]
    rw [sqrt_sq_eq, add_sub_cancel]
  constructor
  · refine descend_actual_signed dom hW hθ hD hμ hq hne (fun r hr => (hder r hr).1) ?_ ?_
    · intro r hr
      dsimp only [A, Q]
      rw [cepsMorseNormalData_neg, cepsMorseDiscount_neg]
      exact (A r).regularEntrance_swap (dom.canonL ρW) μ (Q r) l t
        (hGjets r hr).1 (hGjets r hr).2
    · intro q' _
      rw [hidentify]
      dsimp only [A]
      rw [cepsMorseNormalData_sqrt_eq]
  · refine descend_actual_signed dom hW hθ hD hμ hq hne (fun r hr => (hder r hr).2) ?_ ?_
    · intro r _
      dsimp only [A, Q]
      rw [cepsMorseNormalData_neg, cepsMorseDiscount_neg]
      exact (A r).regularBridge_swap (dom.canonL ρW) μ (Q r) l
    · intro q' _
      rw [hidentify]
      dsimp only [A]
      rw [cepsMorseNormalData_sqrt_eq]

end PGM
