import PLAStochastic.Index.CEPS.Normal.NegativeHolomorphy
import PLAStochastic.ForMathlib.Analysis.Complex.EvenSqrtLocal

/-! # Actual negative-discount holomorphy with a moving analytic marker -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMorseNormalData_holomorphic_near_markerCurve {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    (T : ℂ → ℂ) (hT : Differentiable ℂ T) {r : ℂ}
    (hr : r ∈ dom.normalMorseSet ρW μ)
    (ht : ‖T (cepsMorseDiscount D θ ρW μ r)‖ < dom.c₀ / 2) {l : ℝ}
    (hS : dslope ((cepsMorseNormalData D θ ρW μ r).normalG (dom.canonL ρW) μ
      (cepsMorseDiscount D θ ρW μ r) l)
        (cepsMorseNormalData D θ ρW μ r).βm (cepsMorseNormalData D θ ρW μ r).βp ≠ 0) :
    ∃ ε > 0, DifferentiableOn ℂ (fun r' => (cepsMorseNormalData D θ ρW μ r').regularEntrance
      (dom.canonL ρW) μ (cepsMorseDiscount D θ ρW μ r') l
        (T (cepsMorseDiscount D θ ρW μ r'))) (ball r ε) := by
  let V := dom.normalMorseSet ρW (μ : ℂ)
  let Q := cepsMorseDiscount D θ ρW (μ : ℂ)
  let A := cepsMorseNormalData D θ ρW (μ : ℂ)
  let U := V ∩ {r | ‖T (Q r)‖ < dom.c₀ / 2}
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hQd : Differentiable ℂ Q := by unfold Q cepsMorseDiscount; fun_prop
  have hU : IsOpen U := (cepsNormal_morseSet_open (ρW := ρW) dom (μ : ℂ)).inter
    (isOpen_lt ((hT.comp hQd).continuous.norm) continuous_const)
  have hsub : U ⊆ V := inter_subset_left
  have hΘ := cepsMorseRoot_differentiableOn_r dom hW hθ hD hμ'
  have hbp : DifferentiableOn ℂ (fun r => (A r).βp) U :=
    (hΘ.mono inter_subset_left).mono hsub
  have hbm : DifferentiableOn ℂ (fun r => (A r).βm) U := by
    exact ((hΘ.comp (f := fun r : ℂ => -r) differentiableOn_id.neg
      (fun r hr => mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hr))).mono
        inter_subset_left).mono hsub
  obtain ⟨hp, hm⟩ := cepsMorseNormalData_root_maps_full dom hW hθ hD hμ
  have htA : T (Q r) ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hQt := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hr.2.le htA
  obtain ⟨ε, hε, hE, _⟩ := cepsNormal_holomorphic_near_of_dslope_ne
    (A := A) (L := dom.canonL ρW) (μ := (μ : ℂ)) (q := Q) (t := T ∘ Q) hU
    ((cepsMorseNormalData_Q_differentiableOn_full dom hW hθ hD hμ').mono
      (fun _ hx => ⟨hsub hx.1, hx.2⟩))
    ((cepsMorse_canonL_differentiableOn_full dom hW hθ hD hμ).mono
      (fun _ hx => ⟨hsub hx.1, hx.2⟩))
    hbp hbm (hT.comp hQd).differentiableOn
    (fun _ hu => hp (hsub hu)) (fun _ hu => hm (hsub hu))
    (fun _ hu => mem_ball_zero_iff.mpr hu.2) ⟨hr, ht⟩ hS hQt
  exact ⟨ε, hε, hE⟩

include hW hθ hD in
theorem descend_actual_signed_at_merge {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    (hq : ‖cepsMorseMin D θ ρW μ‖ < dom.q₀) {Φ H : ℂ → ℂ}
    (hΦ : ∃ ε > 0, DifferentiableOn ℂ Φ (ball 0 ε))
    (heven : ∀ r ∈ dom.normalMorseSet ρW μ, Φ (-r) = Φ r)
    (hidentify : ∀ q' : ℂ, ‖q'‖ < dom.q₀ →
      Φ (sqrt (q' - cepsMorseMin D θ ρW μ)) = H q') :
    DifferentiableAt ℂ H (cepsMorseMin D θ ρW μ) := by
  classical
  let m := cepsMorseMin D θ ρW (μ : ℂ)
  let U := dom.normalMorseSet ρW (μ : ℂ)
  let Ψ := fun r : ℂ => if r ∈ U then Φ r else 0
  have hU : IsOpen U := cepsNormal_morseSet_open (ρW := ρW) dom (μ : ℂ)
  have h0 : (0 : ℂ) ∈ U := by
    refine ⟨mem_ball_self dom.rmax_pos, ?_⟩
    change ‖cepsMorseDiscount D θ ρW μ 0‖ < dom.q₀
    simpa only [cepsMorseDiscount, zero_pow (by decide : 2 ≠ 0), add_zero] using hq
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hU 0 h0
  obtain ⟨ε, hε, hd⟩ := hΦ
  let R := min δ ε
  have hR : 0 < R := lt_min hδ hε
  have hΨ : DifferentiableOn ℂ Ψ (ball 0 R) :=
    (hd.mono (ball_subset_ball (min_le_right _ _))).congr fun r hr =>
      by simp only [Ψ, if_pos (hsub (ball_subset_ball (min_le_left _ _) hr))]
  have hneg : ∀ r : ℂ, -r ∈ U ↔ r ∈ U := by
    intro r
    simp only [U, CepsCanonDomain.normalMorseSet, mem_inter_iff, mem_ball_zero_iff,
      norm_neg, mem_ofPred_eq, cepsMorseDiscount_neg]
  have he : ∀ r, Ψ (-r) = Ψ r := by
    intro r
    dsimp only [Ψ]
    rw [hneg]
    split_ifs with hr
    · exact heven r hr
    · rfl
  have hs := ((differentiableOn_comp_sqrt_of_even hR hΨ he) 0 (mem_ball_self (by positivity))).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < R ^ 2)))
  have hs' : DifferentiableAt ℂ (fun w => Ψ (sqrt w)) (m - m) := by simpa using hs
  have hg : DifferentiableAt ℂ (fun q' : ℂ => q' - m) m := differentiableAt_id.sub_const m
  have hc : DifferentiableAt ℂ (fun q' : ℂ => Ψ (sqrt (q' - m))) m := by
    simpa only [Function.comp_def] using hs'.comp (f := fun q' : ℂ => q' - m) m hg
  have heq : (fun q' => Ψ (sqrt (q' - m))) =ᶠ[𝓝 m] H := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hq] with q' hq'
    have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
    have hr : sqrt (q' - m) ∈ U := by
      refine ⟨mem_ball_zero_iff.mpr (actual_rootR_lt_rmax dom hW hθ hD hμ' hq'.le), ?_⟩
      change ‖m + (sqrt (q' - m)) ^ 2‖ < dom.q₀
      rw [sqrt_sq_eq, add_sub_cancel]
      exact hq'
    simp only [Ψ, if_pos hr]
    exact hidentify q' hq'
  exact hc.congr_of_eventuallyEq heq.symm

include hW hθ hD in
theorem cepsNormal_actual_entrance_holomorphicAt_markerCurve_negative
    {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (T : ℂ → ℂ) (hT : Differentiable ℂ T)
    {q : ℂ} (hq : ‖q‖ < dom.q₀) (ht : ‖T q‖ < dom.c₀ / 2)
    {l : ℝ} (hl : dom.normalNegativeWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    DifferentiableAt ℂ (fun q' => (cepsWHNormalData D θ ρW μ q').regularEntrance
      (dom.canonL ρW) μ q' l (T q')) q := by
  let m := cepsMorseMin D θ ρW (μ : ℂ)
  let A := cepsMorseNormalData D θ ρW (μ : ℂ)
  let Q := cepsMorseDiscount D θ ρW (μ : ℂ)
  let U := dom.normalMorseSet ρW (μ : ℂ)
  let Φ := fun r => (A r).regularEntrance (dom.canonL ρW) μ (Q r) l (T (Q r))
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hU := cepsNormal_morseSet_open (ρW := ρW) dom (μ : ℂ)
  have hG := cepsMorseNormalData_normalG_differentiableOn_full dom hW hθ hD hμ (l : ℂ)
  obtain ⟨hp, hm⟩ := cepsMorseNormalData_root_maps_full dom hW hθ hD hμ
  have heven : ∀ r ∈ U, Φ (-r) = Φ r := by
    intro r hr
    dsimp only [Φ, A, Q]
    rw [cepsMorseNormalData_neg, cepsMorseDiscount_neg]
    exact (A r).regularEntrance_swap (dom.canonL ρW) μ (Q r) l (T (Q r))
      (differentiableAt_slice_snd (hU.prod isOpen_ball) hG ⟨hr, hp hr⟩)
      (differentiableAt_slice_snd (hU.prod isOpen_ball) hG ⟨hr, hm hr⟩)
  have hidentify : ∀ q' : ℂ, ‖q'‖ < dom.q₀ → Φ (sqrt (q' - m)) =
      (cepsWHNormalData D θ ρW μ q').regularEntrance (dom.canonL ρW) μ q' l (T q') := by
    intro q' _
    have hQ : Q (sqrt (q' - m)) = q' := by
      dsimp [Q, m, cepsMorseDiscount]
      rw [sqrt_sq_eq, add_sub_cancel]
    dsimp only [Φ]
    rw [hQ]
    dsimp only [A]
    rw [cepsMorseNormalData_sqrt_eq]
  have hnear : ∀ r : ℂ, r ^ 2 = q - m → ∃ ε > 0, DifferentiableOn ℂ Φ (ball r ε) := by
    intro r hr
    have hn : ‖r‖ = ‖cepsRootR D θ ρW μ q‖ := by
      have he : ‖r‖ ^ 2 = ‖cepsRootR D θ ρW μ q‖ ^ 2 := by
        rw [← norm_pow, ← norm_pow, hr]
        change ‖q - m‖ = ‖(sqrt (q - m)) ^ 2‖
        rw [sqrt_sq_eq]
      nlinarith [norm_nonneg r, norm_nonneg (cepsRootR D θ ρW μ q)]
    have hrU : r ∈ U := by
      refine ⟨mem_ball_zero_iff.mpr (hn.trans_lt (actual_rootR_lt_rmax dom hW hθ hD hμ' hq.le)), ?_⟩
      change ‖m + r ^ 2‖ < dom.q₀
      rw [hr, add_sub_cancel]
      exact hq
    have hQ : Q r = q := by dsimp [Q, cepsMorseDiscount]; rw [hr, add_sub_cancel]
    exact cepsMorseNormalData_holomorphic_near_markerCurve dom hW hθ hD hμ T hT hrU
      (by rwa [← hQ] at ht) (cepsMorseNormalData_dslope_ne_zero_negative dom hW hθ hD hμ hq.le hr hl hre)
  by_cases hmerge : q = m
  · subst q
    exact descend_actual_signed_at_merge dom hW hθ hD hμ hq
      (hnear 0 (by simp)) heven hidentify
  · exact descend_actual_signed dom hW hθ hD hμ hq (sub_ne_zero.mpr hmerge)
      (fun r hr => by
        obtain ⟨ε, hε, hd⟩ := hnear r hr
        exact (hd r (mem_ball_self hε)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hε)))
      heven hidentify

end PGM
