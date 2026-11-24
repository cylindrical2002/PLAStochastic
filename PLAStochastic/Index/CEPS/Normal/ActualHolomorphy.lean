import PLAStochastic.Index.CEPS.Normal.ActualJointFactors
import PLAStochastic.Index.CEPS.Normal.SquaredHolomorphyDifferentiable

/-! # Actual local normal forms through a Morse root merger

For a real small drift, a fixed marker in the root disc, and width above an
explicit class budget, the canonical regular entrance and bridge are
holomorphic on a full complex discount neighborhood of the Morse minimum.
The neighborhood radius is local; uniform full-domain bounds are separate.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

set_option maxHeartbeats 800000 in
theorem cepsNormal_actual_holomorphic_near_morseMinimum
    {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
    (hθ : 0 < θ) (hD : 0 < D) {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {t : ℂ} (ht : ‖t‖ < dom.c₀ / 2) {l : ℝ} (hl : dom.normalDerivativeBudget < l) :
    ∃ ε > 0,
      DifferentiableOn ℂ (fun q =>
        (cepsWHNormalData D θ ρW μ q).regularEntrance (dom.canonL ρW) μ q l t)
        (ball (cepsMorseMin D θ ρW μ) (ε ^ 2)) ∧
      DifferentiableOn ℂ (fun q =>
        (cepsWHNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l)
        (ball (cepsMorseMin D θ ρW μ) (ε ^ 2)) := by
  let A : ℂ → CepsNormalData := cepsMorseNormalData D θ ρW μ
  let q : ℂ → ℂ := cepsMorseDiscount D θ ρW μ
  let U : Set ℂ := ball 0 (dom.rmax / 4)
  let b : ℂ := cepsMorseRoot D θ ρW μ 0
  let m : ℂ := cepsMorseMin D θ ρW μ
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hU : IsOpen U := isOpen_ball
  have h0 : (0 : ℂ) ∈ U := mem_ball_self (by have := dom.rmax_pos; positivity)
  have hsub : U ⊆ ball (0 : ℂ) dom.rmax :=
    ball_subset_ball (by have := dom.rmax_pos; linarith)
  have hbp : DifferentiableOn ℂ (fun r => (A r).βp) U :=
    (cepsMorseRoot_differentiableOn_r dom hW hθ hD hμ').mono hsub
  have hbm : DifferentiableOn ℂ (fun r => (A r).βm) U := by
    have ha := cepsMorseRoot_differentiableOn_r dom hW hθ hD hμ'
    exact (ha.comp (f := fun r : ℂ => -r) differentiableOn_id.neg
      (fun r hr => mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hr))).mono hsub
  have hrootmap : ∀ r ∈ U, ‖cepsMorseRoot D θ ρW μ r‖ ≤ dom.c₀ / 4 :=
    fun r hr => cepsMorseRoot_norm_le dom hW hθ hD hμ' (mem_ball_zero_iff.mp (hsub hr))
  have hbpmap : MapsTo (fun r => (A r).βp) U (ball 0 (dom.c₀ / 2)) := by
    intro r hr
    apply mem_ball_zero_iff.mpr
    change ‖cepsMorseRoot D θ ρW μ r‖ < dom.c₀ / 2
    have := hrootmap r hr; have := dom.c₀_pos; linarith
  have hbmmap : MapsTo (fun r => (A r).βm) U (ball 0 (dom.c₀ / 2)) := by
    intro r hr
    have hrneg : -r ∈ U := mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hr)
    apply mem_ball_zero_iff.mpr
    change ‖cepsMorseRoot D θ ρW μ (-r)‖ < dom.c₀ / 2
    have := hrootmap (-r) hrneg; have := dom.c₀_pos; linarith
  have hQ : DifferentiableOn ℂ (fun x : ℂ × ℂ => (A x.1).Q x.2)
      (U ×ˢ ball 0 (dom.c₀ / 2)) :=
    cepsMorseNormalData_Q_differentiableOn dom hW hθ hD hμ'
  have hL : DifferentiableOn ℂ (fun x : ℂ × ℂ => dom.canonL ρW μ (q x.1) x.2)
      (U ×ˢ ball 0 (dom.c₀ / 2)) :=
    cepsMorse_canonL_differentiableOn dom hW hθ hD hμ
  have hroots : (A 0).βp = (A 0).βm := by simp only [A, cepsMorseNormalData, neg_zero]
  have hqm : ‖m‖ ≤ dom.q₀ := by
    have hm := cepsMorseMin_norm_le_class dom hW hθ hD hμ'
    dsimp [m]
    rw [dom.q₀_def]
    nlinarith [sq_nonneg dom.rmax]
  have hbn : ‖b‖ ≤ dom.c₀ / 4 := hrootmap 0 h0
  have hbA : b ∈ ball (0 : ℂ) dom.ρA := by
    apply mem_ball_zero_iff.mpr
    have := dom.c₀_le; have := dom.ρA_pos; linarith
  have htA : t ∈ ball (0 : ℂ) dom.ρA := by
    apply mem_ball_zero_iff.mpr
    have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hdQ := (CepsC6.differentiableAt_cepsQ dom hW hθ hD hμ' hqm hbA).hasDerivAt
  have hdL := (CepsC6.differentiableAt_canonL dom hW hθ hD hμ hqm
    (show b.re < dom.c₀ by linarith [re_le_norm b, dom.c₀_pos])).hasDerivAt
  have hQm0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hqm hbA
  have hQt0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hqm htA
  have hbudget := cepsNormal_actual_derivativeBudget dom hW hθ hD hμ hqm hbn
  have hqzero : q 0 = m := by simp only [q, cepsMorseDiscount, zero_pow (by decide : 2 ≠ 0), add_zero, m]
  have hbmzero : (A 0).βm = b := by simp only [A, cepsMorseNormalData, neg_zero, b]
  have hQzero : (A 0).Q = cepsQ D θ ρW μ m := by
    change cepsQ D θ ρW μ (q 0) = _
    rw [hqzero]
  obtain ⟨ε, hε, hE, hB⟩ := cepsNormal_holomorphic_in_square_near_merged_of_differentiable
    (A := A) (L := dom.canonL ρW) (μ := (μ : ℂ)) (q := q) (t := fun _ => t)
    (l := l) (M := dom.normalDerivativeBudget) hU hQ hL hbp hbm
    (differentiableOn_const t) hbpmap hbmmap (fun _ _ => mem_ball_zero_iff.mpr ht)
    (fun r _ => cepsMorseNormalData_neg D θ ρW μ r)
    (fun r _ => cepsMorseDiscount_neg D θ ρW μ r) (fun _ _ => rfl)
    h0 hroots (by simpa only [hQzero, hbmzero] using hdQ)
    (by simpa only [hqzero, hbmzero] using hdL)
    (by simpa only [hQzero, hbmzero] using hQm0)
    (by simpa only [hQzero] using hQt0)
    (by simpa only [hQzero, hbmzero] using hbudget) hl
  have hp : DifferentiableOn ℂ (fun q' => q' - m) (ball m (ε ^ 2)) :=
    differentiableOn_id.sub_const m
  have hmap : MapsTo (fun q' => q' - m) (ball m (ε ^ 2)) (ball 0 (ε ^ 2)) := by
    intro q' hq'
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hq'
  refine ⟨ε, hε, ?_, ?_⟩
  · apply (hE.comp (f := fun q' => q' - m) hp hmap).congr
    intro q' _
    change _ = (A (sqrt (q' - m))).regularEntrance (dom.canonL ρW) μ
      (q (sqrt (q' - m))) l t
    have hdata := cepsMorseNormalData_sqrt_eq D θ ρW (μ : ℂ) q'
    have hdisc : q (sqrt (q' - m)) = q' := by
      dsimp [q, m, cepsMorseDiscount]; rw [sqrt_sq_eq]; ring
    rw [hdisc]
    exact congrArg (fun a : CepsNormalData => a.regularEntrance (dom.canonL ρW) μ q' l t) hdata.symm
  · apply (hB.comp (f := fun q' => q' - m) hp hmap).congr
    intro q' _
    change _ = (A (sqrt (q' - m))).regularBridge (dom.canonL ρW) μ (q (sqrt (q' - m))) l
    have hdata := cepsMorseNormalData_sqrt_eq D θ ρW (μ : ℂ) q'
    have hdisc : q (sqrt (q' - m)) = q' := by
      dsimp [q, m, cepsMorseDiscount]; rw [sqrt_sq_eq]; ring
    rw [hdisc]
    exact congrArg (fun a : CepsNormalData => a.regularBridge (dom.canonL ρW) μ q' l) hdata.symm

end PGM
