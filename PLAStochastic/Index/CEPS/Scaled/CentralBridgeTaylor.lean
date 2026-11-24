import PLAStochastic.Index.CEPS.Scaled.CentralBridgeIdentification

/-! # Genuine central surrogate bridge scale Taylor budgets -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsScaledSurrogateBridge cepsScaledCentralSurrogateBridge

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledCentralSurrogateBridge_frequency_deriv_differentiableOn_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralFrequencyDriftRadius N M) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      deriv (fun z => cepsScaledCentralSurrogateBridge dom ρW N lam z x.1) x.2)
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralFrequencyRadius N M)) := by
  have hj := cepsScaledCentralSurrogateBridge_differentiableOn_joint dom hW hθ hD hf hη hM N hN hlam
  have hs : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledCentralSurrogateBridge dom ρW N lam x.1 x.2)
      (ball 0 (dom.centralFrequencyRadius N M) ×ˢ ball 0 (dom.centralScaleRadius N M)) :=
    hj.comp (f := fun x : ℂ × ℂ => (x.2, x.1)) (differentiableOn_snd.prodMk differentiableOn_fst)
      (fun _ hx => ⟨hx.2, hx.1⟩)
  exact (differentiableOn_deriv_fst (isOpen_ball.prod isOpen_ball) hs).comp
    (f := fun x : ℂ × ℂ => (x.2, x.1)) (differentiableOn_snd.prodMk differentiableOn_fst)
    (fun _ hx => ⟨hx.2, hx.1⟩)

include hW hθ hD in
theorem cepsScaledSurrogateBridge_central_scale_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ)
    (hlam : |lam| ≤ dom.centralFrequencyDriftRadius N M) {z : ℂ} (hz : 0 ≤ z.re)
    (hznorm : ‖z‖ < dom.centralFrequencyRadius N M) :
    DifferentiableOn ℂ (cepsScaledSurrogateBridge dom ρW N lam z) (ball 0 (dom.centralScaleRadius N M)) ∧
    DifferentiableOn ℂ (fun b => deriv (fun z => cepsScaledSurrogateBridge dom ρW N lam z b) z)
      (ball 0 (dom.centralScaleRadius N M)) ∧
    ∀ b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M),
      ‖cepsScaledSurrogateBridge dom ρW N lam z b‖ ≤ dom.centralBridgeBound N M ∧
      ‖deriv (fun z => cepsScaledSurrogateBridge dom ρW N lam z b) z‖ ≤
        2 * (dom.centralBridgeBound N M / (dom.centralCoordinateRadius N M ^ 2 / 4)) := by
  have hL : ‖(lam : ℂ)‖ ≤ dom.centralFrequencyDriftRadius N M := by simpa only [norm_real, Real.norm_eq_abs] using hlam
  have hR := centralCoordinateRadius_pos dom hW hθ hD N M
  have hmu : ∀ b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M), ‖b * (lam : ℂ)‖ < cepsChartMu D θ := by
    intro b hb
    have hc := (cepsScaledCentral_chart_bounds dom hW hθ hD N M (hL.trans (min_le_left _ _))
      (show ‖(0 : ℂ)‖ ≤ dom.centralCoordinateRadius N M by simpa using hR.le) hb).2.1
    exact dom.μ_lt_chart (hc.le.trans (by linarith [dom.μ₀_pos]))
  have hj := cepsScaledCentralSurrogateBridge_differentiableOn_joint dom hW hθ hD hf hη hM N hN hL
  have hdj := cepsScaledCentralSurrogateBridge_frequency_deriv_differentiableOn_joint dom hW hθ hD hf hη hM N hN hL
  have hmap : MapsTo (fun b : ℂ => (b, z)) (ball 0 (dom.centralScaleRadius N M))
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralFrequencyRadius N M)) :=
    fun _ hb => ⟨hb, mem_ball_zero_iff.mpr hznorm⟩
  refine ⟨(hj.comp (f := fun b : ℂ => (b, z))
      (differentiableOn_id.prodMk (differentiableOn_const z)) hmap).congr
      (fun b hb => (cepsScaledCentralSurrogateBridge_eq dom hW hθ hD N lam hz (hmu b hb)).symm),
    (hdj.comp (f := fun b : ℂ => (b, z))
      (differentiableOn_id.prodMk (differentiableOn_const z)) hmap).congr
      (fun b hb => cepsScaledCentralSurrogateBridge_deriv_eq dom hW hθ hD N lam hz (hmu b hb)), ?_⟩
  intro b hb
  rw [← cepsScaledCentralSurrogateBridge_eq dom hW hθ hD N lam hz (hmu b hb),
    cepsScaledCentralSurrogateBridge_deriv_eq dom hW hθ hD N lam hz (hmu b hb)]
  exact ⟨cepsScaledCentralSurrogateBridge_bound dom hW hθ hD hf hη hM N hN hL hznorm.le hb,
    cepsScaledCentralSurrogateBridge_deriv_bound dom hW hθ hD hf hη hM N hN hL hznorm.le hb⟩

include hW hθ hD in
theorem cepsScaledSurrogateBridge_central_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ)
    (hlam : |lam| ≤ dom.centralFrequencyDriftRadius N M) {z : ℂ} (hz : 0 ≤ z.re)
    (hznorm : ‖z‖ < dom.centralFrequencyRadius N M) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M / 2)) :
    ‖cepsScaledSurrogateBridge dom ρW N lam z b - complexTaylorSum (cepsScaledSurrogateBridge dom ρW N lam z) n 0 b‖ ≤
      ((n.factorial : ℝ) * dom.centralBridgeBound N M / (dom.centralScaleRadius N M / 4) ^ n) * ‖b‖ ^ n ∧
    ‖deriv (fun z => cepsScaledSurrogateBridge dom ρW N lam z b) z -
      complexTaylorSum (fun b => deriv (fun z => cepsScaledSurrogateBridge dom ρW N lam z b) z) n 0 b‖ ≤
      ((n.factorial : ℝ) * (2 * (dom.centralBridgeBound N M / (dom.centralCoordinateRadius N M ^ 2 / 4))) /
        (dom.centralScaleRadius N M / 4) ^ n) * ‖b‖ ^ n := by
  obtain ⟨hB, hDB, hbound⟩ := cepsScaledSurrogateBridge_central_scale_budget dom hW hθ hD hf hη hM N hN lam hlam hz hznorm
  have hR := centralScaleRadius_pos dom hW hθ hD N M
  exact ⟨by simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n hR hB (fun b hb => (hbound b hb).1) hb,
    by simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n hR hDB (fun b hb => (hbound b hb).2) hb⟩

end PGM
