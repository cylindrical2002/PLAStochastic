import PLAStochastic.Index.CEPS.Scaled.CentralScaleBounds
import PLAStochastic.Index.CEPS.Normal.MovingSlopeContinuity
import PLAStochastic.Index.CEPS.Normal.MovingHolomorphicSlope

/-! # Joint continuous signed-coordinate quotient with holomorphic slices -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSigned_raw_analyticOnNhd {U : Set (ℂ × ℂ)} {lam : ℂ}
    (hmu : ∀ x ∈ U, ‖x.1 * lam‖ < cepsChartMu D θ) :
    AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × ℂ =>
      -cepsD ρW (x.1.1 * lam) (cepsScaledSignedDiscount D θ ρW lam x.1.2 x.1.1) x.2)
      (U ×ˢ ball 0 dom.ρA) := by
  have hM : AnalyticOnNhd ℂ (stepTransform ρW) (ball 0 (θ / 2)) :=
    (differentiableOn_stepTransform_ball hW hθ hD.le).analyticOnNhd isOpen_ball
  have hM' : AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × ℂ => stepTransform ρW x.2)
      (U ×ˢ ball 0 dom.ρA) := hM.comp analyticOnNhd_snd (fun x hx => by
    apply mem_ball_zero_iff.mpr
    have hn := mem_ball_zero_iff.mp hx.2
    have := CepsC6.ρA_lt_cgfRadius dom hθ hD
    have := cepsCgfRadius_le (D := D) (θ := θ)
    linarith)
  have hb : AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × ℂ => x.1.1) (U ×ˢ ball 0 dom.ρA) :=
    analyticOnNhd_fst.comp analyticOnNhd_fst (fun _ _ => mem_univ _)
  have hr : AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × ℂ => x.1.2) (U ×ˢ ball 0 dom.ρA) :=
    analyticOnNhd_snd.comp analyticOnNhd_fst (fun _ _ => mem_univ _)
  have hmuA := hb.mul (analyticOnNhd_const (v := lam))
  have hMin := ((differentiableOn_cepsMorseMin hW hθ hD).analyticOnNhd isOpen_ball).comp
    hmuA (fun x hx => mem_ball_zero_iff.mpr (hmu x.1 hx.1))
  have hq : AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × ℂ =>
      cepsScaledSignedDiscount D θ ρW lam x.1.2 x.1.1) (U ×ˢ ball 0 dom.ρA) :=
    hMin.add ((hb.mul hr).pow 2)
  have hE := (hmuA.mul analyticOnNhd_snd).cexp
  unfold cepsD
  exact ((analyticOnNhd_const (v := (1 : ℂ))).sub ((hq.neg.cexp.mul hE).mul hM')).neg

include hW hθ hD in
theorem cepsScaledCentral_physical_root_chart (N : ℕ) (M : ℝ) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW (x.1 * lam) (x.1 * x.2))
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) ∧
    MapsTo (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW (x.1 * lam) (x.1 * x.2))
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) (ball 0 dom.ρA) := by
  have hcoords : ∀ x ∈ ball (0 : ℂ) (dom.centralScaleRadius N M) ×ˢ
      ball 0 (dom.centralCoordinateRadius N M), ‖x.1 * lam‖ ≤ dom.μ₀ ∧ ‖x.1 * x.2‖ < dom.rmax := by
    intro x hx
    have h := cepsScaledCentral_chart_bounds dom hW hθ hD N M hlam (mem_ball_zero_iff.mp hx.2).le hx.1
    exact ⟨h.2.1.le.trans (by linarith [dom.μ₀_pos]), h.2.2.1⟩
  refine ⟨(differentiableOn_cepsMorseRoot hW hθ hD).comp
    ((differentiableOn_fst.mul_const lam).prodMk (differentiableOn_fst.mul differentiableOn_snd)) ?_, ?_⟩
  · intro x hx
    obtain ⟨hmu, hr⟩ := hcoords x hx
    refine ⟨mem_ball_zero_iff.mpr (dom.μ_lt_chart hmu), mem_ball_zero_iff.mpr ?_⟩
    change ‖x.1 * x.2‖ < cepsChartRho D θ
    have := dom.rmax_r1
    have := dom.rmax_pos
    linarith
  · intro x hx
    obtain ⟨hmu, hr⟩ := hcoords x hx
    exact cepsMorseRoot_mem_rootZone dom hW hθ hD hmu hr

include hW hθ hD in
theorem cepsScaledSignedQuotient_continuousOn_central (N : ℕ) (M : ℝ) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M) :
    ContinuousOn (fun x : (ℂ × ℂ) × ℂ => cepsMorseQ D θ ρW (x.1.1 * lam) (x.1.1 * x.1.2) x.2)
      ((ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) ×ˢ ball 0 dom.ρA) := by
  let U : Set (ℂ × ℂ) := ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)
  have hmu : ∀ x ∈ U, ‖x.1 * lam‖ < cepsChartMu D θ := by
    intro x hx
    have h := (cepsScaledCentral_chart_bounds dom hW hθ hD N M hlam (mem_ball_zero_iff.mp hx.2).le hx.1).2.1
    exact dom.μ_lt_chart (h.le.trans (by linarith [dom.μ₀_pos]))
  have hG := cepsScaledSigned_raw_analyticOnNhd dom hW hθ hD (U := U) (lam := lam) hmu
  obtain ⟨hp, hpmap⟩ := cepsScaledCentral_physical_root_chart dom hW hθ hD N M hlam
  have hn : MapsTo (fun x : ℂ × ℂ => (x.1, -x.2)) U U := fun x hx =>
    ⟨hx.1, mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hx.2)⟩
  have hm : DifferentiableOn ℂ
      (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW (x.1 * lam) (x.1 * (-x.2))) U :=
    hp.comp (differentiableOn_fst.prodMk differentiableOn_snd.neg) hn
  have hmmap : MapsTo (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW (x.1 * lam) (x.1 * (-x.2))) U
      (ball 0 dom.ρA) := hpmap.comp hn
  have hd : ∀ x ∈ U, DifferentiableOn ℂ
      (fun ζ => -cepsD ρW (x.1 * lam) (cepsScaledSignedDiscount D θ ρW lam x.2 x.1) ζ)
      (ball 0 dom.ρA) := fun x hx ζ hζ =>
    (hG (x, ζ) ⟨hx, hζ⟩).curry_right.differentiableAt.differentiableWithinAt
  have h := cepsNormal_continuousOn_joint_moving_second_dslope_general
    (E := ℂ × ℂ) (U := U) (R := dom.ρA)
    (G := fun x ζ => -cepsD ρW (x.1 * lam) (cepsScaledSignedDiscount D θ ρW lam x.2 x.1) ζ)
    (a := fun x => cepsMorseRoot D θ ρW (x.1 * lam) (x.1 * x.2))
    (b := fun x => cepsMorseRoot D θ ρW (x.1 * lam) (x.1 * (-x.2)))
    (isOpen_ball.prod isOpen_ball) hG.continuousOn hd hp.continuousOn hm.continuousOn hpmap hmmap
  simpa only [cepsMorseQ, cepsScaledSignedDiscount, mul_neg] using h

end PGM
