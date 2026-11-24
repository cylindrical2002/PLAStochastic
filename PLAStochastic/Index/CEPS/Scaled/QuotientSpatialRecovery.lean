import PLAStochastic.Index.CEPS.Scaled.QuotientCurveJets

/-! # Exact genuine quotient jets along arbitrary analytic spatial curves -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology Asymptotics PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include dom hW hθ hD in
theorem cepsScaledQuotient_curve_eq_unit_eventually (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {ξ : ℂ → ℂ} (hξ : AnalyticAt ℂ ξ 0) :
    (fun b => cepsScaledQuotient D θ ρW lam z b (b * ξ b)) =ᶠ[𝓝 (0 : ℂ)]
      (fun b => cepsScaledUnitQuotient D θ ρW lam z b (ξ b)) := by
  let a := cepsScaledSignedRoot D θ ρW lam z 1
  let d := cepsScaledSignedRoot D θ ρW lam z (-1)
  let t := ξ
  have ha := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (1 : ℂ) ^ 2 = 1)
  have hd := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (-1 : ℂ) ^ 2 = 1)
  have ht := hξ
  let R : ℝ := 1 + ‖a 0‖ + ‖d 0‖ + ‖t 0‖
  have hR : 0 < R := by dsimp [R]; positivity
  have ha0 : a 0 ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (d 0), norm_nonneg (t 0)]
  have hd0 : d 0 ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (t 0)]
  have ht0 : t 0 ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (d 0)]
  have hscale : ∀ᶠ b : ℂ in 𝓝 0, b ∈ ball (0 : ℂ) (cepsCgfRadius D θ / R) :=
    ball_mem_nhds _ (div_pos (cepsCgfRadius_pos hD hθ) hR)
  filter_upwards [hscale, ha.continuousAt.eventually (isOpen_ball.mem_nhds ha0),
    hd.continuousAt.eventually (isOpen_ball.mem_nhds hd0),
    ht.continuousAt.eventually (isOpen_ball.mem_nhds ht0)] with b hbs hab hdb htb
  by_cases hb : b = 0
  · subst b
    simp only [zero_mul]
    rw [cepsScaledUnitQuotient_zero, cepsCgfUnit_zero hW hθ hD]
    simpa only [cepsScaledQuotientAtRoot, zero_mul] using
      cepsScaledQuotientAtRoot_zero hW hθ hD lam z (1 : ℂ)
  · have hbR : ‖b‖ * R ≤ cepsCgfRadius D θ :=
      ((lt_div_iff₀ hR).mp (mem_ball_zero_iff.mp hbs)).le
    exact cepsScaledQuotient_eq_unit_of_nonzero hW hθ hD lam z hb hbR hab hdb htb

theorem cepsCumulantJetQuotient_curve_analyticAt (p : ℕ → ℝ) (N : ℕ)
    (lam : ℝ) (z : ℂ) {ξ : ℂ → ℂ} (hξ : AnalyticAt ℂ ξ 0) :
    AnalyticAt ℂ (fun b => cepsCumulantJetQuotient p N lam z b (ξ b)) 0 := by
  let a := cepsCumulantRootModel p N lam z 1 N
  let d := cepsCumulantRootModel p N lam z (-1) N
  let t := ξ
  let R : ℝ := 1 + ‖a 0‖ + ‖d 0‖ + ‖t 0‖
  have hG : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => cepsCumulantQuotientSpatialUnit p N lam z x.1 x.2)
      (ball 0 1 ×ˢ ball 0 R) := fun x _ => cepsCumulantQuotientSpatialUnit_joint_analyticAt p N lam z x
  have ha : AnalyticAt ℂ a 0 := (cepsCumulantRootModel_differentiable p N lam z 1 N).analyticAt 0
  have hd : AnalyticAt ℂ d 0 := (cepsCumulantRootModel_differentiable p N lam z (-1) N).analyticAt 0
  have ht : AnalyticAt ℂ t 0 := hξ
  apply cepsNormal_analyticAt_moving_second_dslope (by norm_num : (0 : ℝ) < 1) hG ha hd ht
  · rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (d 0), norm_nonneg (t 0)]
  · rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (t 0)]
  · rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (d 0)]

include dom hW hθ hD in
theorem cepsScaledQuotient_curve_analyticAt (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {ξ : ℂ → ℂ} (hξ : AnalyticAt ℂ ξ 0) :
    AnalyticAt ℂ (fun b => cepsScaledQuotient D θ ρW lam z b (b * ξ b)) 0 := by
  have hcurve : AnalyticAt ℂ (fun b : ℂ => (b, b * ξ b)) 0 :=
    analyticAt_id.prod (analyticAt_id.mul hξ)
  have h0 : (0, (0 : ℂ) * ξ 0) ∈
      ball (0 : ℂ) (dom.canonScaleRadius lam z) ×ˢ ball 0 dom.ρA := by
    refine ⟨mem_ball_self (canonScaleRadius_pos dom hW hθ hD lam z), ?_⟩
    simpa only [zero_mul] using mem_ball_self dom.ρA_pos
  have he := analyticAt_complex_curve_of_differentiableOn
    (F := fun x : ℂ × ℂ => cepsScaledQuotient D θ ρW lam z x.1 x.2)
    (a := fun b : ℂ => (b, b * ξ b)) (isOpen_ball.prod isOpen_ball)
    (cepsScaledQuotient_differentiableOn dom hW hθ hD lam hz) hcurve h0
  exact he

include dom hW hθ hD in
theorem cepsScaledQuotient_curve_taylorJets_eq_finite_model (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {ξ : ℂ → ℂ} (hξ : AnalyticAt ℂ ξ 0) :
    ∀ j ≤ N, coeff j (complexTaylorSeries
      (fun b => cepsScaledQuotient D θ ρW lam z b (b * ξ b)) 0) =
      coeff j (complexTaylorSeries
        (fun b => cepsCumulantJetQuotient (cepsJet f) N lam z b (ξ b)) 0) := by
  have he := cepsScaledQuotient_curve_eq_unit_eventually dom hW hθ hD lam hz hξ
  have ha := cepsScaledQuotient_curve_analyticAt dom hW hθ hD lam hz hξ
  have hm := cepsCumulantJetQuotient_curve_analyticAt (cepsJet f) N lam z hξ
  have herr := cepsScaledUnitQuotient_curve_jet_isBigO dom hW hθ hD hfW N lam hz hξ
  have herr' : (fun b => cepsScaledQuotient D θ ρW lam z b (b * ξ b) -
      cepsCumulantJetQuotient (cepsJet f) N lam z b (ξ b))
      =O[𝓝 (0 : ℂ)] (fun b => b ^ (N + 1)) := by
    apply herr.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [he] with b hb
    rw [hb]
  exact complexTaylorSeries_coeff_eq_of_isBigO ha hm N herr'

end PGM
