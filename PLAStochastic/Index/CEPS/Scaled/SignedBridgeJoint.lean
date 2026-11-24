import PLAStochastic.Index.CEPS.Scaled.SignedSurrogateGSlices
import PLAStochastic.Index.CEPS.Scaled.CentralBridgeBudget
import PLAStochastic.Index.CEPS.Normal.TwoParameterEvaluation

/-! # Joint holomorphy of the uniformly bounded central signed bridge -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsScaledMorseChart

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledCentral_scaled_root_chart (N : ℕ) (M : ℝ) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledMorseChart D θ ρW lam x.2 x.1)
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) ∧
    MapsTo (fun x : ℂ × ℂ => cepsScaledMorseChart D θ ρW lam x.2 x.1)
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) (ball 0 1) := by
  have hR := centralCoordinateRadius_pos dom hW hθ hD N M
  have hL := centralDriftRadius_pos dom hW hθ hD N M
  have hbase : dom.centralScaleRadius N M ≤ dom.scaledMorseJointRadius lam (dom.centralCoordinateRadius N M) := by
    apply (min_le_left _ _).trans
    apply div_le_div_of_nonneg_left (lt_min dom.μ₀_pos dom.rmax_pos).le (by positivity)
    linarith
  refine ⟨(cepsScaledMorseChart_differentiableOn_joint dom hW hθ hD lam hR).mono
    (fun x hx => ⟨ball_subset_ball hbase hx.1, hx.2⟩), ?_⟩
  intro x hx
  have h := (cepsScaledCentral_chart_bounds dom hW hθ hD N M hlam (mem_ball_zero_iff.mp hx.2).le hx.1).2.2.2
  apply mem_ball_zero_iff.mpr
  have hroot : dom.boundedSpatialRootRadius N M ≤ 1 / 4 := min_le_left _ _
  linarith

include hW hθ hD in
theorem cepsScaledCentral_negative_scaled_root_chart (N : ℕ) (M : ℝ) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledMorseChart D θ ρW lam (-x.2) x.1)
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) ∧
    MapsTo (fun x : ℂ × ℂ => cepsScaledMorseChart D θ ρW lam (-x.2) x.1)
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) (ball 0 1) := by
  obtain ⟨hp, hpmap⟩ := cepsScaledCentral_scaled_root_chart dom hW hθ hD N M hlam
  have hn : MapsTo (fun x : ℂ × ℂ => (x.1, -x.2))
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M))
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) := fun x hx =>
    ⟨hx.1, mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hx.2)⟩
  have hh := hp.comp (f := fun x : ℂ × ℂ => (x.1, -x.2))
    (differentiableOn_fst.prodMk differentiableOn_snd.neg) hn
  refine ⟨?_, fun x hx => hpmap (hn hx)⟩
  simpa only [Function.comp_def] using! hh

include hW hθ hD in
theorem cepsScaledSignedSurrogateDenominator_differentiableOn_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) {lam : ℂ} (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSignedSurrogateDenominator dom ρW N lam x.2 x.1)
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) := by
  obtain ⟨hp, hpmap⟩ := cepsScaledCentral_scaled_root_chart dom hW hθ hD N M hlam
  obtain ⟨hm, hmmap⟩ := cepsScaledCentral_negative_scaled_root_chart dom hW hθ hD N M hlam
  exact cepsNormal_differentiableOn_two_parameter_moving_dslope
    (G := fun x ξ => cepsScaledSignedSurrogateG dom ρW N lam x.2 x.1 ξ)
    (a := fun x => cepsScaledMorseChart D θ ρW lam (-x.2) x.1)
    (b := fun x => cepsScaledMorseChart D θ ρW lam x.2 x.1)
    isOpen_ball isOpen_ball
    (cepsScaledSignedSurrogateG_continuousOn_joint dom hW hθ hD hf hη N hN hlam)
    (fun _r hr => cepsScaledSignedSurrogateG_scale_spatial_differentiableOn dom hW hθ hD hf hη N hN hlam hr)
    (fun _b hb => cepsScaledSignedSurrogateG_coordinate_spatial_differentiableOn dom hW hθ hD hf hη N hN hlam hb)
    hm hp hmmap hpmap

include hW hθ hD in
theorem cepsScaledSignedSurrogateG_eval_differentiableOn_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) {lam : ℂ} (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M)
    {a : (ℂ × ℂ) → ℂ}
    (ha : DifferentiableOn ℂ a (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)))
    (hamap : MapsTo a (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) (ball 0 1)) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSignedSurrogateG dom ρW N lam x.2 x.1 (a x))
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) :=
  cepsNormal_differentiableOn_two_parameter_eval
    (G := fun x ξ => cepsScaledSignedSurrogateG dom ρW N lam x.2 x.1 ξ) (a := a)
    isOpen_ball isOpen_ball
    (cepsScaledSignedSurrogateG_continuousOn_joint dom hW hθ hD hf hη N hN hlam)
    (fun _r hr => cepsScaledSignedSurrogateG_scale_spatial_differentiableOn dom hW hθ hD hf hη N hN hlam hr)
    (fun _b hb => cepsScaledSignedSurrogateG_coordinate_spatial_differentiableOn dom hW hθ hD hf hη N hN hlam hb)
    ha hamap

include hW hθ hD in
theorem cepsScaledSignedSurrogateBridge_differentiableOn_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralDriftRadius N M) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSignedSurrogateBridge dom ρW N lam x.2 x.1)
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M)) := by
  obtain ⟨hp, hpmap⟩ := cepsScaledCentral_scaled_root_chart dom hW hθ hD N M hlam
  obtain ⟨hm, hmmap⟩ := cepsScaledCentral_negative_scaled_root_chart dom hW hθ hD N M hlam
  have hGp := cepsScaledSignedSurrogateG_eval_differentiableOn_joint dom hW hθ hD hf hη N hN hlam hp hpmap
  have hGm := cepsScaledSignedSurrogateG_eval_differentiableOn_joint dom hW hθ hD hf hη N hN hlam hm hmmap
  have hS := cepsScaledSignedSurrogateDenominator_differentiableOn_joint dom hW hθ hD hf hη N hN hlam
  have hnon : ∀ x ∈ ball (0 : ℂ) (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralCoordinateRadius N M),
      cepsScaledSignedSurrogateDenominator dom ρW N lam x.2 x.1 ≠ 0 := by
    intro x hx
    have hlow := cepsScaledSignedSurrogateDenominator_central_lower dom hW hθ hD hf hη hM N hN hlam
      (mem_ball_zero_iff.mp hx.2).le hx.1
    exact norm_pos_iff.mp ((div_pos (boundedSpatialWeightLower_pos dom hD N M) (by norm_num : (0 : ℝ) < 8)).trans_le hlow)
  exact (hGp.neg.mul hGm).mul (hS.inv hnon)

end PGM
