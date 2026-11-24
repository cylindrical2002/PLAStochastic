import PLAStochastic.Index.CEPS.Scaled.CentralFrequencyRadius

/-! # A uniformly bounded central bridge and its complex frequency derivative -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledCentralSurrogateBridge {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam z b : ℂ) : ℂ :=
  cepsScaledDescendedSurrogateBridge dom ρW N lam (cepsScaledMorseRadicand D θ ρW lam z b) b

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledCentral_radicand_differentiableOn_joint (N : ℕ) (M : ℝ) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralFrequencyDriftRadius N M) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledMorseRadicand D θ ρW lam x.2 x.1)
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralFrequencyRadius N M)) := by
  have hL : ‖lam‖ ≤ dom.centralDriftRadius N M := hlam.trans (min_le_left _ _)
  have hR := centralCoordinateRadius_pos dom hW hθ hD N M
  have hUnit : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsMorseMinUnit D θ ρW (x.1 * lam))
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralFrequencyRadius N M)) :=
    (cepsMorseMinUnit_class_budget dom hW hθ hD).1.comp (differentiableOn_fst.mul_const lam)
      (fun x hx => by
        have hmu := (cepsScaledCentral_chart_bounds dom hW hθ hD N M hL
          (show ‖(0 : ℂ)‖ ≤ dom.centralCoordinateRadius N M by simpa using hR.le) hx.1).2.1
        exact mem_ball_zero_iff.mpr (hmu.trans (by linarith [dom.μ₀_pos])))
  exact (differentiableOn_snd.mul ((differentiableOn_const (1 : ℂ)).add
    (differentiableOn_fst.mul_const lam))).sub (hUnit.const_mul (lam ^ 2))

include hW hθ hD in
theorem cepsScaledCentralSurrogateBridge_differentiableOn_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) {lam : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralFrequencyDriftRadius N M) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledCentralSurrogateBridge dom ρW N lam x.2 x.1)
      (ball 0 (dom.centralScaleRadius N M) ×ˢ ball 0 (dom.centralFrequencyRadius N M)) := by
  have hd := cepsScaledDescendedSurrogateBridge_differentiableOn_joint dom hW hθ hD hf hη hM N hN
    (hlam.trans (min_le_left _ _))
  have hσ := cepsScaledCentral_radicand_differentiableOn_joint dom hW hθ hD N M hlam
  apply hd.comp (differentiableOn_fst.prodMk hσ)
  intro x hx
  have h := cepsScaledCentral_radicand_bounds dom hW hθ hD N M hlam (mem_ball_zero_iff.mp hx.2).le hx.1
  exact ⟨hx.1, mem_ball_zero_iff.mpr (h.trans (half_lt_self (sq_pos_of_pos
    (centralCoordinateRadius_pos dom hW hθ hD N M))))⟩

include hW hθ hD in
theorem cepsScaledCentralSurrogateBridge_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) {lam z b : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralFrequencyDriftRadius N M)
    (hz : ‖z‖ ≤ dom.centralFrequencyRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M)) :
    ‖cepsScaledCentralSurrogateBridge dom ρW N lam z b‖ ≤ dom.centralBridgeBound N M := by
  have hσ := cepsScaledCentral_radicand_bounds dom hW hθ hD N M hlam hz hb
  exact (cepsScaledDescendedSurrogateBridge_budget dom hW hθ hD hf hη hM N hN
    (hlam.trans (min_le_left _ _)) hb).2 _ (mem_ball_zero_iff.mpr
      (hσ.trans (half_lt_self (sq_pos_of_pos (centralCoordinateRadius_pos dom hW hθ hD N M)))))

include hW hθ hD in
theorem cepsScaledCentralSurrogateBridge_deriv_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) {lam z b : ℂ}
    (hlam : ‖lam‖ ≤ dom.centralFrequencyDriftRadius N M)
    (hz : ‖z‖ ≤ dom.centralFrequencyRadius N M)
    (hb : b ∈ ball (0 : ℂ) (dom.centralScaleRadius N M)) :
    ‖deriv (fun z => cepsScaledCentralSurrogateBridge dom ρW N lam z b) z‖ ≤
      2 * (dom.centralBridgeBound N M / (dom.centralCoordinateRadius N M ^ 2 / 4)) := by
  let σ := cepsScaledMorseRadicand D θ ρW lam z b
  have hL := hlam.trans (min_le_left _ _)
  have hσ := cepsScaledCentral_radicand_bounds dom hW hθ hD N M hlam hz hb
  have hR := centralCoordinateRadius_pos dom hW hθ hD N M
  have hσfull : σ ∈ ball (0 : ℂ) (dom.centralCoordinateRadius N M ^ 2) :=
    mem_ball_zero_iff.mpr (hσ.trans (half_lt_self (sq_pos_of_pos hR)))
  have hd := ((cepsScaledDescendedSurrogateBridge_budget dom hW hθ hD hf hη hM N hN hL hb).1
    σ hσfull).differentiableAt (isOpen_ball.mem_nhds hσfull) |>.hasDerivAt
  have hcurve : HasDerivAt (fun z => cepsScaledMorseRadicand D θ ρW lam z b) (1 + b * lam) z := by
    simpa only [cepsScaledMorseRadicand, one_mul] using ((hasDerivAt_id' z).mul_const (1 + b * lam)).sub_const
      (lam ^ 2 * cepsMorseMinUnit D θ ρW (b * lam))
  have he := (hd.comp z hcurve).deriv
  change deriv (fun z => cepsScaledCentralSurrogateBridge dom ρW N lam z b) z = _ at he
  rw [he, norm_mul]
  have hDσ := cepsScaledDescendedSurrogateBridge_deriv_bound dom hW hθ hD hf hη hM N hN hL hb
    (mem_ball_zero_iff.mpr hσ)
  have hw := (cepsScaledCentral_scale_bounds dom hW hθ hD N M hL
    (show ‖(0 : ℂ)‖ ≤ dom.centralCoordinateRadius N M by simpa using hR.le) hb).2.2.2.2
  have hw2 : ‖1 + b * lam‖ ≤ 2 := by
    have ht := norm_add_le ((1 + b * lam) - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at ht
    linarith
  have hC : 0 ≤ dom.centralBridgeBound N M / (dom.centralCoordinateRadius N M ^ 2 / 4) := by
    unfold CepsCanonDomain.centralBridgeBound
    have := boundedSpatialWeightLower_pos dom hD N M
    positivity
  exact (mul_le_mul hDσ hw2 (norm_nonneg _) hC).trans_eq (by ring)

end PGM
