import PLAStochastic.Index.CEPS.Normal.MovingJointSlope
import PLAStochastic.Index.CEPS.Normal.DividedDifferenceSymmetry
import PLAStochastic.Index.CEPS.Ident.CorollariesQ

/-! # The actual quadratic quotient in Morse coordinates

The signed Morse parameter is used before choosing a square-root branch.
Both roots and their collisions are included in the joint domain.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

/-- The actual quotient evaluated at the two signed Morse roots. -/
def cepsMorseQ (D θ : ℝ) (ρW : Measure ℝ) (μ r ζ : ℂ) : ℂ :=
  dslope (dslope (fun z => -cepsD ρW μ (cepsMorseMin D θ ρW μ + r ^ 2) z)
    (cepsMorseRoot D θ ρW μ r)) (cepsMorseRoot D θ ρW μ (-r)) ζ

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMorseRoot_norm_le {μ r : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hr : ‖r‖ < dom.rmax) : ‖cepsMorseRoot D θ ρW μ r‖ ≤ dom.c₀ / 4 := by
  have hr' : ‖r‖ < cepsChartRho D θ := by
    have := dom.rmax_r1; have := dom.rmax_pos; linarith
  have hsub := norm_cepsMorseRoot_sub_center_le hW hθ hD (dom.μ_lt_chart hμ) hr'
  have hcenter := dom.norm_center_le hW hθ hD hμ
  have hK := cepsChartK_pos hD
  have hsmall : cepsChartK D * ‖r‖ ≤ dom.c₀ / 8 := by
    nlinarith [dom.rmax_c₀]
  calc
    ‖cepsMorseRoot D θ ρW μ r‖ = ‖cepsMorseCenter D θ ρW μ +
        (cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ)‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ dom.c₀ / 4 := by linarith

include hW hθ hD in
theorem cepsMorseRoot_mem_rootZone {μ r : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hr : ‖r‖ < dom.rmax) : cepsMorseRoot D θ ρW μ r ∈ ball 0 dom.ρA := by
  have hnorm := cepsMorseRoot_norm_le dom hW hθ hD hμ hr
  apply mem_ball_zero_iff.mpr
  have := dom.c₀_le; have := dom.ρA_pos
  linarith

include hW hθ hD in
theorem cepsMorseRoot_differentiableOn_r {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) :
    DifferentiableOn ℂ (cepsMorseRoot D θ ρW μ) (ball 0 dom.rmax) := by
  have hp : DifferentiableOn ℂ (fun r : ℂ => (μ, r)) (ball 0 dom.rmax) :=
    (differentiableOn_const μ).prodMk differentiableOn_id
  refine (differentiableOn_cepsMorseRoot hW hθ hD).comp hp ?_
  intro r hr
  refine ⟨mem_ball_zero_iff.mpr (dom.μ_lt_chart hμ), ?_⟩
  apply mem_ball_zero_iff.mpr
  have := mem_ball_zero_iff.mp hr
  have := dom.rmax_r1; have := dom.rmax_pos; linarith

set_option maxHeartbeats 800000 in
include hW hθ hD in
theorem cepsMorseQ_differentiableOn_joint {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsMorseQ D θ ρW μ x.1 x.2)
      (ball 0 dom.rmax ×ˢ ball 0 dom.ρA) := by
  have hM : AnalyticOnNhd ℂ (stepTransform ρW) (ball 0 (θ / 2)) :=
    (differentiableOn_stepTransform_ball hW hθ hD.le).analyticOnNhd isOpen_ball
  have hM' : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => stepTransform ρW x.2)
      (ball 0 dom.rmax ×ˢ ball 0 dom.ρA) := by
    have hmap : MapsTo (fun x : ℂ × ℂ => x.2)
        (ball 0 dom.rmax ×ˢ ball 0 dom.ρA) (ball 0 (θ / 2)) := by
      intro x hx
      apply mem_ball_zero_iff.mpr
      have := mem_ball_zero_iff.mp hx.2
      have := dom.ρA_R; have := cepsChartRadius_le_r0 (D := D) (θ := θ)
      have := cepsCgfRadius_le (D := D) (θ := θ); linarith
    exact hM.comp analyticOnNhd_snd hmap
  have hq : AnalyticOnNhd ℂ (fun x : ℂ × ℂ =>
      cepsMorseMin D θ ρW μ + x.1 ^ 2) (ball 0 dom.rmax ×ˢ ball 0 dom.ρA) :=
    (analyticOnNhd_const (v := cepsMorseMin D θ ρW μ)).add (analyticOnNhd_fst.pow 2)
  have hE : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => cexp (μ * x.2))
      (ball 0 dom.rmax ×ˢ ball 0 dom.ρA) :=
    ((analyticOnNhd_const (v := μ)).mul analyticOnNhd_snd).cexp
  have hG : AnalyticOnNhd ℂ (fun x : ℂ × ℂ =>
      -cepsD ρW μ (cepsMorseMin D θ ρW μ + x.1 ^ 2) x.2)
      (ball 0 dom.rmax ×ˢ ball 0 dom.ρA) := by
    unfold cepsD
    exact ((analyticOnNhd_const (v := (1 : ℂ))).sub
      ((hq.neg.cexp.mul hE).mul hM')).neg
  have ha := cepsMorseRoot_differentiableOn_r dom hW hθ hD hμ
  have hb : DifferentiableOn ℂ (fun r => cepsMorseRoot D θ ρW μ (-r))
      (ball 0 dom.rmax) := ha.comp differentiableOn_id.neg
    (fun r hr => mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hr))
  exact cepsNormal_differentiableOn_joint_moving_second_dslope
    (G := fun r z => -cepsD ρW μ (cepsMorseMin D θ ρW μ + r ^ 2) z)
    (a := cepsMorseRoot D θ ρW μ) (b := fun r => cepsMorseRoot D θ ρW μ (-r))
    isOpen_ball hG ha hb
    (fun r hr => cepsMorseRoot_mem_rootZone dom hW hθ hD hμ (mem_ball_zero_iff.mp hr))
    (fun r hr => cepsMorseRoot_mem_rootZone dom hW hθ hD hμ
      (by simpa using mem_ball_zero_iff.mp hr))

include hW hθ hD in
theorem cepsMorseQ_neg {μ r ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hr : ‖r‖ < dom.rmax) :
    cepsMorseQ D θ ρW μ (-r) ζ = cepsMorseQ D θ ρW μ r ζ := by
  have hG : DifferentiableOn ℂ
      (fun z => -cepsD ρW μ (cepsMorseMin D θ ρW μ + r ^ 2) z) (ball 0 dom.ρA) := by
    have hM := (differentiableOn_stepTransform_ball hW hθ hD.le).mono
      (ball_subset_ball (show dom.ρA ≤ θ / 2 by
        have := dom.ρA_R; have := cepsChartRadius_le_r0 (D := D) (θ := θ)
        have := cepsCgfRadius_le (D := D) (θ := θ); linarith))
    exact (differentiableOn_const _ |>.sub
      (((differentiableOn_const _).mul (differentiableOn_id.const_mul μ).cexp).mul hM)).neg
  have ha := cepsMorseRoot_mem_rootZone dom hW hθ hD hμ hr
  have hb := cepsMorseRoot_mem_rootZone dom hW hθ hD hμ (r := -r) (by simpa using hr)
  unfold cepsMorseQ
  rw [neg_sq, neg_neg]
  exact cepsNormal_second_dslope_swap
    ((hG _ ha).differentiableAt (isOpen_ball.mem_nhds ha))
    ((hG _ hb).differentiableAt (isOpen_ball.mem_nhds hb)) ζ

end PGM
