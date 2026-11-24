import PLAStochastic.Index.CEPS.Scaled.MorseChartJoint
import PLAStochastic.Index.CEPS.Scaled.ActualScaleChart

/-! # Fixed signed-coordinate chart identification through zero scale -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include dom hW hθ hD in
theorem cepsScaledSignedRoot_eq_fixed_chart (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) (b : ℂ) :
    cepsScaledSignedRoot D θ ρW lam z sign b =
      cepsScaledMorseChart D θ ρW lam (sign * cepsScaledRootCoordinate D θ ρW lam z b) b := by
  by_cases hb : b ≠ 0
  · rw [cepsScaledSignedRoot_eq_div hW hθ hD lam z sign hb,
      cepsScaledMorseChart_eq_div hW hθ hD _ _ hb, mul_assoc]
  · have hb0 : b = 0 := not_ne_iff.mp hb
    subst b
    let r : ℂ → ℂ := fun b => sign * cepsScaledRootCoordinate D θ ρW lam z b
    let R : ℝ := ‖r 0‖ + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have hr : r 0 ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; dsimp [R]; linarith
    have hcoord : ContinuousAt r 0 := by
      have hd := (cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).1
      exact (hd 0 (mem_ball_self (radicandScaleRadius_budget dom hW hθ hD lam).1)).differentiableAt
        (ball_mem_nhds _ (radicandScaleRadius_budget dom hW hθ hD lam).1) |>.continuousAt.const_mul sign
    have hchart : ContinuousAt (fun x : ℂ × ℂ => cepsScaledMorseChart D θ ρW lam x.2 x.1) (0, r 0) :=
      (cepsScaledMorseChart_differentiableOn_joint dom hW hθ hD (lam : ℂ) hR).continuousOn.continuousAt
        ((isOpen_ball.prod isOpen_ball).mem_nhds
          ⟨mem_ball_self (scaledMorseJointRadius_pos dom (lam : ℂ) hR), hr⟩)
    have ht : ContinuousAt (fun b : ℂ => cepsScaledMorseChart D θ ρW lam (r b) b) 0 :=
      hchart.comp (f := fun b : ℂ => (b, r b)) (continuousAt_id.prodMk hcoord)
    have hs : ContinuousAt (cepsScaledSignedRoot D θ ρW lam z sign) 0 :=
      (cepsScaledSignedRoot_budget dom hW hθ hD lam hz hsign).1.continuousOn.continuousAt
        (ball_mem_nhds _ (actualRootScaleRadius_pos dom hW hθ hD lam z))
    have he : (fun b : ℂ => cepsScaledSignedRoot D θ ρW lam z sign b) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun b => cepsScaledMorseChart D θ ρW lam (r b) b) := by
      filter_upwards [self_mem_nhdsWithin] with b hb
      have hb' : b ≠ 0 := hb
      rw [cepsScaledSignedRoot_eq_div hW hθ hD lam z sign hb',
        cepsScaledMorseChart_eq_div hW hθ hD _ _ hb']
      dsimp [r]
      rw [mul_assoc]
    exact tendsto_nhds_unique (hs.tendsto.mono_left nhdsWithin_le_nhds)
      ((ht.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)

include hW hθ hD in
theorem cepsScaledSignedRoot_eq_fixed_chart_of_differentiable (lam : ℝ) (z sign : ℂ)
    (hcoord : DifferentiableAt ℂ (cepsScaledRootCoordinate D θ ρW lam z) 0) (b : ℂ) :
    cepsScaledSignedRoot D θ ρW lam z sign b =
      cepsScaledMorseChart D θ ρW lam (sign * cepsScaledRootCoordinate D θ ρW lam z b) b := by
  by_cases hb : b ≠ 0
  · rw [cepsScaledSignedRoot_eq_div hW hθ hD lam z sign hb,
      cepsScaledMorseChart_eq_div hW hθ hD _ _ hb, mul_assoc]
  · have hb0 : b = 0 := not_ne_iff.mp hb
    subst b
    let F : ℂ × ℂ → ℂ := fun x => cepsMorseRoot D θ ρW x.1 x.2
    let r := cepsScaledRootCoordinate D θ ρW lam z 0
    have hp : (0 : ℂ × ℂ) ∈ ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ) :=
      ⟨mem_ball_self (cepsChartMu_pos hD hθ), mem_ball_self (cepsChartRho_pos hD hθ)⟩
    have hF := ((differentiableOn_cepsMorseRoot hW hθ hD) (0, 0) hp).differentiableAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hp) |>.hasFDerivAt
    have hcurve : HasDerivAt (fun a : ℂ => (a * lam,
        a * sign * cepsScaledRootCoordinate D θ ρW lam z a)) ((lam : ℂ), sign * r) 0 := by
      simpa only [r, Pi.mul_apply, zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one] using!
        (((hasDerivAt_id' (0 : ℂ)).mul_const (lam : ℂ)).prodMk
          (((hasDerivAt_id' (0 : ℂ)).mul_const sign).mul hcoord.hasDerivAt))
    have hfixed : HasDerivAt (fun a : ℂ => (a * lam, a * (sign * r))) ((lam : ℂ), sign * r) 0 := by
      simpa only [mul_one, one_mul] using!
        (((hasDerivAt_id' (0 : ℂ)).mul_const (lam : ℂ)).prodMk
          ((hasDerivAt_id' (0 : ℂ)).mul_const (sign * r)))
    have hd := hF.comp_hasDerivAt_of_eq (0 : ℂ) hcurve (by simp)
    have hf := hF.comp_hasDerivAt_of_eq (0 : ℂ) hfixed (by simp)
    unfold cepsScaledSignedRoot cepsScaledMorseChart
    rw [dslope_same, dslope_same]
    exact hd.deriv.trans hf.deriv.symm

theorem cepsScaledSignedRoot_zeroDrift_eq_chart (z sign b : ℂ) :
    cepsScaledSignedRoot D θ ρW 0 z sign b = cepsScaledMorseChart D θ ρW 0 (sign * sqrt z) b := by
  unfold cepsScaledSignedRoot cepsScaledMorseChart
  congr 1
  funext a
  simp only [ofReal_zero, mul_zero, cepsScaledRootCoordinate, cepsScaledMorseRadicand,
    zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero, mul_one, sub_zero, mul_assoc]

end PGM
