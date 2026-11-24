import PLAStochastic.Index.CEPS.Normal.ActualRootContinuity
import PLAStochastic.Index.CEPS.Normal.MovingSlopeContinuity

/-! # Actual quadratic quotient continuity along real-drift parameter curves

This retains root collisions. Spatial divided differences are continuous
even when the individual roots are only continuous in the real parameter.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsQ_continuousOn_joint_real_curve {U : Set ℝ} (hU : IsOpen U)
    {μ : ℝ → ℝ} {q : ℝ → ℂ} (hcμ : ContinuousOn μ U) (hcq : ContinuousOn q U)
    (hμ : ∀ t ∈ U, |μ t| ≤ dom.μ₀) (hq : ∀ t ∈ U, ‖q t‖ ≤ dom.q₀)
    (hre : ∀ t ∈ U, 0 ≤ (q t).re) :
    ContinuousOn (fun x : ℝ × ℂ => cepsQ D θ ρW (μ x.1) (q x.1) x.2)
      (U ×ˢ ball 0 dom.ρA) := by
  have hM := (differentiableOn_stepTransform_ball hW hθ hD.le).mono
    (ball_subset_ball (show dom.ρA ≤ θ / 2 by
      have := CepsC6.ρA_lt_cgfRadius dom hθ hD
      have := cepsCgfRadius_le (D := D) (θ := θ)
      linarith))
  have hcM : ContinuousOn (fun x : ℝ × ℂ => stepTransform ρW x.2) (U ×ˢ ball 0 dom.ρA) :=
    hM.continuousOn.comp continuousOn_snd (fun x hx => hx.2)
  have hμc : ContinuousOn (fun x : ℝ × ℂ => (μ x.1 : ℂ)) (U ×ˢ ball 0 dom.ρA) :=
    continuous_ofReal.comp_continuousOn (hcμ.comp continuousOn_fst (fun x hx => hx.1))
  have hqc : ContinuousOn (fun x : ℝ × ℂ => q x.1) (U ×ˢ ball 0 dom.ρA) :=
    hcq.comp continuousOn_fst (fun x hx => hx.1)
  have hG : ContinuousOn (fun x : ℝ × ℂ => -cepsD ρW (μ x.1) (q x.1) x.2)
      (U ×ˢ ball 0 dom.ρA) := by
    unfold cepsD
    exact (continuousOn_const.sub ((hqc.neg.cexp.mul (hμc.mul continuousOn_snd).cexp).mul hcM)).neg
  have hd : ∀ t ∈ U, DifferentiableOn ℂ (fun z => -cepsD ρW (μ t) (q t) z)
      (ball 0 dom.ρA) := by
    intro t ht
    unfold cepsD
    fun_prop
  have hpc : ContinuousOn (fun t => cepsRootPlus D θ ρW (μ t) (q t)) U := by
    intro t ht
    have hc := (cepsRootPlusMinus_continuousAt_joint_of_real_drift dom hW hθ hD
      (hμ t ht) (hq t ht) (hre t ht)).1
    exact (hc.comp (x := t) (f := fun t : ℝ => ((μ t : ℂ), q t))
      ((continuous_ofReal.continuousAt.comp (x := t) (f := μ) (hcμ.continuousAt (hU.mem_nhds ht))).prodMk
        (hcq.continuousAt (hU.mem_nhds ht)))).continuousWithinAt
  have hmc : ContinuousOn (fun t => cepsRootMinus D θ ρW (μ t) (q t)) U := by
    intro t ht
    have hc := (cepsRootPlusMinus_continuousAt_joint_of_real_drift dom hW hθ hD
      (hμ t ht) (hq t ht) (hre t ht)).2
    exact (hc.comp (x := t) (f := fun t : ℝ => ((μ t : ℂ), q t))
      ((continuous_ofReal.continuousAt.comp (x := t) (f := μ) (hcμ.continuousAt (hU.mem_nhds ht))).prodMk
        (hcq.continuousAt (hU.mem_nhds ht)))).continuousWithinAt
  have hpmap : MapsTo (fun t => cepsRootPlus D θ ρW (μ t) (q t)) U (ball 0 dom.ρA) := by
    intro t ht
    apply mem_ball_zero_iff.mpr
    have hμn : ‖(μ t : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ t ht
    have hn := dom.norm_rootPlus_le hW hθ hD hμn (hq t ht)
    have := dom.c₀_le
    have := dom.ρA_pos
    linarith
  have hmmap : MapsTo (fun t => cepsRootMinus D θ ρW (μ t) (q t)) U (ball 0 dom.ρA) := by
    intro t ht
    apply mem_ball_zero_iff.mpr
    have hμn : ‖(μ t : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ t ht
    have hn := dom.norm_rootMinus_le hW hθ hD hμn (hq t ht)
    have := dom.c₀_le
    have := dom.ρA_pos
    linarith
  exact cepsNormal_continuousOn_joint_moving_second_dslope_general
    (G := fun t z => -cepsD ρW (μ t) (q t) z)
    (a := fun t => cepsRootPlus D θ ρW (μ t) (q t))
    (b := fun t => cepsRootMinus D θ ρW (μ t) (q t)) hU hG hd hpc hmc hpmap hmmap

end PGM
