import PLAStochastic.Index.CEPS.Normal.WeightedSlopeIntegral

/-! # The spatial derivative of a divided difference -/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

theorem cepsNormal_deriv_dslope_eq_integral {g : ℂ → ℂ} {R : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) {b z : ℂ}
    (hb : b ∈ ball 0 R) (hz : z ∈ ball 0 R) :
    deriv (dslope g b) z =
      ∫ s in (0 : ℝ)..1, (s : ℂ) * deriv (deriv g) (b + (s : ℂ) * (z - b)) := by
  let F : ℂ → ℝ → ℂ := fun z s => deriv g (b + (s : ℂ) * (z - b))
  let D : ℂ → ℝ → ℂ := fun z s => (s : ℂ) * deriv (deriv g) (b + (s : ℂ) * (z - b))
  have hpath : MapsTo (fun x : ℂ × ℝ => b + (x.2 : ℂ) * (x.1 - b))
      (ball 0 R ×ˢ Icc (0 : ℝ) 1) (ball 0 R) :=
    fun _ hx => cepsNormal_segment_mem_ball hb hx.1 hx.2
  have hp : ContinuousOn (fun x : ℂ × ℝ => b + (x.2 : ℂ) * (x.1 - b))
      (ball 0 R ×ˢ Icc (0 : ℝ) 1) := by fun_prop
  have hc : ContinuousOn (fun x : ℂ × ℝ => F x.1 x.2)
      (ball 0 R ×ˢ Icc (0 : ℝ) 1) := (hg.deriv isOpen_ball).continuousOn.comp hp hpath
  have hdc : ContinuousOn (fun x : ℂ × ℝ => D x.1 x.2)
      (ball 0 R ×ˢ Icc (0 : ℝ) 1) :=
    (by fun_prop : ContinuousOn (fun x : ℂ × ℝ => (x.2 : ℂ)) _).mul
      (((hg.deriv isOpen_ball).deriv isOpen_ball).continuousOn.comp hp hpath)
  have hd : ∀ z ∈ ball (0 : ℂ) R, ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun z => F z s) (D z s) z := by
    intro z hz s hs
    have hmem := cepsNormal_segment_mem_ball hb hz hs
    have hlin := ((hasDerivAt_id z).sub_const b).const_mul (s : ℂ) |>.const_add b
    have h := (((hg.deriv isOpen_ball) _ hmem).differentiableAt
      (isOpen_ball.mem_nhds hmem)).hasDerivAt.comp z hlin
    simpa [F, D, Function.comp_def, mul_comm] using h
  have hmain := cepsNormal_hasDerivAt_parameterIntegral (F := F) (D := D)
    isOpen_ball hc hdc hd hz
  have heq : (fun z => ∫ s in (0 : ℝ)..1, F z s) =ᶠ[𝓝 z] dslope g b := by
    filter_upwards [isOpen_ball.mem_nhds hz] with z hz
    exact (cepsNormal_dslope_eq_integral hg hb hz).symm
  exact (hmain.congr_of_eventuallyEq heq.symm).deriv

end PGM
