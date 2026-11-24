import PLAStochastic.Index.CEPS.Normal.ActualRootDifferential

/-! # Actual root continuity through the real-drift discount merger

The principal square root is continuous at the whole closed right
half-plane, including zero. Individual roots need no differentiability
at their merger for these continuity statements.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsRootR_continuousAt_joint_of_real_drift {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : 0 ≤ q.re) :
    ContinuousAt (fun x : ℂ × ℂ => cepsRootR D θ ρW x.1 x.2) ((μ : ℂ), q) := by
  have hm : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ
  have hmem : (μ : ℂ) ∈ ball (0 : ℂ) (cepsChartMu D θ) :=
    mem_ball_zero_iff.mpr (dom.μ_lt_chart hm)
  have hc := (((differentiableOn_cepsMorseMin hW hθ hD) _ hmem).differentiableAt
    (isOpen_ball.mem_nhds hmem)).continuousAt
  have hrad : ContinuousAt (fun x : ℂ × ℂ => x.2 - cepsMorseMin D θ ρW x.1) ((μ : ℂ), q) :=
    continuousAt_snd.sub (hc.comp (x := ((μ : ℂ), q))
      (f := fun x : ℂ × ℂ => x.1) continuousAt_fst)
  have hre : 0 ≤ (q - cepsMorseMin D θ ρW μ).re := by
    rw [sub_re]
    linarith [re_cepsMorseMin_nonpos hW hθ hD (dom.μ_lt_chart hm)]
  exact (continuousAt_sqrt (Or.inl hre)).comp
    (f := fun x : ℂ × ℂ => x.2 - cepsMorseMin D θ ρW x.1) hrad

include hW hθ hD in
theorem cepsRootPlusMinus_continuousAt_joint_of_real_drift {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hre : 0 ≤ q.re) :
    ContinuousAt (fun x : ℂ × ℂ => cepsRootPlus D θ ρW x.1 x.2) ((μ : ℂ), q) ∧
      ContinuousAt (fun x : ℂ × ℂ => cepsRootMinus D θ ρW x.1 x.2) ((μ : ℂ), q) := by
  have hm : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ
  have hμb : (μ : ℂ) ∈ ball (0 : ℂ) (cepsChartMu D θ) :=
    mem_ball_zero_iff.mpr (dom.μ_lt_chart hm)
  have hrb : cepsRootR D θ ρW μ q ∈ ball (0 : ℂ) (cepsChartRho D θ) :=
    mem_ball_zero_iff.mpr (dom.norm_cepsRootR_lt hW hθ hD hm hq)
  have hrneg : -cepsRootR D θ ρW μ q ∈ ball (0 : ℂ) (cepsChartRho D θ) := by
    simpa only [mem_ball_zero_iff, norm_neg] using hrb
  have hr := cepsRootR_continuousAt_joint_of_real_drift dom hW hθ hD hμ hre
  have hp := ((differentiableOn_cepsMorseRoot hW hθ hD) ((μ : ℂ), cepsRootR D θ ρW μ q)
    ⟨hμb, hrb⟩).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hμb, hrb⟩)
  have hn := ((differentiableOn_cepsMorseRoot hW hθ hD) ((μ : ℂ), -cepsRootR D θ ρW μ q)
    ⟨hμb, hrneg⟩).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hμb, hrneg⟩)
  exact ⟨hp.continuousAt.comp (x := ((μ : ℂ), q))
      (f := fun x : ℂ × ℂ => (x.1, cepsRootR D θ ρW x.1 x.2))
      (continuousAt_fst.prodMk hr),
    hn.continuousAt.comp (x := ((μ : ℂ), q))
      (f := fun x : ℂ × ℂ => (x.1, -cepsRootR D θ ρW x.1 x.2))
      (continuousAt_fst.prodMk hr.neg)⟩

end PGM
