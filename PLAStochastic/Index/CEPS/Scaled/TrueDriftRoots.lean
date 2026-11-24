import PLAStochastic.Index.CEPS.Normal.ActualRootContinuity
import PLAStochastic.Index.CEPS.Scaled.TrueFrequencyDisc

/-! # Actual scaled-root continuity in real drift through mergers -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSignedRootPlusMinus_continuousAt_drift {b lam : ℝ} (hb : 0 < b) {z : ℂ}
    (hμ : |b * lam| ≤ dom.μ₀) (hq : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀)
    (hre : 0 ≤ (cepsComplexScaledDiscount lam z b).re) :
    ContinuousAt (fun a : ℝ => cepsScaledSignedRoot D θ ρW a z 1 b) lam ∧
      ContinuousAt (fun a : ℝ => cepsScaledSignedRoot D θ ρW a z (-1) b) lam := by
  obtain ⟨hp, hm⟩ := cepsRootPlusMinus_continuousAt_joint_of_real_drift dom hW hθ hD hμ hq hre
  have hcurve : Continuous (fun a : ℝ => (((b * a : ℝ) : ℂ), cepsComplexScaledDiscount a z b)) := by
    unfold cepsComplexScaledDiscount
    fun_prop
  have hpc : ContinuousAt (fun a : ℝ =>
      cepsRootPlus D θ ρW ((b * a : ℝ) : ℂ) (cepsComplexScaledDiscount a z b) / (b : ℂ)) lam :=
    (hp.comp (x := lam) (f := fun a : ℝ => (((b * a : ℝ) : ℂ), cepsComplexScaledDiscount a z b))
      hcurve.continuousAt).div_const (b : ℂ)
  have hmc : ContinuousAt (fun a : ℝ =>
      cepsRootMinus D θ ρW ((b * a : ℝ) : ℂ) (cepsComplexScaledDiscount a z b) / (b : ℂ)) lam :=
    (hm.comp (x := lam) (f := fun a : ℝ => (((b * a : ℝ) : ℂ), cepsComplexScaledDiscount a z b))
      hcurve.continuousAt).div_const (b : ℂ)
  have hμn : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ
  have hcont : Continuous (fun a : ℝ => ((b * a : ℝ) : ℂ)) := by fun_prop
  have hev := hcont.norm.tendsto lam (isOpen_Iio.mem_nhds (dom.μ_lt_chart hμn))
  have hpeq : (fun a : ℝ => cepsScaledSignedRoot D θ ρW a z 1 b) =ᶠ[𝓝 lam]
      (fun a => cepsRootPlus D θ ρW ((b * a : ℝ) : ℂ) (cepsComplexScaledDiscount a z b) / (b : ℂ)) := by
    filter_upwards [hev] with a ha
    simpa only [cepsScaledDiscount, cepsComplexScaledDiscount, ofReal_mul, ofReal_add, ofReal_one] using
      cepsScaledSignedRoot_plus_actual hW hθ hD hb ha
  have hmeq : (fun a : ℝ => cepsScaledSignedRoot D θ ρW a z (-1) b) =ᶠ[𝓝 lam]
      (fun a => cepsRootMinus D θ ρW ((b * a : ℝ) : ℂ) (cepsComplexScaledDiscount a z b) / (b : ℂ)) := by
    filter_upwards [hev] with a ha
    simpa only [cepsScaledDiscount, cepsComplexScaledDiscount, ofReal_mul, ofReal_add, ofReal_one] using
      cepsScaledSignedRoot_minus_actual hW hθ hD hb ha
  exact ⟨hpc.congr_of_eventuallyEq hpeq, hmc.congr_of_eventuallyEq hmeq⟩

end PGM
