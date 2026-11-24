import PLAStochastic.Index.CEPS.Normal.MovingSlope
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Spatial derivatives of a jointly analytic family -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNormal_fderiv_spatial_apply {D : ℂ × ℂ → ℂ} {x : ℂ × ℂ}
    (hD : DifferentiableAt ℂ D x) (c : ℂ) :
    fderiv ℂ D x (0, c) = c * deriv (fun ζ => D (x.1, ζ)) x.2 := by
  have hp := (hasFDerivAt_const (𝕜 := ℂ) x.1 x.2).prodMk
    (hasFDerivAt_id (𝕜 := ℂ) x.2)
  have hd := (hD.hasFDerivAt.comp x.2 hp).hasDerivAt
  have h1 : fderiv ℂ D x (0, 1) = deriv (fun ζ => D (x.1, ζ)) x.2 := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, zero_apply, id_eq,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      one_smul] using hd.deriv.symm
  rw [show (0, c) = c • ((0, 1) : ℂ × ℂ) by simp, map_smul, smul_eq_mul, h1]

/-- Joint analyticity of a spatial derivative follows from the actual joint
Fréchet derivative; it is not a separate factor assumption.
-/
theorem cepsNormal_analyticOnNhd_spatial_deriv {U : Set ℂ} {R : ℝ}
    (hU : IsOpen U)
    {G : ℂ → ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => G x.1 x.2) (U ×ˢ ball 0 R)) :
    AnalyticOnNhd ℂ (fun x : ℂ × ℂ => deriv (G x.1) x.2) (U ×ˢ ball 0 R) := by
  have hF := (ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)).comp_analyticOnNhd hG.fderiv
  apply hF.congr (hU.prod isOpen_ball)
  intro x hx
  have hp := (hasFDerivAt_const (𝕜 := ℂ) x.1 x.2).prodMk
    (hasFDerivAt_id (𝕜 := ℂ) x.2)
  have hc := (hG x hx).differentiableAt.hasFDerivAt.comp x.2 hp
  have hd := hc.hasDerivAt
  change (fderiv ℂ (fun x : ℂ × ℂ => G x.1 x.2) x) (0, 1) = deriv (G x.1) x.2
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply, id_eq,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    one_smul] using hd.deriv.symm

end PGM
