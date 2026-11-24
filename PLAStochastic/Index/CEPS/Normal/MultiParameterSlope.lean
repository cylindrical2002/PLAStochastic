import PLAStochastic.Index.CEPS.Normal.ParameterFDeriv
import PLAStochastic.ForMathlib.Analysis.Complex.ContinuousFDerivTwo

/-! # Moving divided differences with several complex parameters

Actual joint Frechet derivatives provide the continuous compact-integral
majorants. This includes all endpoint diagonals and arbitrary finite
products of complex parameter spaces.
-/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cepsNormal_analyticOnNhd_spatial_deriv_general {U : Set E} {R : ℝ}
    (hU : IsOpen U) {G : E → ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ (fun x : E × ℂ => G x.1 x.2) (U ×ˢ ball 0 R)) :
    AnalyticOnNhd ℂ (fun x : E × ℂ => deriv (G x.1) x.2) (U ×ˢ ball 0 R) := by
  have hF := (ContinuousLinearMap.apply ℂ ℂ ((0, 1) : E × ℂ)).comp_analyticOnNhd hG.fderiv
  apply hF.congr (hU.prod isOpen_ball)
  intro x hx
  have hp := (hasFDerivAt_const (𝕜 := ℂ) x.1 x.2).prodMk
    (hasFDerivAt_id (𝕜 := ℂ) x.2)
  have hd := ((hG x hx).differentiableAt.hasFDerivAt.comp x.2 hp).hasDerivAt
  change (fderiv ℂ (fun x : E × ℂ => G x.1 x.2) x) (0, 1) = deriv (G x.1) x.2
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply, id_eq,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul] using hd.deriv.symm

variable [ProperSpace E]

set_option maxHeartbeats 800000 in
theorem cepsNormal_multi_moving_dslope_of_continuous_fderiv
    {U : Set E} (hU : IsOpen U) {R : ℝ} {G : E → ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ (fun x : E × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    {a b : E → ℂ} (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b U)
    (hda : ContinuousOn (fderiv ℂ a) U) (hdb : ContinuousOn (fderiv ℂ b) U)
    (hamap : MapsTo a U (ball 0 R)) (hbmap : MapsTo b U (ball 0 R)) :
    DifferentiableOn ℂ (fun x => dslope (G x) (a x) (b x)) U := by
  let D : E × ℂ → ℂ := fun x => deriv (G x.1) x.2
  let P : E → ℝ → E × ℂ := fun x s => (x, a x + (s : ℂ) * (b x - a x))
  let T : E → ℝ → E →L[ℂ] E × ℂ := fun x s =>
    (ContinuousLinearMap.id ℂ E).prod
      ((1 - (s : ℂ)) • fderiv ℂ a x + (s : ℂ) • fderiv ℂ b x)
  have hD := cepsNormal_analyticOnNhd_spatial_deriv_general hU hG
  have hmap : ∀ y : E × ℝ, y ∈ U ×ˢ Icc (0 : ℝ) 1 → P y.1 y.2 ∈ U ×ˢ ball 0 R :=
    fun y hy => ⟨hy.1, cepsNormal_segment_mem_ball (hamap hy.1) (hbmap hy.1) hy.2⟩
  have hca : ContinuousOn (fun y : E × ℝ => a y.1) (U ×ˢ Icc (0 : ℝ) 1) :=
    ha.continuousOn.comp continuousOn_fst (fun _ hy => hy.1)
  have hcb : ContinuousOn (fun y : E × ℝ => b y.1) (U ×ˢ Icc (0 : ℝ) 1) :=
    hb.continuousOn.comp continuousOn_fst (fun _ hy => hy.1)
  have hcS : ContinuousOn (fun y : E × ℝ => (y.2 : ℂ)) (U ×ˢ Icc (0 : ℝ) 1) := by fun_prop
  have hcP : ContinuousOn (fun y : E × ℝ => P y.1 y.2) (U ×ˢ Icc (0 : ℝ) 1) :=
    continuousOn_fst.prodMk (hca.add (hcS.mul (hcb.sub hca)))
  have hdca : ContinuousOn (fun y : E × ℝ => fderiv ℂ a y.1) (U ×ˢ Icc (0 : ℝ) 1) :=
    hda.comp continuousOn_fst (fun _ hy => hy.1)
  have hdcb : ContinuousOn (fun y : E × ℝ => fderiv ℂ b y.1) (U ×ˢ Icc (0 : ℝ) 1) :=
    hdb.comp continuousOn_fst (fun _ hy => hy.1)
  have hcT : ContinuousOn (fun y : E × ℝ => T y.1 y.2) (U ×ˢ Icc (0 : ℝ) 1) :=
    (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp_continuousOn
      (continuousOn_const.prodMk (((continuousOn_const.sub hcS).smul hdca).add (hcS.smul hdcb)))
  have hcF : ContinuousOn (fun y : E × ℝ => D (P y.1 y.2)) (U ×ˢ Icc (0 : ℝ) 1) :=
    hD.continuousOn.comp hcP hmap
  have hcF' : ContinuousOn (fun y : E × ℝ => (fderiv ℂ D (P y.1 y.2)).comp (T y.1 y.2))
      (U ×ˢ Icc (0 : ℝ) 1) := (hD.fderiv.continuousOn.comp hcP hmap).clm_comp hcT
  have hdP : ∀ x ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, HasFDerivAt (fun x => P x s) (T x s) x := by
    intro x hx s _
    have had := ((ha x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
    have hbd := ((hb x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
    have hp := (hasFDerivAt_id (𝕜 := ℂ) x).prodMk (had.add ((hbd.sub had).const_mul (s : ℂ)))
    apply hp.congr_fderiv
    apply ContinuousLinearMap.ext
    intro y
    change (y, (fderiv ℂ a x) y + (s : ℂ) * ((fderiv ℂ b x) y - (fderiv ℂ a x) y)) =
      (y, (1 - (s : ℂ)) * ((fderiv ℂ a x) y) + (s : ℂ) * ((fderiv ℂ b x) y))
    congr 1
    ring
  have hI : DifferentiableOn ℂ (fun x => ∫ s in (0 : ℝ)..1, D (P x s)) U := by
    intro x hx
    exact (cepsNormal_hasFDerivAt_parameterIntegral hU hcF hcF'
      (fun x hx s hs => ((hD _ (hmap (x, s) ⟨hx, hs⟩)).differentiableAt.hasFDerivAt.comp x
        (hdP x hx s hs))) hx).differentiableAt.differentiableWithinAt
  apply hI.congr
  intro x hx
  exact cepsNormal_dslope_eq_integral
    (fun ξ hξ => (hG (x, ξ) ⟨hx, hξ⟩).curry_right.differentiableAt.differentiableWithinAt)
    (hamap hx) (hbmap hx)

theorem cepsNormal_differentiableOn_multi_moving_dslope
    {U : Set E} (hU : IsOpen U) {R : ℝ} {G : E → ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ (fun x : E × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    {a b : E → ℂ} (ha : AnalyticOnNhd ℂ a U) (hb : AnalyticOnNhd ℂ b U)
    (hamap : MapsTo a U (ball 0 R)) (hbmap : MapsTo b U (ball 0 R)) :
    DifferentiableOn ℂ (fun x => dslope (G x) (a x) (b x)) U :=
  cepsNormal_multi_moving_dslope_of_continuous_fderiv hU hG ha.differentiableOn hb.differentiableOn
    ha.fderiv.continuousOn hb.fderiv.continuousOn hamap hbmap

theorem cepsNormal_differentiableOn_pair_moving_dslope
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) {R : ℝ} {G : (ℂ × ℂ) → ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × ℂ => G x.1 x.2) (U ×ˢ ball 0 R))
    {a b : (ℂ × ℂ) → ℂ} (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b U)
    (hamap : MapsTo a U (ball 0 R)) (hbmap : MapsTo b U (ball 0 R)) :
    DifferentiableOn ℂ (fun x => dslope (G x) (a x) (b x)) U :=
  cepsNormal_multi_moving_dslope_of_continuous_fderiv hU hG ha hb
    (continuousOn_fderiv_of_complex_differentiableOn hU ha)
    (continuousOn_fderiv_of_complex_differentiableOn hU hb) hamap hbmap

end PGM
