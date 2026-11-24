import PLAStochastic.Index.CEPS.Normal.ParameterFDeriv

/-! # Moving line-segment integrals of jointly analytic families -/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

set_option maxHeartbeats 800000 in
theorem cepsNormal_hasFDerivAt_weighted_segmentIntegral
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} {D : ℂ × ℂ → ℂ}
    (hD : AnalyticOnNhd ℂ D (U ×ˢ ball 0 R))
    {a : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a U) (hamap : MapsTo a U (ball 0 R))
    {w : ℝ → ℂ} (hw : ContinuousOn w (Icc (0 : ℝ) 1))
    {x : ℂ × ℂ} (hx : x ∈ U ×ˢ ball 0 R) :
    HasFDerivAt
      (fun x : ℂ × ℂ => ∫ s in (0 : ℝ)..1, w s * D (x.1, a x.1 + (s : ℂ) * (x.2 - a x.1)))
      (∫ s in (0 : ℝ)..1,
        w s • ((fderiv ℂ D (x.1, a x.1 + (s : ℂ) * (x.2 - a x.1))).comp
          ((ContinuousLinearMap.fst ℂ ℂ ℂ).prod
            (((1 - (s : ℂ)) * deriv a x.1) • ContinuousLinearMap.fst ℂ ℂ ℂ +
              (s : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ)))) x := by
  let P : (ℂ × ℂ) → ℝ → ℂ × ℂ := fun x s => (x.1, a x.1 + (s : ℂ) * (x.2 - a x.1))
  let T : (ℂ × ℂ) → ℝ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := fun x s =>
    (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
      (((1 - (s : ℂ)) * deriv a x.1) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (s : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ)
  have hmap : ∀ y : (ℂ × ℂ) × ℝ, y ∈ (U ×ˢ ball 0 R) ×ˢ Icc (0 : ℝ) 1 →
      P y.1 y.2 ∈ U ×ˢ ball 0 R := fun y hy =>
    ⟨hy.1.1, cepsNormal_segment_mem_ball (hamap hy.1.1) hy.1.2 hy.2⟩
  have hca : ContinuousOn (fun y : (ℂ × ℂ) × ℝ => a y.1.1)
      ((U ×ˢ ball 0 R) ×ˢ Icc (0 : ℝ) 1) :=
    ha.continuousOn.comp (continuous_fst.fst.continuousOn) (fun _ hy => hy.1.1)
  have hda : ContinuousOn (fun y : (ℂ × ℂ) × ℝ => deriv a y.1.1)
      ((U ×ˢ ball 0 R) ×ˢ Icc (0 : ℝ) 1) :=
    ha.deriv.continuousOn.comp (continuous_fst.fst.continuousOn) (fun _ hy => hy.1.1)
  have hcS : ContinuousOn (fun y : (ℂ × ℂ) × ℝ => (y.2 : ℂ))
      ((U ×ˢ ball 0 R) ×ˢ Icc (0 : ℝ) 1) := by fun_prop
  have hcP : ContinuousOn (fun y : (ℂ × ℂ) × ℝ => P y.1 y.2)
      ((U ×ˢ ball 0 R) ×ˢ Icc (0 : ℝ) 1) :=
    continuous_fst.fst.continuousOn.prodMk
      (hca.add (hcS.mul (continuous_fst.snd.continuousOn.sub hca)))
  have hcw : ContinuousOn (fun y : (ℂ × ℂ) × ℝ => w y.2)
      ((U ×ˢ ball 0 R) ×ˢ Icc (0 : ℝ) 1) :=
    hw.comp continuousOn_snd (fun _ hy => hy.2)
  have hcF : ContinuousOn (fun y : (ℂ × ℂ) × ℝ => w y.2 * D (P y.1 y.2))
      ((U ×ˢ ball 0 R) ×ˢ Icc (0 : ℝ) 1) :=
    hcw.mul (hD.continuousOn.comp hcP hmap)
  have hcT : ContinuousOn (fun y : (ℂ × ℂ) × ℝ => T y.1 y.2)
      ((U ×ˢ ball 0 R) ×ˢ Icc (0 : ℝ) 1) := by
    exact (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp_continuousOn
      (continuousOn_const.prodMk
        ((((continuousOn_const.sub hcS).mul hda).smul continuousOn_const).add
          (hcS.smul continuousOn_const)))
  have hcF' : ContinuousOn (fun y : (ℂ × ℂ) × ℝ =>
      w y.2 • ((fderiv ℂ D (P y.1 y.2)).comp (T y.1 y.2)))
      ((U ×ˢ ball 0 R) ×ˢ Icc (0 : ℝ) 1) :=
    hcw.smul ((hD.fderiv.continuousOn.comp hcP hmap).clm_comp hcT)
  have hdP : ∀ y ∈ U ×ˢ ball (0 : ℂ) R, ∀ s ∈ Icc (0 : ℝ) 1,
      HasFDerivAt (fun y => P y s) (T y s) y := by
    intro y hy s _
    have hf := hasFDerivAt_fst (𝕜 := ℂ) (p := y)
    have hs := hasFDerivAt_snd (𝕜 := ℂ) (p := y)
    have had := (ha y.1 hy.1).differentiableAt.hasDerivAt.comp_hasFDerivAt y hf
    have hp := hf.prodMk (had.add ((hs.sub had).const_mul (s : ℂ)))
    apply hp.congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    change (v.1, deriv a y.1 * v.1 + (s : ℂ) * (v.2 - deriv a y.1 * v.1)) =
      (v.1, ((1 - (s : ℂ)) * deriv a y.1) * v.1 + (s : ℂ) * v.2)
    congr 1
    ring
  exact cepsNormal_hasFDerivAt_parameterIntegral (E := ℂ × ℂ)
    (F := fun y s => w s * D (P y s))
    (F' := fun y s => w s • ((fderiv ℂ D (P y s)).comp (T y s)))
    (hU.prod isOpen_ball) hcF hcF'
    (fun y hy s hs => ((hD _ (hmap (y, s) ⟨hy, hs⟩)).differentiableAt.hasFDerivAt.comp y
      (hdP y hy s hs)).const_mul (w s)) hx

end PGM
