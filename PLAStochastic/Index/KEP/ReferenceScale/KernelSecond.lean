import PLAStochastic.Index.KEP.ReferenceScale.RealDecomposition

/-!
# Combining the regular and small parts in the second actual kernel step

The existing long-row decomposition supplies `B` and `R`. The estimate pays
the input first derivative on the regular part and the second derivative only
on the exponentially small remainder. The two endpoint values of `p'` remain
explicit for the subsequent slope integral.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

theorem truncatedConvolution_second_of_decomposition
    (p : HellingerDensity (volume : Measure ℝ)) {p' p'' g r : ℝ → ℝ} {a b D B R : ℝ}
    (hab : a ≤ b) (hp : Continuous p.density) (hp' : Continuous p') (hp'' : Continuous p'')
    (hpi' : Integrable p' volume) (hpi'' : Integrable p'' volume)
    (hd : ∀ t, HasDerivAt p.density (p' t) t) (hdd : ∀ t, HasDerivAt p' (p'' t) t)
    (hpD : ∀ t, p.density t ≤ D) (hB : 0 ≤ B)
    (hg : Integrable g volume) (hr : Integrable r volume) (hr2 : MemLp r 2 volume)
    (hs : ∀ z, z ∉ Icc a b → g z = 0 ∧ r z = 0)
    (hvar : eVariationOn (fun z => (g z : ℂ)) univ ≤ ENNReal.ofReal B)
    (hR : Real.sqrt (∫ z, r z ^ 2) ≤ R) (y : ℝ) :
    |truncatedConvolution a b p'' (truncatedConvolution a b p.density (g + r)) y| ≤
      D * B * ((∫ t, |p' t|) + (b - a) * (|p' (y - a)| + |p' (y - b)|)) +
        (∫ t, |p'' t|) * Real.sqrt D * R := by
  have hD : 0 ≤ D := (p.nonneg 0).trans (hpD 0)
  have hbv : BoundedVariationOn (fun z => (g z : ℂ)) univ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  have hV : (eVariationOn (fun z => (g z : ℂ)) univ).toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hvar
  have hmass := integral_abs_bv_support_le hab hB hg (fun z hz => (hs z hz).1) hvar
  have hG := truncatedConvolution_second_bv_bound hab hp hp' hp'' hpi' hd hdd
    p.nonneg hpD hg (fun z hz => (hs z hz).1) hbv y
  have hR' := truncatedConvolution_second_remainder_bound p hp hp' hd hpi'' hpD
    hr hr2 (fun z hz => (hs z hz).2) y
  have hGb : |truncatedConvolution a b p'' (truncatedConvolution a b p.density g) y| ≤
      D * B * ((∫ t, |p' t|) + (b - a) * (|p' (y - a)| + |p' (y - b)|)) := by
    refine hG.trans ?_
    calc
      D * (eVariationOn (fun z => (g z : ℂ)) univ).toReal * (∫ t, |p' t|) +
          D * (∫ z, |g z|) * (|p' (y - a)| + |p' (y - b)|) ≤
          D * B * (∫ t, |p' t|) +
            D * ((b - a) * B) * (|p' (y - a)| + |p' (y - b)|) := by
        gcongr
      _ = _ := by ring
  have hRb : |truncatedConvolution a b p'' (truncatedConvolution a b p.density r) y| ≤
      (∫ t, |p'' t|) * Real.sqrt D * R :=
    hR'.trans (mul_le_mul_of_nonneg_left hR (by positivity))
  have hcg : Continuous (truncatedConvolution a b p.density g) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_truncatedConvolution hp hp' hd hg.integrableOn t).continuousAt
  have hcr : Continuous (truncatedConvolution a b p.density r) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_truncatedConvolution hp hp' hd hr.integrableOn t).continuousAt
  have he : truncatedConvolution a b p.density (g + r) =
      truncatedConvolution a b p.density g + truncatedConvolution a b p.density r := by
    funext t
    exact truncatedConvolution_add hp hg.integrableOn hr.integrableOn t
  rw [he, truncatedConvolution_add hp''
    (hcg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hcr.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  exact (abs_add_le _ _).trans (add_le_add hGb hRb)

/-- The combined estimate on the existing actual row after both final steps.
The decomposition is supplied, without new hypotheses, by
`krDens_long_real_decomposition` when its regular class applies. -/
theorem krDens_second_of_decomposition
    (p : HellingerDensity (volume : Measure ℝ)) (ν : ProbabilityMeasure ℝ)
    {f' f'' g r : ℝ → ℝ} {w β a D B R : ℝ}
    (hw : 0 ≤ w) (hp : Continuous p.density) (hp' : Continuous f') (hp'' : Continuous f'')
    (hpi' : Integrable f' volume) (hpi'' : Integrable f'' volume)
    (hd : ∀ t, HasDerivAt p.density (f' t) t) (hdd : ∀ t, HasDerivAt f' (f'' t) t)
    (hpD : ∀ t, p.density t ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (p.density x)))
    (ha : a ≠ 0) (n : ℕ) (x : ℝ) (hB : 0 ≤ B)
    (hg : Integrable g volume) (hr : Integrable r volume) (hr2 : MemLp r 2 volume)
    (hs : ∀ z, z ∉ Icc 0 w → g z = 0 ∧ r z = 0)
    (hdecomp : ∀ z, krDens (Icc 0 w) ν p.density β a (n + 1) x z = g z + r z)
    (hvar : eVariationOn (fun z => (g z : ℂ)) univ ≤ ENNReal.ofReal B)
    (hR : Real.sqrt (∫ z, r z ^ 2) ≤ R) (y : ℝ) :
    |truncatedConvolution 0 w (kepStepSpatialSecond f'' β a)
        (fun z => krDens (Icc 0 w) ν p.density β a (n + 2) x z) y| ≤
      (D / |a|) * B * (((∫ t, |f' t|) / |a|) +
        w * (|kepStepSpatialFirst f' β a y| + |kepStepSpatialFirst f' β a (y - w)|)) +
        ((∫ t, |f'' t|) / |a| ^ 2) * Real.sqrt (D / |a|) * R := by
  have hi'' : Integrable (kepStepSpatialSecond f'' β a) volume := by
    have h : Integrable (fun z => f'' (z / a)) volume := by
      convert hpi''.comp_mul_left' (inv_ne_zero ha) using 1
      funext z
      rw [div_eq_mul_inv, mul_comm]
    exact (h.comp_sub_left β).div_const (a ^ 2 * |a|)
  have hpD' : ∀ t, (kepStepDensity p β a ha).density t ≤ D / |a| := fun t =>
    div_le_div_of_nonneg_right (hpD _) (abs_nonneg a)
  have hh := truncatedConvolution_second_of_decomposition (kepStepDensity p β a ha)
    (a := 0) (b := w) hw (continuous_kepStepSpatial hp β a)
    (continuous_kepStepSpatialFirst hp' β a) (continuous_kepStepSpatialSecond hp'' β a)
    (integrable_kepStepSpatialFirst hpi' ha β) hi''
    (hasDerivAt_kepStepSpatial hd β a) (hasDerivAt_kepStepSpatialFirst hdd β a)
    hpD' hB hg hr hr2 hs hvar hR y
  change |truncatedConvolution 0 w (kepStepSpatialSecond f'' β a)
    (truncatedConvolution 0 w (kepStepSpatial p.density β a) (g + r)) y| ≤ _ at hh
  simp only [sub_zero, integral_abs_kepStepSpatialFirst f' β ha,
    integral_abs_kepStepSpatialSecond f'' β ha] at hh
  have he : truncatedConvolution 0 w (kepStepSpatialSecond f'' β a)
        (fun z => krDens (Icc 0 w) ν p.density β a (n + 2) x z) y =
      truncatedConvolution 0 w (kepStepSpatialSecond f'' β a)
        (truncatedConvolution 0 w (kepStepSpatial p.density β a) (g + r)) y := by
    unfold truncatedConvolution
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    dsimp only
    rw [krDens_eq_kepFinalConvolution ν (β := β) p.measurable p.nonneg hpD hν ha n x
      ⟨hz.1.le, hz.2⟩]
    unfold kepFinalConvolution truncatedConvolution
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp only
    rw [hdecomp]
    rfl
  rw [he]
  exact hh

end

end PGM
