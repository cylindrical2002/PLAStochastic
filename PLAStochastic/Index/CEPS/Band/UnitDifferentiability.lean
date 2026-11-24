import PLAStochastic.Index.CEPS.Band.UnitWidth
import PLAStochastic.Index.CEPS.Actual.Defs

/-! # Classical finite bridge width derivatives with bounded density derivative -/

set_option backward.isDefEq.respectTransparency false

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

set_option backward.isDefEq.respectTransparency.types false in
theorem cepsBandUnitBridge_hasDerivAt {p p' : ℝ → ℝ} {P Q : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hp : ∀ t, |p t| ≤ P) (hp' : ∀ t, |p' t| ≤ Q)
    (hd : ∀ t, HasDerivAt p (p' t) t) (n : ℕ) (l : ℝ) {x y : ℝ}
    (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    HasDerivAt (fun t => cepsBandUnitBridge p n t x y)
      (cepsBandUnitBridgeWidth p p' n l x y) l := by
  have hc : Continuous p := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  have hm' : Measurable p' := by
    have heq : p' = deriv p := funext fun t => (hd t).deriv.symm
    rw [heq]; exact measurable_deriv p
  induction n generalizing l y with
  | zero =>
    simpa only [cepsBandUnitBridge, cepsBandUnitBridgeWidth, Function.comp_def, id_eq, one_mul] using
      (hd (l * (y - x))).comp l ((hasDerivAt_id l).mul_const (y - x))
  | succ n ih =>
    let R := |l| + 1
    let F := fun t z => cepsBandUnitBridge p n t x z * p (t * (y - z))
    let F' := fun t z => cepsBandUnitBridgeWidth p p' n t x z * p (t * (y - z)) +
      cepsBandUnitBridge p n t x z * (p' (t * (y - z)) * (y - z))
    let M := cepsBandUnitWidthBound P Q R n * P + cepsBandUnitBound P R n * Q
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hfc : Continuous (Function.uncurry F) :=
      ((continuous_cepsBandUnitBridge hc n).comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))).mul
        (hc.comp (continuous_fst.mul (continuous_const.sub continuous_snd)))
    have hfm' : Measurable (F' l) :=
      (((measurable_cepsBandUnitBridgeWidth hc hm' n).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).mul
        (hc.measurable.comp (measurable_const.mul (measurable_const.sub measurable_id)))).add
        (((continuous_cepsBandUnitBridge hc n).measurable.comp
          (measurable_const.prodMk (measurable_const.prodMk measurable_id))).mul
          ((hm'.comp (measurable_const.mul (measurable_const.sub measurable_id))).mul
            (measurable_const.sub measurable_id)))
    have hbd : ∀ᵐ z ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        ∀ t ∈ Ioo (l - 1) (l + 1), ‖F' t z‖ ≤ M := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz t ht
      have htR : |t| ≤ R := by
        dsimp [R]
        exact abs_le.mpr ⟨by linarith [neg_abs_le l, ht.1], by linarith [le_abs_self l, ht.2]⟩
      have hz' : z ∈ Icc (0 : ℝ) 1 := ⟨hz.1.le, hz.2⟩
      dsimp only [F', M]
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul (cepsBandUnitBridgeWidth_bound hP hQ hR hp hp' n htR hx hz')
          (hp _) (abs_nonneg _) (cepsBandUnitWidthBound_nonneg hP hQ hR n)
      · rw [abs_mul, abs_mul]
        have hzy : |y - z| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1, hz.2], by linarith [hy.2, hz.1]⟩
        exact mul_le_mul (cepsBandUnitBridge_bound hP hR hp n htR hx hz')
          ((mul_le_mul (hp' _) hzy (abs_nonneg _) hQ).trans_eq (mul_one _))
          (by positivity) (cepsBandUnitBound_nonneg hP hR n)
    have hdiff : ∀ᵐ z ∂(volume.restrict (Ioc (0 : ℝ) 1)),
        ∀ t ∈ Ioo (l - 1) (l + 1), HasDerivAt (F · z) (F' t z) t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz t _
      convert (ih t ⟨hz.1.le, hz.2⟩).mul
          ((hd (t * (y - z))).comp t ((hasDerivAt_id t).mul_const (y - z))) using 1 <;>
        first | rfl | (dsimp [F, F']; ring)
    have hI := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioc (0 : ℝ) 1)) (F := F) (F' := F') (bound := fun _ => M)
      (Ioo_mem_nhds (by linarith) (by linarith))
      (Eventually.of_forall fun t => (hfc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      ((hfc.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      hfm'.aestronglyMeasurable hbd (integrableOn_const (by simp)) hdiff).2
    convert (hasDerivAt_id l).mul hI using 1 <;>
      first | rfl | (dsimp [cepsBandUnitBridge, cepsBandUnitBridgeWidth, F, F']; ring)

theorem cepsBandUnitBridge_eq_fixed {p : ℝ → ℝ} {l : ℝ} (hl : 0 < l)
    (n : ℕ) (x y : ℝ) :
    cepsBandUnitBridge p n l x y =
      kepFixedBridge (fun _ => p) l 0 n (l * x) (l * y) := by
  induction n generalizing y with
  | zero => simp only [cepsBandUnitBridge, kepFixedBridge]; congr 1; ring
  | succ n ih =>
    simp only [cepsBandUnitBridge, kepFixedBridge]
    simp_rw [ih]
    have he : (fun z => kepFixedBridge (fun _ => p) l 0 n (l * x) (l * z) * p (l * (y - z))) =
        (fun z => (fun u => kepFixedBridge (fun _ => p) l 0 n (l * x) u * p (l * y - u)) (l * z)) := by
      funext z; congr 2; ring
    rw [he, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← intervalIntegral.integral_of_le hl.le]
    simpa only [smul_eq_mul, mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left
        (fun u => kepFixedBridge (fun _ => p) l 0 n (l * x) u * p (l * y - u)) l
        (a := 0) (b := 1)

/-- Each actual opposite-boundary density has a classical width derivative.
No continuity of the density derivative is assumed. -/
theorem CepsGapDensity.cepsBand_pin_differentiableAt {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D : ℝ} (hf : CepsGapDensity ν f D) (hd : Differentiable ℝ f)
    {K : ℝ≥0} (hb : ∀ x, |deriv f x| ≤ K) (β : ℝ) {a l : ℝ}
    (ha : a ≠ 0) (hl : 0 < l) (n : ℕ) :
    DifferentiableAt ℝ (fun t => krDens (Icc 0 t) ν f β a (n + 1) 0 t) l := by
  let p := fun t => f ((β - t) / a) / |a|
  let p' := fun t => deriv f ((β - t) / a) * (-1 / a) / |a|
  have hd' : ∀ t, HasDerivAt p (p' t) t := by
    intro t
    dsimp only [p, p']
    convert ((hd ((β - t) / a)).hasDerivAt.comp t
      (((hasDerivAt_const t β).sub (hasDerivAt_id t)).div_const a)).div_const |a| using 1 <;> first | rfl | ring
  have hpa : 0 < |a| := abs_pos.mpr ha
  have hp : ∀ t, |p t| ≤ D / |a| := by
    intro t; dsimp [p]; rw [abs_div, abs_abs, abs_of_nonneg (hf.nonneg _)]
    exact div_le_div_of_nonneg_right (hf.le _) hpa.le
  have hp' : ∀ t, |p' t| ≤ (K : ℝ) / |a| ^ 2 := by
    intro t; dsimp [p']; rw [abs_div, abs_mul, abs_div, abs_neg, abs_one, abs_abs]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hb _) (by positivity)) hpa.le).trans_eq (by ring)
  have h := (cepsBandUnitBridge_hasDerivAt (div_nonneg hf.nonneg_D hpa.le)
    (by positivity) hp hp' hd' n l (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1)).differentiableAt
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hl] with t ht
  rw [cepsBandUnitBridge_eq_fixed ht]
  simp only [mul_zero, mul_one]
  convert (kepFixedBridge_eq_krDens ν hf.measurable hf.nonneg hf.le hf.eq (β := β) ha n
      ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩).symm using 1
  exact kepFixedBridge_congr_at (fun z => rfl) t n 0 t

end
end PGM
