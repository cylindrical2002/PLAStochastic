import PLAStochastic.Index.GEP.Response.Defs

/-!
# Slope integration regularizes the endpoint jump

The endpoint atoms in `influence-lipschitz.md`, Section 4, produce a jump at
`a * x = 1`.  Integrating its bounded measurable coefficient over slopes
`a ∈ [1/2, 2]` gives a globally Lipschitz function of `x`.  No regularity of
that coefficient in the slope variable is needed.

This file proves that step independently of the still open killed-row and
flux estimates.  It does not assert either `KernelC` or `KernelPhi`.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter

/-- The reciprocal endpoint, clipped to the compact slope interval. -/
def kernelJumpCut (x : ℝ) : ℝ := (max (1 / 2 : ℝ) (min 2 x))⁻¹

theorem kernelJumpCut_mem (x : ℝ) : kernelJumpCut x ∈ Icc (1 / 2 : ℝ) 2 := by
  have hlo : (1 / 2 : ℝ) ≤ max (1 / 2 : ℝ) (min 2 x) := le_max_left _ _
  have hhi : max (1 / 2 : ℝ) (min 2 x) ≤ 2 := max_le (by norm_num) (min_le_left _ _)
  have hp : 0 < max (1 / 2 : ℝ) (min 2 x) := by linarith
  unfold kernelJumpCut
  rw [inv_eq_one_div]
  constructor
  · exact one_div_le_one_div_of_le hp hhi
  · apply (div_le_iff₀ hp).2
    linarith

/-- Clipping before taking the reciprocal removes its apparent singularity at zero. -/
theorem kernelJumpCut_lip (x y : ℝ) :
    |kernelJumpCut x - kernelJumpCut y| ≤ 4 * |x - y| := by
  let c : ℝ → ℝ := fun t => max (1 / 2 : ℝ) (min 2 t)
  have hc : LipschitzWith 1 c := (LipschitzWith.id.const_min 2).const_max (1 / 2)
  have hdiff : |c y - c x| ≤ |x - y| := by
    simpa [Real.dist_eq, abs_sub_comm] using hc.dist_le_mul y x
  have hx : 0 < c x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hy : 0 < c y := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hprod : (1 / 4 : ℝ) ≤ c x * c y := by
    have := mul_le_mul (show (1 / 2 : ℝ) ≤ c x from le_max_left _ _)
      (show (1 / 2 : ℝ) ≤ c y from le_max_left _ _) (by norm_num) hx.le
    norm_num at this
    exact this
  change |(c x)⁻¹ - (c y)⁻¹| ≤ _
  rw [inv_sub_inv hx.ne' hy.ne', abs_div, abs_of_pos (mul_pos hx hy)]
  apply (div_le_iff₀ (mul_pos hx hy)).2
  nlinarith [abs_nonneg (x - y)]

/-- The primitive representation of the integrated jump. -/
def kernelJumpPrimitive (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ a in (1 / 2 : ℝ)..kernelJumpCut x, f a

/-- A merely bounded, integrable slope weight suffices for the sharp moving-jump bound. -/
theorem kernelJumpPrimitive_lip {f : ℝ → ℝ} {M : ℝ}
    (hf : IntervalIntegrable f volume (1 / 2 : ℝ) 2) (hM : 0 ≤ M)
    (hb : ∀ a ∈ Icc (1 / 2 : ℝ) 2, |f a| ≤ M) (x y : ℝ) :
    |kernelJumpPrimitive f x - kernelJumpPrimitive f y| ≤ (4 * M) * |x - y| := by
  have hi (t : ℝ) : IntervalIntegrable f volume (1 / 2 : ℝ) (kernelJumpCut t) := by
    apply hf.mono_set
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]
    exact uIcc_subset_Icc ⟨le_rfl, by norm_num⟩ (kernelJumpCut_mem t)
  have hsub : kernelJumpPrimitive f x - kernelJumpPrimitive f y =
      ∫ a in kernelJumpCut y..kernelJumpCut x, f a := by
    unfold kernelJumpPrimitive
    have he := intervalIntegral.integral_add_adjacent_intervals
      (hi y) ((hi y).symm.trans (hi x))
    linarith
  rw [hsub]
  calc
    |∫ a in kernelJumpCut y..kernelJumpCut x, f a| ≤ M * |kernelJumpCut x - kernelJumpCut y| := by
      rw [← Real.norm_eq_abs]
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro a ha
      exact hb a (uIcc_subset_Icc (kernelJumpCut_mem y) (kernelJumpCut_mem x)
        (uIoc_subset_uIcc ha))
    _ ≤ M * (4 * |x - y|) := mul_le_mul_of_nonneg_left (kernelJumpCut_lip x y) hM
    _ = (4 * M) * |x - y| := by ring

/-- On the interior of the slope interval, the clipped endpoint is exactly the jump locus. -/
theorem lt_kernelJumpCut_iff {a : ℝ} (ha : a ∈ Ioo (1 / 2 : ℝ) 2) (x : ℝ) :
    a < kernelJumpCut x ↔ a * x < 1 := by
  have ha0 : 0 < a := by linarith [ha.1]
  by_cases hx : x ≤ 1 / 2
  · have hc : kernelJumpCut x = 2 := by
      unfold kernelJumpCut
      rw [min_eq_right (show x ≤ 2 by linarith), max_eq_left hx]
      norm_num
    rw [hc]
    exact iff_of_true ha.2 (by nlinarith [ha.2, mul_le_mul_of_nonneg_left hx ha0.le])
  · by_cases hx2 : 2 ≤ x
    · have hc : kernelJumpCut x = 1 / 2 := by
        norm_num [kernelJumpCut, min_eq_left hx2]
      rw [hc]
      exact iff_of_false (by linarith [ha.1])
        (by nlinarith [ha.1, mul_le_mul_of_nonneg_left hx2 ha0.le])
    · have hx0 : 0 < x := by linarith
      simp only [kernelJumpCut, min_eq_right (le_of_not_ge hx2),
        max_eq_right (le_of_not_ge hx), inv_eq_one_div]
      exact lt_div_iff₀ hx0

/-- The actual slope integral with a moving endpoint atom. -/
def kernelSlopeJump (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ a in Ioo (1 / 2 : ℝ) 2, {a : ℝ | a * x < 1}.indicator f a

/-- The primitive formula is valid even for a nonsmooth slope coefficient. -/
theorem kernelSlopeJump_eq_primitive (f : ℝ → ℝ) (x : ℝ) :
    kernelSlopeJump f x = kernelJumpPrimitive f x := by
  unfold kernelSlopeJump kernelJumpPrimitive
  rw [intervalIntegral.integral_of_le (kernelJumpCut_mem x).1, integral_Ioc_eq_integral_Ioo]
  calc
    (∫ a in Ioo (1 / 2 : ℝ) 2, {a : ℝ | a * x < 1}.indicator f a) =
        ∫ a in Ioo (1 / 2 : ℝ) 2, (Iio (kernelJumpCut x)).indicator f a := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro a ha
      have he : (a ∈ {a : ℝ | a * x < 1}) ↔ a ∈ Iio (kernelJumpCut x) :=
        (lt_kernelJumpCut_iff ha x).symm
      by_cases hm : a ∈ {a : ℝ | a * x < 1}
      · rw [indicator_of_mem hm, indicator_of_mem (he.mp hm)]
      · rw [indicator_of_notMem hm, indicator_of_notMem (fun h => hm (he.mpr h))]
    _ = ∫ a in Ioo (1 / 2 : ℝ) (kernelJumpCut x), f a := by
      have hs : Iio (kernelJumpCut x) ∩ Ioo (1 / 2 : ℝ) 2 =
          Ioo (1 / 2 : ℝ) (kernelJumpCut x) := by
        ext a
        simp only [mem_inter_iff, mem_Iio, mem_Ioo]
        constructor
        · rintro ⟨hcut, hlo, _⟩
          exact ⟨hlo, hcut⟩
        · rintro ⟨hlo, hcut⟩
          exact ⟨hcut, hlo, lt_of_lt_of_le hcut (kernelJumpCut_mem x).2⟩
      rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, hs]

/-- The endpoint-atom contribution is Lipschitz after slope integration, with no slope derivative. -/
theorem kernelSlopeJump_lip {f : ℝ → ℝ} {M : ℝ}
    (hf : IntervalIntegrable f volume (1 / 2 : ℝ) 2) (hM : 0 ≤ M)
    (hb : ∀ a ∈ Icc (1 / 2 : ℝ) 2, |f a| ≤ M) (x y : ℝ) :
    |kernelSlopeJump f x - kernelSlopeJump f y| ≤ (4 * M) * |x - y| := by
  simp only [kernelSlopeJump_eq_primitive]
  exact kernelJumpPrimitive_lip hf hM hb x y

/-- The same estimate needs only an essential bound on the coefficient.
Clipping selects a bounded representative without changing the slope integral. -/
theorem kernelSlopeJump_lip_ae {f : ℝ → ℝ} {M : ℝ}
    (hf : IntervalIntegrable f volume (1 / 2 : ℝ) 2) (hM : 0 ≤ M)
    (hb : ∀ᵐ a ∂(volume.restrict (Ioo (1 / 2 : ℝ) 2)), |f a| ≤ M) (x y : ℝ) :
    |kernelSlopeJump f x - kernelSlopeJump f y| ≤ (4 * M) * |x - y| := by
  let f' : ℝ → ℝ := fun a => max (-M) (min M (f a))
  have hbound (a : ℝ) : |f' a| ≤ M := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have he : f' =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 2)] f := by
    filter_upwards [hb] with a ha
    obtain ⟨hl, hu⟩ := abs_le.mp ha
    simp only [f', min_eq_right hu, max_eq_right hl]
  have hfi : IntervalIntegrable f' volume (1 / 2 : ℝ) 2 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hf ⊢
    exact hf.congr he.symm
  have hj (t : ℝ) : kernelSlopeJump f' t = kernelSlopeJump f t := by
    apply integral_congr_ae
    filter_upwards [he] with a ha
    by_cases hat : a ∈ {a : ℝ | a * t < 1}
    · rw [indicator_of_mem hat, indicator_of_mem hat, ha]
    · rw [indicator_of_notMem hat, indicator_of_notMem hat]
  rw [← hj x, ← hj y]
  exact kernelSlopeJump_lip hfi hM (fun a _ => hbound a) x y

/-- Integrating rowwise Lipschitz bounds only requires an integrable majorant. -/
theorem kernelIntegral_lip {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {H : α → ℝ → ℝ} {L : α → ℝ} {R : ℝ}
    (hI : ∀ x ∈ Icc 0 R, Integrable (fun a => H a x) μ) (hLI : Integrable L μ)
    (hL : ∀ x ∈ Icc 0 R, ∀ y ∈ Icc 0 R,
      ∀ᵐ a ∂μ, |H a x - H a y| ≤ L a * |x - y|)
    {x y : ℝ} (hx : x ∈ Icc 0 R) (hy : y ∈ Icc 0 R) :
    |(∫ a, H a x ∂μ) - ∫ a, H a y ∂μ| ≤ (∫ a, L a ∂μ) * |x - y| := by
  rw [← integral_sub (hI x hx) (hI y hy), ← integral_mul_const]
  simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le
    (f := fun a => H a x - H a y) (hLI.mul_const |x - y|)
    (by simpa only [Real.norm_eq_abs] using hL x hx y hy)

/-- The regular, endpoint-atom and undifferentiated error terms in the slope integral give
the exact `KernelApproxLip` shape.  This is the integration step of (H-split), not a claim
that the required row decomposition has already been constructed. -/
theorem kernelApproxLip_of_slope_split
    {H h r : ℝ → ℝ → ℝ} {f L E : ℝ → ℝ} {R M : ℝ}
    (hhI : ∀ x ∈ Icc 0 R, IntegrableOn (fun a => h a x) (Ioo (1 / 2 : ℝ) 2))
    (hrI : ∀ x ∈ Icc 0 R, IntegrableOn (fun a => r a x) (Ioo (1 / 2 : ℝ) 2))
    (hf : IntervalIntegrable f volume (1 / 2 : ℝ) 2)
    (hLI : IntegrableOn L (Ioo (1 / 2 : ℝ) 2))
    (hEI : IntegrableOn E (Ioo (1 / 2 : ℝ) 2))
    (hM : 0 ≤ M)
    (hfM : ∀ᵐ a ∂(volume.restrict (Ioo (1 / 2 : ℝ) 2)), |f a| ≤ M)
    (hsplit : ∀ x ∈ Icc 0 R, ∀ᵐ a ∂(volume.restrict (Ioo (1 / 2 : ℝ) 2)),
      H a x = h a x + {a : ℝ | a * x < 1}.indicator f a + r a x)
    (hL : ∀ x ∈ Icc 0 R, ∀ y ∈ Icc 0 R,
      ∀ᵐ a ∂(volume.restrict (Ioo (1 / 2 : ℝ) 2)), |h a x - h a y| ≤ L a * |x - y|)
    (hE : ∀ x ∈ Icc 0 R, ∀ᵐ a ∂(volume.restrict (Ioo (1 / 2 : ℝ) 2)), |r a x| ≤ E a) :
    KernelApproxLip R ((∫ a in Ioo (1 / 2 : ℝ) 2, L a) + 4 * M)
      (∫ a in Ioo (1 / 2 : ℝ) 2, E a)
      (fun x => ∫ a in Ioo (1 / 2 : ℝ) 2, H a x) := by
  classical
  have hfI : IntegrableOn f (Ioo (1 / 2 : ℝ) 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)).mp hf
  refine ⟨fun x => (∫ a in Ioo (1 / 2 : ℝ) 2, h a x) + kernelSlopeJump f x, ?_, ?_⟩
  · intro x hx y hy
    calc
      |((∫ a in Ioo (1 / 2 : ℝ) 2, h a x) + kernelSlopeJump f x) -
          ((∫ a in Ioo (1 / 2 : ℝ) 2, h a y) + kernelSlopeJump f y)| =
          |((∫ a in Ioo (1 / 2 : ℝ) 2, h a x) - ∫ a in Ioo (1 / 2 : ℝ) 2, h a y) +
            (kernelSlopeJump f x - kernelSlopeJump f y)| := by ring_nf
      _ ≤ |(∫ a in Ioo (1 / 2 : ℝ) 2, h a x) - ∫ a in Ioo (1 / 2 : ℝ) 2, h a y| +
          |kernelSlopeJump f x - kernelSlopeJump f y| := abs_add_le _ _
      _ ≤ (∫ a in Ioo (1 / 2 : ℝ) 2, L a) * |x - y| + (4 * M) * |x - y| :=
        add_le_add (kernelIntegral_lip hhI hLI hL hx hy) (kernelSlopeJump_lip_ae hf hM hfM x y)
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' : x ∈ Icc 0 R := Ioo_subset_Icc_self hx
    have hjumpI : IntegrableOn ({a : ℝ | a * x < 1}.indicator f) (Ioo (1 / 2 : ℝ) 2) :=
      hfI.indicator (measurableSet_lt (by fun_prop) measurable_const)
    have hsumI : IntegrableOn (fun a => h a x + {a : ℝ | a * x < 1}.indicator f a)
        (Ioo (1 / 2 : ℝ) 2) := (hhI x hx').add hjumpI
    have he := integral_congr_ae (hsplit x hx')
    rw [integral_add hsumI (hrI x hx'),
      integral_add (hhI x hx') hjumpI] at he
    have herr : (∫ a in Ioo (1 / 2 : ℝ) 2, H a x) -
        ((∫ a in Ioo (1 / 2 : ℝ) 2, h a x) + kernelSlopeJump f x) =
        ∫ a in Ioo (1 / 2 : ℝ) 2, r a x := by
      rw [he, kernelSlopeJump]
      ring
    rw [herr]
    simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le
      (f := fun a => r a x) hEI (by simpa only [Real.norm_eq_abs] using hE x hx')

end

end PGM
