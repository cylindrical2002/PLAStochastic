import PLAStochastic.Index.GEP.Kernel.BV.Operators
import PLAStochastic.Index.GEP.Kernel.BV.SmallEnergySplit
import PLAStochastic.Index.GEP.Kernel.BV.VariationContraction

/-!
# The actual regularizing step has a BV representative

The bound is derived from the constructed low-frequency operator. It is uniform
on the whole `L²` space, and includes both interval boundary traces.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory FourierTransform Set Filter

theorem kBVLowPass_normSq_le {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    kBVNormSq (kBVLowPass u) ≤ kBVNormSq u := by
  unfold kBVLowPass kBVNormSq
  rw [kBV_plancherelInv (kBVLowFreq_integrable h1 h2) (kBVLowFreq_memLp h1 h2),
    ← plancherel_integrable_memLp h1 h2]
  have hF2 := kill_memLp_two_fourier h1 h2
  have hFI := (memLp_two_iff_integrable_sq_norm hF2.aestronglyMeasurable).1 hF2
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hFI
    (Eventually.of_forall fun ξ => ?_)
  by_cases hξ : ξ ∈ Icc (-1 : ℝ) 1 <;> simp [kBVLowFreq, hξ]

/-- The low-pass cutoff regularizes an arbitrary `L¹ ∩ L²` input on an interval.
Unlike `split-state`, this estimate uses the input norm rather than its energy. -/
theorem kBVRegularPart_variation_norm_le {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2)
    {α w : ℝ} (hw : 1 ≤ w) :
    eVariationOn (kBVRegularPart α w u) univ ≤
      ENNReal.ofReal (8 * Real.pi * Real.sqrt w * Real.sqrt (kBVNormSq u)) := by
  have hv := kernelVariation_indicator_le (by linarith : α ≤ α + w)
    (fun x _ => kBVLowPass_hasDerivAt h1 h2 x)
    ((kBVLowPassDeriv_continuous h1 h2).intervalIntegrable α (α + w))
  apply hv.trans
  apply ENNReal.ofReal_le_ofReal
  have he := kBVEnergy_le_normSq h1 h2
  have hinter : (∫ x in α..α + w, ‖kBVLowPassDeriv u x‖) ≤
      2 * Real.pi * Real.sqrt w * Real.sqrt (kBVNormSq u) := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    exact (kBVLowPass_deriv_integral_le h1 h2 α (by linarith)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (by positivity))
  have hv2 := kBVLowPass_memLp h1 h2
  have hd2 := kBVLowPassDeriv_memLp h1 h2
  have hvi := (memLp_two_iff_integrable_sq_norm hv2.aestronglyMeasurable).1 hv2
  have hdi := (memLp_two_iff_integrable_sq_norm hd2.aestronglyMeasurable).1 hd2
  have hbound (x : ℝ) : ‖kBVLowPass u x‖ ≤ (1 + 2 * Real.pi) * Real.sqrt (kBVNormSq u) := by
    have ht := kernelTrace_left (kBVLowPass_hasDerivAt h1 h2) hv2 hd2 x
    have hvl := (setIntegral_le_integral (s := Iic x) hvi
      (Eventually.of_forall fun _ => sq_nonneg _)).trans (kBVLowPass_normSq_le h1 h2)
    have hdl := (setIntegral_le_integral (s := Iic x) hdi
      (Eventually.of_forall fun _ => sq_nonneg _)).trans
        ((kBVLowPass_deriv_normSq_le h1 h2).trans
          (mul_le_mul_of_nonneg_left he (sq_nonneg _)))
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (kBVNormSq_nonneg u)]
    nlinarith [Real.pi_pos, kBVNormSq_nonneg u]
  have hl := hbound α
  have hr := hbound (α + w)
  have hwroot : 1 ≤ Real.sqrt w := by simpa using Real.sqrt_le_sqrt hw
  have hcoef : 2 * (1 + 2 * Real.pi) ≤ 6 * Real.pi * Real.sqrt w := by
    have hpi := Real.pi_gt_three
    nlinarith
  have hlast := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (kBVNormSq u))
  nlinarith

theorem kBVProject_toLp {J : Set ℝ} (hJ : MeasurableSet J) {u : ℝ → ℂ} (h2 : MemLp u 2) :
    kBVProject J hJ (h2.toLp u) = (h2.indicator hJ).toLp (J.indicator u) := by
  apply Lp.ext
  filter_upwards [kBVProject_coe J hJ (h2.toLp u), h2.coeFn_toLp,
    (h2.indicator hJ).coeFn_toLp] with x hp hu hi
  rw [hp, hi]
  by_cases hx : x ∈ J <;> simp [hx, hu]

theorem kBVProject_toLp_of_support {J : Set ℝ} (hJ : MeasurableSet J)
    {u : ℝ → ℂ} (h2 : MemLp u 2) (hsupp : ∀ x, x ∉ J → u x = 0) :
    kBVProject J hJ (h2.toLp u) = h2.toLp u := by
  apply Lp.ext
  filter_upwards [kBVProject_coe J hJ (h2.toLp u), h2.coeFn_toLp] with x hp hu
  rw [hp]
  by_cases hx : x ∈ J
  · exact indicator_of_mem hx _
  · simp [hx, hu, hsupp x hx]

/-- The Fourier construction of `Q` is the original killed integral step on
interval-supported inputs. -/
theorem kBVKilledL2_toLp {J : Set ℝ} (hJ : MeasurableSet J) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (β a : ℝ) {u : ℝ → ℂ}
    (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2)
    (hsupp : ∀ x, x ∉ J → u x = 0) :
    kBVKilledL2 J hJ ν β a (h2.toLp u) =
      (((memLp_two_kConv ν hu h1 h2 β a).1).indicator hJ).toLp (kStep J ν β a u) := by
  change kBVProject J hJ (kBVConvolutionL2 ν β a (kBVProject J hJ (h2.toLp u))) = _
  rw [kBVProject_toLp_of_support hJ h2 hsupp, kBVConvolutionL2_toLp ν β a hu h1 h2,
    kBVProject_toLp hJ]
  rfl

/-- The actual regularized-step representative of an arbitrary `L²` vector. -/
def kBVSmoothRepresentative (α w : ℝ) (ν : Measure ℝ) (β a : ℝ) (U : KernelL2) : ℝ → ℂ :=
  kBVRegularPart α w (kConv ν β a ((Icc α (α + w)).indicator (U : ℝ → ℂ)))

/-- The constructed low-frequency step has an actual measurable, integrable BV
representative, with the full `sqrt(w)` regularization bound. -/
theorem kBVLowStepL2_regularizes (ν : Measure ℝ) [IsProbabilityMeasure ν] (β a α : ℝ)
    {w : ℝ} (hw : 1 ≤ w) (U : KernelL2) :
    ∃ g : ℝ → ℂ, Measurable g ∧ Integrable g ∧ ∃ hg2 : MemLp g 2,
      hg2.toLp g = kBVLowStepL2 (Icc α (α + w)) measurableSet_Icc ν β a U ∧
      (∀ x, x ∉ Icc α (α + w) → g x = 0) ∧
      eVariationOn g univ ≤ ENNReal.ofReal (8 * Real.pi * Real.sqrt w * ‖U‖) := by
  let J := Icc α (α + w)
  let v : ℝ → ℂ := J.indicator (U : ℝ → ℂ)
  have hv : Measurable v := (Lp.stronglyMeasurable U).measurable.indicator measurableSet_Icc
  have hv2 : MemLp v 2 := (Lp.memLp U).indicator measurableSet_Icc
  have hv1 : Integrable v := kill_integrable_of_support (by simp [J] : volume J ≠ ⊤)
    (fun _ hx => indicator_of_notMem hx _) hv2
  have hvLp : hv2.toLp v = kBVProject J measurableSet_Icc U := by
    apply Lp.ext
    exact hv2.coeFn_toLp.trans (kBVProject_coe J measurableSet_Icc U).symm
  let f := kConv ν β a v
  have hf : Measurable f := measurable_kConv ν hv β a
  have hf1 : Integrable f := integrable_kConv ν hv hv1 β a
  have hf2 : MemLp f 2 := (memLp_two_kConv ν hv hv1 hv2 β a).1
  let g := kBVRegularPart α w f
  have hg : Measurable g := (kBVLowPass_continuous hf1 hf2).measurable.indicator measurableSet_Icc
  have hg2 : MemLp g 2 := (kBVLowPass_memLp hf1 hf2).indicator measurableSet_Icc
  have hgsupp : ∀ x, x ∉ J → g x = 0 := fun _ hx => indicator_of_notMem hx _
  have hg1 : Integrable g := kill_integrable_of_support (by simp [J] : volume J ≠ ⊤) hgsupp hg2
  refine ⟨g, hg, hg1, hg2, ?_, hgsupp, ?_⟩
  · change hg2.toLp g = kBVProject J measurableSet_Icc
      (kBVLowProjectL2 (kBVConvolutionL2 ν β a (kBVProject J measurableSet_Icc U)))
    rw [← hvLp, kBVConvolutionL2_toLp ν β a hv hv1 hv2,
      kBVLowProjectL2_toLp hf1 hf2, kBVProject_toLp measurableSet_Icc]
    rfl
  · refine (kBVRegularPart_variation_norm_le hf1 hf2 hw).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← kBV_toLp_norm_sq hf2, Real.sqrt_sq (norm_nonneg _)]
    rw [← kBVConvolutionL2_toLp ν β a hv hv1 hv2, hvLp]
    exact (kBVConvolutionL2_bound ν β a _).trans (kBVProject_bound J measurableSet_Icc U)

end
end PGM
