import PLAStochastic.Index.GEP.Kernel.BV.Translation

/-!
# The last real killed step

A bounded-density probability law sends every measurable L² remainder to a
uniformly bounded function. No boundedness of the input remainder is assumed.
Together with the BV translation estimate, this is the final smoothing step
used after the long-time BV decomposition.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

/-- Each pointwise convolution integral exists for an arbitrary measurable
`L²` input. Boundedness of the representative is not needed. -/
theorem kernel_kConv_integrable {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {D a β : ℝ} (hρ : LocBd D ρ) (ha : a ≠ 0)
    {f : ℝ → ℂ} (hm : Measurable f) (hf : MemLp f 2) (x : ℝ) :
    Integrable (fun t => f (x + β - a * t)) ρ := by
  have hdom : ρ ≤ ENNReal.ofReal D • (volume : Measure ℝ) := by
    apply Measure.le_iff.mpr
    intro A hA
    simpa only [Measure.smul_apply, smul_eq_mul] using hρ A hA
  have hf2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hvol : Integrable (fun t => ‖f (x + β - a * t)‖ ^ 2) := by
    have hh := (hf2.comp_add_left (x + β)).comp_mul_left' (neg_ne_zero.mpr ha)
    convert hh using 1
    funext t
    congr 3
    ring
  have hi2 : Integrable (fun t => ‖f (x + β - a * t)‖ ^ 2) ρ :=
    (hvol.smul_measure ENNReal.ofReal_ne_top).mono_measure hdom
  have hm' : Measurable (fun t => f (x + β - a * t)) := hm.comp (by fun_prop)
  have hmem : MemLp (fun t => f (x + β - a * t)) 2 ρ :=
    (memLp_two_iff_integrable_sq_norm hm'.aestronglyMeasurable).2 hi2
  exact hmem.integrable (by norm_num)

/-- A real killed step preserves an exact decomposition of measurable `L²`
representatives at every point, including the endpoints. -/
theorem kernel_kStep_add {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {D a β : ℝ} (hρ : LocBd D ρ) (ha : a ≠ 0)
    {f g : ℝ → ℂ} (hf : Measurable f) (hf2 : MemLp f 2)
    (hg : Measurable g) (hg2 : MemLp g 2) (J : Set ℝ) :
    kStep J ρ β a (f + g) = kStep J ρ β a f + kStep J ρ β a g := by
  funext x
  by_cases hx : x ∈ J
  · simp only [kStep, indicator_of_mem hx, Pi.add_apply]
    exact integral_add (kernel_kConv_integrable hρ ha hf hf2 x)
      (kernel_kConv_integrable hρ ha hg hg2 x)
  · simp only [kStep, indicator_of_notMem hx, Pi.add_apply, zero_add]

theorem kernel_kConv_norm_sq_le {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {D a β : ℝ} (hρ : LocBd D ρ) (hD : 0 ≤ D) (ha : a ≠ 0)
    {f : ℝ → ℂ} (hm : Measurable f) (hf : MemLp f 2) (x : ℝ) :
    ‖kConv ρ β a f x‖ ^ 2 ≤ D / |a| * ∫ t, ‖f t‖ ^ 2 := by
  have hdom : ρ ≤ ENNReal.ofReal D • (volume : Measure ℝ) := by
    apply Measure.le_iff.mpr
    intro A hA
    simpa only [Measure.smul_apply, smul_eq_mul] using hρ A hA
  have hf2 := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hvol : Integrable (fun t => ‖f (x + β - a * t)‖ ^ 2) := by
    have hh := (hf2.comp_add_left (x + β)).comp_mul_left' (neg_ne_zero.mpr ha)
    convert hh using 1
    funext t
    congr 3
    ring
  have hi2 : Integrable (fun t => ‖f (x + β - a * t)‖ ^ 2) ρ :=
    (hvol.smul_measure ENNReal.ofReal_ne_top).mono_measure hdom
  have hm' : Measurable (fun t => f (x + β - a * t)) := hm.comp (by fun_prop)
  have hmem : MemLp (fun t => f (x + β - a * t)) 2 ρ :=
    (memLp_two_iff_integrable_sq_norm hm'.aestronglyMeasurable).2 hi2
  have hi1 := hmem.integrable (by norm_num)
  have hcs := kill_sq_integral_le hi1.norm hi2
  rw [probReal_univ, one_mul] at hcs
  have hcv : (∫ t, ‖f (x + β - a * t)‖ ^ 2) = |a|⁻¹ * ∫ t, ‖f t‖ ^ 2 := by
    have he : (fun t => ‖f (x + β - a * t)‖ ^ 2) =
        fun t => ‖f ((x + β) + (-a) * t)‖ ^ 2 := by
      funext t
      congr 3
      ring
    rw [he, Measure.integral_comp_mul_left (fun t => ‖f ((x + β) + t)‖ ^ 2) (-a),
      integral_add_left_eq_self (fun t : ℝ => ‖f t‖ ^ 2) (x + β),
      smul_eq_mul, abs_inv, abs_neg]
  calc
    ‖kConv ρ β a f x‖ ^ 2 ≤ (∫ t, ‖f (x + β - a * t)‖ ∂ρ) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖f (x + β - a * t)‖ ^ 2 ∂ρ := hcs
    _ ≤ ∫ t, ‖f (x + β - a * t)‖ ^ 2 ∂(ENNReal.ofReal D • (volume : Measure ℝ)) :=
      integral_mono_measure hdom (Eventually.of_forall fun _ => sq_nonneg _)
        (hvol.smul_measure ENNReal.ofReal_ne_top)
    _ = D / |a| * ∫ t, ‖f t‖ ^ 2 := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal hD, smul_eq_mul, hcv]
      ring

theorem kernel_kStep_norm_sq_le {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {D a β : ℝ} (hρ : LocBd D ρ) (hD : 0 ≤ D) (ha : a ≠ 0)
    {f : ℝ → ℂ} (hm : Measurable f) (hf : MemLp f 2) (J : Set ℝ) (x : ℝ) :
    ‖kStep J ρ β a f x‖ ^ 2 ≤ D / |a| * ∫ t, ‖f t‖ ^ 2 := by
  apply le_trans ?_ (kernel_kConv_norm_sq_le (β := β) hρ hD ha hm hf x)
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact norm_indicator_le_norm_self _ _

theorem kernel_kStep_lip_on {ρ : Measure ℝ} {D a β : ℝ}
    (hρ : LocBd D ρ) (hD : 0 ≤ D) (ha : a ≠ 0)
    {f : ℝ → ℂ} (hf : BoundedVariationOn f univ) (hi : Integrable f)
    {J : Set ℝ} {x y : ℝ} (hx : x ∈ J) (hy : y ∈ J) :
    ‖kStep J ρ β a f x - kStep J ρ β a f y‖ ≤
      (D / |a| * (eVariationOn f univ).toReal) * |x - y| := by
  unfold kStep
  rw [indicator_of_mem hx, indicator_of_mem hy]
  exact kernel_kConv_lip hρ hD ha hf hi x y

end
end PGM
