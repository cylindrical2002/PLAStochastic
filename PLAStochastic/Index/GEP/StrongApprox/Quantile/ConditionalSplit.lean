import PLAStochastic.Index.GEP.StrongApprox.LocalCLT.SmoothedDensity

/-!
# WP5: normalized conditional densities for a dyadic split

For two independent variables with the same positive bounded density `p`, the
conditional density of the first given their sum `a` is proportional to
`p x * p (a - x)`. This file constructs the normalized family and proves the
joint measurability and exact marginal law of its quantile sampler.
-/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

/-- A continuous positive bounded probability density. -/
structure SADensity (p : ℝ → ℝ) : Prop where
  continuous : Continuous p
  pos : ∀ x, 0 < p x
  integrable : Integrable p
  mass : ∫ x, p x = 1
  bounded : ∃ C : ℝ, ∀ x, p x ≤ C

/-- Extract the real integral conditions from an actual probability density. -/
theorem saDensity_of_probability {p : ℝ → ℝ} (hc : Continuous p) (hp : ∀ x, 0 < p x)
    (hb : ∃ C : ℝ, ∀ x, p x ≤ C)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (p x)))] :
    SADensity p := by
  have hl : (∫⁻ x, ENNReal.ofReal (p x)) = 1 := by
    simpa only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using
      (measure_univ (μ := volume.withDensity (fun x => ENNReal.ofReal (p x))))
  have hi : Integrable p := ⟨hc.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => (hp x).le)).mpr (by rw [hl]; simp)⟩
  refine ⟨hc, hp, hi, ?_, hb⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (hp x).le)] at hl
  exact ENNReal.ofReal_eq_one.mp hl

theorem saDensity_gaussian (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ≥0} (hv : v ≠ 0) : SADensity (saGaussianDensity μ v) := by
  have : IsProbabilityMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (saGaussianDensity μ v x))) := by
    rw [saGaussianDensity_law μ hv]
    infer_instance
  exact saDensity_of_probability (continuous_saGaussianDensity μ v)
    (saGaussianDensity_pos μ hv) ⟨_, saGaussianDensity_le μ v⟩

/-- The probability measure represented by a density. -/
def SADensity.law {p : ℝ → ℝ} (hp : SADensity p) : ProbabilityMeasure ℝ :=
  ⟨volume.withDensity (fun x => ENNReal.ofReal (p x)), ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hp.integrable (ae_of_all _ fun x => (hp.pos x).le),
      hp.mass, ENNReal.ofReal_one]⟩⟩

theorem SADensity.regularCDF {p : ℝ → ℝ} (hp : SADensity p) :
    SACDF (cdf (hp.law : Measure ℝ)) := by
  have : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (p x))) := hp.law.prop
  exact saCDF_withDensity hp.continuous.measurable hp.pos

/-- Equality of laws fixes a continuous density at every point. -/
theorem SADensity.eq_of_law {p q : ℝ → ℝ} (hp : SADensity p) (hq : SADensity q)
    (he : (hp.law : Measure ℝ) = (hq.law : Measure ℝ)) : p = q := by
  have hae : (fun x => ENNReal.ofReal (p x)) =ᵐ[volume] fun x => ENNReal.ofReal (q x) :=
    (withDensity_eq_iff_of_sigmaFinite hp.continuous.measurable.ennreal_ofReal.aemeasurable
      hq.continuous.measurable.ennreal_ofReal.aemeasurable).mp he
  apply hp.continuous.ae_eq_iff_eq volume hq.continuous |>.mp
  filter_upwards [hae] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hp.pos x).le (hq.pos x).le).mp hx

/-- The density of a sum of two variables with density `p`. -/
def saSumDensity (p : ℝ → ℝ) (a : ℝ) : ℝ := ∫ x, p x * p (a - x)

theorem SADensity.integrable_split_product {p : ℝ → ℝ} (hp : SADensity p) (a : ℝ) :
    Integrable (fun x => p x * p (a - x)) := by
  obtain ⟨C, hC⟩ := hp.bounded
  refine (hp.integrable.mul_const C).mono'
    ((hp.continuous.mul (hp.continuous.comp
      (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hp.pos x) (hp.pos (a - x)))]
  exact mul_le_mul_of_nonneg_left (hC _) (hp.pos x).le

theorem SADensity.sumDensity_pos {p : ℝ → ℝ} (hp : SADensity p) (a : ℝ) :
    0 < saSumDensity p a := by
  apply (integral_pos_iff_support_of_nonneg (fun x => mul_nonneg (hp.pos x).le (hp.pos _).le)
    (hp.integrable_split_product a)).mpr
  have he : Function.support (fun x => p x * p (a - x)) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (mul_pos (hp.pos _) (hp.pos _)).ne'
  rw [he]
  simp

theorem SADensity.continuous_sumDensity {p : ℝ → ℝ} (hp : SADensity p) :
    Continuous (saSumDensity p) := by
  obtain ⟨C, hC⟩ := hp.bounded
  apply continuous_of_dominated (bound := fun x => p x * C)
    (fun a => (hp.integrable_split_product a).aestronglyMeasurable)
    (fun a => ae_of_all _ fun x => ?_) (hp.integrable.mul_const C)
    (ae_of_all _ fun x => continuous_const.mul (hp.continuous.comp (continuous_id.sub continuous_const)))
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hp.pos x) (hp.pos (a - x)))]
  exact mul_le_mul_of_nonneg_left (hC _) (hp.pos x).le

theorem SADensity.sumDensity_law {p : ℝ → ℝ} (hp : SADensity p) :
    volume.withDensity (fun a => ENNReal.ofReal (saSumDensity p a)) =
      (hp.law : Measure ℝ) ∗ (hp.law : Measure ℝ) := by
  change _ = (volume.withDensity (fun x => ENNReal.ofReal (p x))) ∗
    (volume.withDensity (fun x => ENNReal.ofReal (p x)))
  rw [conv_withDensity_eq_lconvolution hp.continuous.measurable.ennreal_ofReal
    hp.continuous.measurable.ennreal_ofReal]
  congr 1
  funext a
  rw [saSumDensity, ofReal_integral_eq_lintegral_ofReal (hp.integrable_split_product a)
    (ae_of_all _ fun x => mul_nonneg (hp.pos x).le (hp.pos _).le), lconvolution_def]
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_mul (hp.pos x).le]
  simp only [sub_eq_add_neg, add_comm]

theorem SADensity.sumDensity {p : ℝ → ℝ} (hp : SADensity p) : SADensity (saSumDensity p) := by
  have : IsProbabilityMeasure (volume.withDensity (fun a => ENNReal.ofReal (saSumDensity p a))) := by
    rw [hp.sumDensity_law]
    infer_instance
  apply saDensity_of_probability hp.continuous_sumDensity hp.sumDensity_pos
  obtain ⟨C, hC⟩ := hp.bounded
  refine ⟨C, fun a => ?_⟩
  calc
    _ ≤ ∫ x, p x * C := integral_mono (hp.integrable_split_product a)
      (hp.integrable.mul_const C) (fun x => mul_le_mul_of_nonneg_left (hC _) (hp.pos x).le)
    _ = C := by rw [integral_mul_const, hp.mass, one_mul]

/-- The conditional density of the left child, for every real parent total. -/
def saSplitDensity (p : ℝ → ℝ) (a x : ℝ) : ℝ := p x * p (a - x) / saSumDensity p a

theorem SADensity.splitDensity {p : ℝ → ℝ} (hp : SADensity p) (a : ℝ) :
    SADensity (saSplitDensity p a) := by
  refine ⟨?_, ?_, (hp.integrable_split_product a).div_const _, ?_, ?_⟩
  · exact (hp.continuous.mul (hp.continuous.comp (continuous_const.sub continuous_id))).div_const _
  · intro x
    exact div_pos (mul_pos (hp.pos x) (hp.pos _)) (hp.sumDensity_pos a)
  · change (∫ x, p x * p (a - x) / saSumDensity p a) = 1
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const]
    rw [← div_eq_mul_inv]
    exact div_self (hp.sumDensity_pos a).ne'
  · obtain ⟨C, hC⟩ := hp.bounded
    have hC0 : 0 ≤ C := (hp.pos 0).le.trans (hC 0)
    refine ⟨C ^ 2 / saSumDensity p a, fun x => ?_⟩
    apply div_le_div_of_nonneg_right _ (hp.sumDensity_pos a).le
    exact (mul_le_mul (hC x) (hC (a - x)) (hp.pos _).le hC0).trans_eq (pow_two C).symm

theorem SADensity.continuous_splitDensity {p : ℝ → ℝ} (hp : SADensity p) :
    Continuous (fun z : ℝ × ℝ => saSplitDensity p z.1 z.2) := by
  exact ((hp.continuous.comp continuous_snd).mul
    (hp.continuous.comp (continuous_fst.sub continuous_snd))).div
      (hp.continuous_sumDensity.comp continuous_fst) (fun z => (hp.sumDensity_pos z.1).ne')

/-- The conditional distribution functions are measurable in the parent total. -/
theorem SADensity.measurable_splitCDF {p : ℝ → ℝ} (hp : SADensity p) (x : ℝ) :
    Measurable (fun a => cdf ((hp.splitDensity a).law : Measure ℝ) x) := by
  have he : (fun a => cdf ((hp.splitDensity a).law : Measure ℝ) x) =
      fun a => ENNReal.toReal (∫⁻ y in Iic x, ENNReal.ofReal (saSplitDensity p a y)) := by
    funext a
    rw [cdf_eq_real, measureReal_def]
    change (volume.withDensity (fun y => ENNReal.ofReal (saSplitDensity p a y)) (Iic x)).toReal = _
    rw [withDensity_apply _ measurableSet_Iic]
  rw [he]
  exact (hp.continuous_splitDensity.measurable.ennreal_ofReal.lintegral_prod_right
    (ν := volume.restrict (Iic x))).ennreal_toReal

/-- The measurable splitting map driven by one uniform innovation. -/
def saSplitQuantile {p : ℝ → ℝ} (hp : SADensity p) (a u : ℝ) : ℝ :=
  saQuantile (cdf ((hp.splitDensity a).law : Measure ℝ)) u

theorem SADensity.measurable_splitQuantile {p : ℝ → ℝ} (hp : SADensity p) :
    Measurable (fun z : ℝ × ℝ => saSplitQuantile hp z.1 z.2) :=
  measurable_saQuantile (fun a => (hp.splitDensity a).regularCDF) hp.measurable_splitCDF

theorem SADensity.splitQuantile_law {p : ℝ → ℝ} (hp : SADensity p) (a : ℝ) :
    saUniform.map (saSplitQuantile hp a) = ((hp.splitDensity a).law : Measure ℝ) :=
  saQuantile_map_uniform _ (hp.splitDensity a).regularCDF

end

end PGM
