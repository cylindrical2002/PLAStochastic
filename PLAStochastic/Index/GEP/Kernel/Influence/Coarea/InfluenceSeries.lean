import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.PrefixDerivative
import PLAStochastic.Index.GEP.Kernel.Flux.Prefix.InfluenceDerivative
import PLAStochastic.Index.GEP.Kernel.Flux.Sections.PrimitiveUnique

/-!
# The actual infinite influence as an absolutely summable facet derivative

The finite oriented-facet derivative inherits the original surviving-window
variation bound by uniqueness on the positive half-line. Its prescribed zero
extension then makes the bound global. This proves absolute convergence before
any reindexing of the influence series; no separate bound on an ungrouped signed
infinite facet expansion is assumed.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Interval

theorem kernel_IF_prefix_eq_zero_of_lt_two (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ≥0∞) (eps : ℝ) {k : ℕ} (hk : k < 2) (i : ℕ) :
    kernelIFPrefixKernel ν f eps k i = fun _ => 0 := by
  classical
  have hc (q : FluxFacetIndex k) : fluxFacetCoef eps q i = 0 := by
    have hn : ¬ fluxFacetValid q := by
      intro h
      have ht := q.2.2.1.isLt
      change (q.1 : ℕ) < q.2.1 ∧ (q.2.1 : ℕ) < q.2.2.1 at h
      omega
    simp only [fluxFacetCoef, if_neg hn]
  funext x
  simp [kernelIFPrefixKernel, kernelIFOrientedDensity, hc, fluxPositiveDensity]

theorem kernel_IF_prefix_aePrimitive_all (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {eps : ℝ} {k i : ℕ}
    (heps : 1 ≤ eps) (hi : i < k) :
    AEPrimitive (pwQ eps ν k i) (kernelIFPrefixKernel ν f eps k i) ∧
      Integrable (kernelIFPrefixKernel ν f eps k i) := by
  by_cases hk : 2 ≤ k
  · exact kernel_IF_prefix_aePrimitive ν hf hν hpos (by linarith) hk hi
  · rw [kernel_IF_prefix_eq_zero_of_lt_two ν f eps (by omega) i]
    have hk1 : k = 1 := by omega
    have hi0 : i = 0 := by omega
    subst k i
    refine ⟨⟨fun R => (integrable_zero _ _ _).intervalIntegrable, 1, ?_⟩,
      integrable_zero _ _ _⟩
    exact Eventually.of_forall fun x => by simp [flux_pwQ_one heps ν x]

/-- The actual finite facet derivative, rather than an existential substitute,
has the same exponentially small window variation bound. -/
theorem kernel_IF_prefix_integral_norm_le (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {eps : ℝ} {k i : ℕ}
    (heps : 1 ≤ eps) (hi : i < k) :
    (∫ x, ‖kernelIFPrefixKernel ν f eps k i x‖) ≤
      2 * (iidLaw ν).real (fluxWindow eps k i) := by
  have hac : (ν : Measure ℝ) ≪ volume := by
    rw [hν]
    exact withDensity_absolutelyContinuous _ _
  obtain ⟨j, hj, hji, hb⟩ := flux_pwQ_window_primitive_all hac hpos heps hi
  have hp := kernel_IF_prefix_aePrimitive_all ν hf hν hpos heps hi
  have he := kernel_aePrimitive_unique hp.1 hj
  have hsupp : (Ioi (0 : ℝ)).indicator (fun x => ‖kernelIFPrefixKernel ν f eps k i x‖) =
      fun x => ‖kernelIFPrefixKernel ν f eps k i x‖ := by
    funext x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · exact indicator_of_mem hx _
    · simp only [indicator_of_notMem hx, kernelIFPrefixKernel, fluxPositiveDensity,
        sub_self, norm_zero]
  calc
    _ = ∫ x in Ioi (0 : ℝ), ‖kernelIFPrefixKernel ν f eps k i x‖ := by
      rw [← integral_indicator measurableSet_Ioi, hsupp]
    _ = ∫ x in Ioi (0 : ℝ), ‖j x‖ := integral_congr_ae (he.fun_comp fun x => ‖x‖)
    _ ≤ ∫ x, ‖j x‖ := setIntegral_le_integral hji.norm
      (Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ _ := hb

/-- Absolute `L¹` convergence of the original finite influence derivatives. -/
theorem kernel_IF_prefix_norm_summable_of_tail (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {eps q : ℝ}
    (heps : 1 ≤ eps) (hq0 : 0 < q) (hq1 : q < 1)
    (htail : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m)) :
    Summable (fun b : FluxInfluenceIndex => ∫ x, ‖kernelIFPrefixKernel ν f eps b.1 b.2 x‖) := by
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun b => ?_) ((flux_geometric_index_summable hq0 hq1).mul_left 2)
  calc
    _ ≤ 2 * (iidLaw ν).real (fluxWindow eps b.1 b.2) :=
      kernel_IF_prefix_integral_norm_le ν hf hν hpos heps b.2.isLt
    _ ≤ 2 * (72 / 71 * q ^ (2 * (b.1 - 1))) :=
      mul_le_mul_of_nonneg_left (fluxWindow_le hq0.le hq1.le htail b.2.isLt) (by norm_num)
    _ = _ := by rw [flux_geometric_index_eq hq0 b]

theorem kernel_IF_prefix_ae_summable_of_tail (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {eps q : ℝ}
    (heps : 1 ≤ eps) (hq0 : 0 < q) (hq1 : q < 1)
    (htail : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m)) :
    ∀ᵐ x ∂volume, Summable (fun b : FluxInfluenceIndex => ‖kernelIFPrefixKernel ν f eps b.1 b.2 x‖) := by
  have hi (b : FluxInfluenceIndex) :=
    (kernel_IF_prefix_aePrimitive_all ν hf hν hpos heps b.2.isLt).2
  have hs := kernel_IF_prefix_norm_summable_of_tail ν hf hν hpos heps hq0 hq1 htail
  have hfinite : (∫⁻ x, ∑' b : FluxInfluenceIndex,
      ‖kernelIFPrefixKernel ν f eps b.1 b.2 x‖ₑ) ≠ ∞ := by
    rw [lintegral_tsum fun b => (hi b).aestronglyMeasurable.enorm]
    exact kernel_tsum_lintegral_enorm_ne_top hi hs
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun b => (hi b).aestronglyMeasurable.enorm)
    hfinite] with x hx
  exact tsum_enorm_ne_top_iff_summable_norm.mp hx.ne

/-- Concrete infinite influence derivative, with the original zero extension. -/
def kernelIFInfluence (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps x : ℝ) : ℝ := ∑' b : FluxInfluenceIndex, kernelIFPrefixKernel ν f eps b.1 b.2 x

theorem kernel_IF_influence_aePrimitive_of_tail (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {eps q : ℝ}
    (heps : 1 ≤ eps) (hq0 : 0 < q) (hq1 : q < 1)
    (htail : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m)) :
    AEPrimitive (lawJC eps ν) (kernelIFInfluence ν f eps) ∧ Integrable (kernelIFInfluence ν f eps) := by
  classical
  let B : FluxInfluenceIndex → ℝ := fun b => (72 / 71 / q ^ 2) * (q ^ 2) ^ b.1
  let j : FluxInfluenceIndex → ℝ → ℝ := fun b => kernelIFPrefixKernel ν f eps b.1 b.2
  have hB : Summable B := flux_geometric_index_summable hq0 hq1
  have hQ (b : FluxInfluenceIndex) (x : ℝ) : |pwQ eps ν b.1 b.2 x| ≤ B b := by
    rw [abs_of_nonneg (pwQ_nonneg eps ν b.1 b.2 x)]
    change pwQ eps ν b.1 b.2 x ≤ (72 / 71 / q ^ 2) * (q ^ 2) ^ b.1
    rw [flux_geometric_index_eq hq0 b]
    exact pwQ_le hq0.le hq1.le htail b.2.isLt x
  have hp (b : FluxInfluenceIndex) :=
    kernel_IF_prefix_aePrimitive_all ν hf hν hpos heps b.2.isLt
  have hi (b : FluxInfluenceIndex) : Integrable (j b) := (hp b).2
  have hs : Summable (fun b => ∫ x, ‖j b x‖) :=
    kernel_IF_prefix_norm_summable_of_tail ν hf hν hpos heps hq0 hq1 htail
  have hc (b : FluxInfluenceIndex) : ∃ c : ℝ,
      (∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), pwQ eps ν b.1 b.2 x = c + ∫ t in (0 : ℝ)..x, j b t) ∧
        |c| ≤ B b + ∫ x, ‖j b x‖ := by
    simpa only [Real.norm_eq_abs] using
      kernel_aePrimitive_constant_bound (hp b).1 (hi b) (fun x _ => hQ b x)
  choose c hc hcB using hc
  have hcs : Summable c := Summable.of_norm_bounded (hB.add hs)
    (fun b => by simpa only [Real.norm_eq_abs] using hcB b)
  have hslocal (R : ℝ) : Summable fun b => ∫ t in Ι (0 : ℝ) R, ‖j b t‖ :=
    Summable.of_nonneg_of_le (fun b => integral_nonneg fun _ => norm_nonneg _)
      (fun b => setIntegral_le_integral (hi b).norm
        (Eventually.of_forall fun _ => norm_nonneg _)) hs
  have hprim := kernel_aePrimitive_tsum (fun b R => (hi b).intervalIntegrable) hc hcs hslocal
  have he : (fun x => ∑' b : FluxInfluenceIndex, pwQ eps ν b.1 b.2 x) = lawJC eps ν := by
    funext x
    have hsum : Summable (fun b : FluxInfluenceIndex => pwQ eps ν b.1 b.2 x) :=
      Summable.of_norm_bounded hB (fun b => by simpa only [Real.norm_eq_abs] using hQ b x)
    rw [hsum.tsum_sigma]
    simp only [tsum_fintype, lawJC_eq_pwQ]
    apply tsum_congr
    intro k
    exact Fin.sum_univ_eq_sum_range (fun i => pwQ eps ν k i x) k
  rw [he] at hprim
  exact ⟨hprim, kernel_integrable_tsum hi hs⟩

/-- Replacing the triangular index by the original finite inner sum is valid
almost everywhere because the derivative series is absolutely summable there. -/
theorem kernel_IF_influence_ae_double_sum (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {eps q : ℝ}
    (heps : 1 ≤ eps) (hq0 : 0 < q) (hq1 : q < 1)
    (htail : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m)) :
    kernelIFInfluence ν f eps =ᵐ[volume]
      fun x => ∑' k : ℕ, ∑ i ∈ Finset.range k, kernelIFPrefixKernel ν f eps k i x := by
  filter_upwards [kernel_IF_prefix_ae_summable_of_tail ν hf hν hpos heps hq0 hq1 htail] with x hx
  rw [kernelIFInfluence, hx.of_norm.tsum_sigma]
  simp only [tsum_fintype]
  apply tsum_congr
  intro k
  exact Fin.sum_univ_eq_sum_range (fun i => kernelIFPrefixKernel ν f eps k i x) k

/-- The original regular-law assumptions supply the tail used by the concrete
infinite IF series, with a threshold uniform over the whole law class. -/
theorem kernel_IF_influence_regLaw (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ e0 : ℝ, ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ f : ℝ → ℝ≥0∞, Measurable f →
        (ν : Measure ℝ) = volume.withDensity f →
        AEPrimitive (lawJC eps ν) (kernelIFInfluence ν f eps) ∧
          Integrable (kernelIFInfluence ν f eps) ∧
          Summable (fun b : FluxInfluenceIndex => ∫ x, ‖kernelIFPrefixKernel ν f eps b.1 b.2 x‖) := by
  obtain ⟨e0, he01, hfacts⟩ := regLaw_facts hD hθ hvlo hv
  refine ⟨e0, fun eps heps ν hν f hf hνf => ?_⟩
  obtain ⟨_, _, htail, _⟩ := hfacts eps heps ν hν
  have heps1 : 1 ≤ eps := he01.trans heps
  have heps0 : 0 < eps := by linarith
  let c := tailRate * regV vlo
  have hc : 0 < c := mul_pos tailRate_pos (regV_pos hvlo)
  let q := Real.exp (-c / (4 * eps ^ 2))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hc) (by positivity)
  have hq4 : q ^ 4 = tailA vlo eps := by
    rw [show q = Real.exp (-c / (4 * eps ^ 2)) from rfl, ← Real.exp_nat_mul, tailA]
    congr 1
    dsimp [c]
    field_simp
  have ht : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m) := by
    rw [hq4]
    exact htail
  have hp := kernel_IF_influence_aePrimitive_of_tail ν hf hνf hν.ae_pos heps1 hq0 hq1 ht
  exact ⟨hp.1, hp.2,
    kernel_IF_prefix_norm_summable_of_tail ν hf hνf hν.ae_pos heps1 hq0 hq1 ht⟩

end
end PGM
