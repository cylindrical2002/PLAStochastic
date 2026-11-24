import PLAStochastic.Index.GEP.Response.Score.ChangeOfMeasure

/-!
# WP4 leaf 4A-S, part 3: the score as a sum of single-gap insertions

Let `ν` be a law, `h` a bounded score with `∫ a h dν = ∫ a dν₁ - ∫ a dν₀`, and `ν₀, ν₁ ≤ c ν`.
For a countable family of functionals `G n i` of the iid path (`i ∈ S n` a coordinate),
`integral_tsum_insert` identifies

  `E[∑_n ∑_{i ∈ S n} G n i (g) h(g_i)] = ∫ k d(ν₁ - ν₀)`,
  `k(y) = ∑_n ∑_{i ∈ S n} E[G n i (g with g_i := y)]`,

with `k` integrable against both endpoints, as soon as `∑_n ∑_i E|G n i| < ∞`.  This is the
identification of the derivative along the mixture path with the one-gap insertion kernels of
`positive-direction-response.md` (33)–(35) (`insKernel`) and of `lawJC` (kernel-bv §8).  No
bound uniform in the inserted value is needed: all integrability is inherited from the base
law through `ν_j ≤ c ν`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

theorem lintegral_le_of_le_smul {μ ν : Measure ℝ} {c : ℝ≥0∞} (hle : μ ≤ c • ν) (f : ℝ → ℝ≥0∞) :
    ∫⁻ y, f y ∂μ ≤ c * ∫⁻ y, f y ∂ν := by
  rw [← smul_eq_mul, ← lintegral_smul_measure]
  exact lintegral_mono' hle le_rfl

/-- The inserted functional `y ↦ E[G(g with g_i := y)]` has `L¹(ν)` norm at most `E|G|`. -/
theorem lintegral_enorm_integral_update_le (ν : ProbabilityMeasure ℝ) (i : ℕ)
    {G : (ℕ → ℝ) → ℝ} (hGm : Measurable G) :
    ∫⁻ y, ‖∫ g, G (Function.update g i y) ∂(iidLaw ν)‖ₑ ∂(ν : Measure ℝ) ≤
      ∫⁻ g, ‖G g‖ₑ ∂(iidLaw ν) := by
  rw [lintegral_update ν i hGm.enorm]
  exact lintegral_mono fun y => enorm_integral_le_lintegral_enorm _

/-- **Identification of the score derivative with single-gap insertions.** -/
theorem integral_tsum_insert (ν ν₀ ν₁ : ProbabilityMeasure ℝ) {h : ℝ → ℝ}
    (hh : Measurable h) {K₀ : ℝ} (hhb : ∀ y, |h y| ≤ K₀)
    (hscore : ∀ a : ℝ → ℝ, Integrable a (ν : Measure ℝ) →
      ∫ y, a y * h y ∂(ν : Measure ℝ) = ∫ y, a y ∂(ν₁ : Measure ℝ) - ∫ y, a y ∂(ν₀ : Measure ℝ))
    {c₀ c₁ : ℝ≥0∞} (hc₀ : c₀ ≠ ⊤) (hc₁ : c₁ ≠ ⊤)
    (hle₀ : (ν₀ : Measure ℝ) ≤ c₀ • (ν : Measure ℝ))
    (hle₁ : (ν₁ : Measure ℝ) ≤ c₁ • (ν : Measure ℝ))
    (S : ℕ → Finset ℕ) (G : ℕ → ℕ → (ℕ → ℝ) → ℝ) (hGm : ∀ n i, Measurable (G n i))
    (hsum : ∑' n, ∑ i ∈ S n, ∫⁻ g, ‖G n i g‖ₑ ∂(iidLaw ν) ≠ ⊤) :
    Integrable (fun y => ∑' n, ∑ i ∈ S n, ∫ g, G n i (Function.update g i y) ∂(iidLaw ν))
        (ν₀ : Measure ℝ) ∧
      Integrable (fun y => ∑' n, ∑ i ∈ S n, ∫ g, G n i (Function.update g i y) ∂(iidLaw ν))
        (ν₁ : Measure ℝ) ∧
      ∫ g, ∑' n, ∑ i ∈ S n, G n i g * h (g i) ∂(iidLaw ν) =
        ∫ y, (∑' n, ∑ i ∈ S n, ∫ g, G n i (Function.update g i y) ∂(iidLaw ν))
            ∂(ν₁ : Measure ℝ) -
          ∫ y, (∑' n, ∑ i ∈ S n, ∫ g, G n i (Function.update g i y) ∂(iidLaw ν))
            ∂(ν₀ : Measure ℝ) := by
  set P := iidLaw ν with hP
  set K : ℕ → ℕ → ℝ → ℝ := fun n i y => ∫ g, G n i (Function.update g i y) ∂P with hK
  set Kn : ℕ → ℝ → ℝ := fun n y => ∑ i ∈ S n, K n i y with hKn
  have hK₀ : 0 ≤ K₀ := (abs_nonneg _).trans (hhb 0)
  -- integrability of the pieces
  have hGfin : ∀ n i, i ∈ S n → ∫⁻ g, ‖G n i g‖ₑ ∂P ≠ ⊤ := by
    intro n i hi
    refine ne_top_of_le_ne_top hsum ?_
    exact (Finset.single_le_sum (f := fun i => ∫⁻ g, ‖G n i g‖ₑ ∂P) (fun _ _ => zero_le) hi).trans
      (ENNReal.le_tsum (f := fun n => ∑ i ∈ S n, ∫⁻ g, ‖G n i g‖ₑ ∂P) n)
  have hGint : ∀ n i, i ∈ S n → Integrable (G n i) P := fun n i hi =>
    ⟨(hGm n i).aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_enorm]; exact (hGfin n i hi).lt_top⟩
  have hKm : ∀ n i, Measurable (K n i) := fun n i => measurable_integral_update ν i (hGm n i)
  have hKnm : ∀ n, Measurable (Kn n) := fun n =>
    Finset.measurable_sum _ fun i _ => hKm n i
  have hKint : ∀ n i, i ∈ S n → Integrable (K n i) (ν : Measure ℝ) := fun n i hi =>
    integrable_update ν i (hGm n i) (hGint n i hi)
  -- the endpoint sums
  have hKnle : ∀ {μ : Measure ℝ} {c : ℝ≥0∞}, μ ≤ c • (ν : Measure ℝ) → ∀ n,
      ∫⁻ y, ‖Kn n y‖ₑ ∂μ ≤ c * ∑ i ∈ S n, ∫⁻ g, ‖G n i g‖ₑ ∂P := by
    intro μ c hle n
    refine (lintegral_le_of_le_smul hle _).trans ?_
    gcongr
    calc ∫⁻ y, ‖Kn n y‖ₑ ∂(ν : Measure ℝ) ≤ ∫⁻ y, ∑ i ∈ S n, ‖K n i y‖ₑ ∂(ν : Measure ℝ) :=
          lintegral_mono fun y => enorm_sum_le _ _
      _ = ∑ i ∈ S n, ∫⁻ y, ‖K n i y‖ₑ ∂(ν : Measure ℝ) :=
          lintegral_finsetSum _ fun i _ => (hKm n i).enorm
      _ ≤ ∑ i ∈ S n, ∫⁻ g, ‖G n i g‖ₑ ∂P :=
          Finset.sum_le_sum fun i _ => lintegral_enorm_integral_update_le ν i (hGm n i)
  have hKnsum : ∀ {μ : Measure ℝ} {c : ℝ≥0∞}, c ≠ ⊤ → μ ≤ c • (ν : Measure ℝ) →
      ∑' n, ∫⁻ y, ‖Kn n y‖ₑ ∂μ ≠ ⊤ := by
    intro μ c hc hle
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hc hsum) ?_
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun n => hKnle hle n
  have hend : ∀ {μ : Measure ℝ} {c : ℝ≥0∞}, c ≠ ⊤ → μ ≤ c • (ν : Measure ℝ) →
      Integrable (fun y => ∑' n, Kn n y) μ ∧
        ∫ y, ∑' n, Kn n y ∂μ = ∑' n, ∫ y, Kn n y ∂μ ∧
        Summable fun n => ∫ y, Kn n y ∂μ := by
    intro μ c hc hle
    have hs := hKnsum hc hle
    refine ⟨⟨(Measurable.tsum fun n => hKnm n).aestronglyMeasurable, ?_⟩,
      integral_tsum (fun n => (hKnm n).aestronglyMeasurable) hs, ?_⟩
    · rw [hasFiniteIntegral_iff_enorm]
      calc ∫⁻ y, ‖∑' n, Kn n y‖ₑ ∂μ ≤ ∫⁻ y, ∑' n, ‖Kn n y‖ₑ ∂μ :=
            lintegral_mono fun y => enorm_tsum_le_tsum_enorm
        _ = ∑' n, ∫⁻ y, ‖Kn n y‖ₑ ∂μ := lintegral_tsum fun n => (hKnm n).enorm.aemeasurable
        _ < ⊤ := hs.lt_top
    · refine Summable.of_norm_bounded (ENNReal.summable_toReal hs) fun n => ?_
      refine (norm_integral_le_lintegral_norm _).trans ?_
      simp only [ofReal_norm]
      exact le_rfl
  obtain ⟨hI₀, hE₀, hS₀⟩ := hend hc₀ hle₀
  obtain ⟨hI₁, hE₁, hS₁⟩ := hend hc₁ hle₁
  refine ⟨hI₀, hI₁, ?_⟩
  -- the base-space side
  set F : ℕ → (ℕ → ℝ) → ℝ := fun n g => ∑ i ∈ S n, G n i g * h (g i) with hF
  have hFm : ∀ n, Measurable (F n) := fun n =>
    Finset.measurable_sum _ fun i _ => (hGm n i).mul (hh.comp (measurable_pi_apply i))
  have hFle : ∀ n, ∫⁻ g, ‖F n g‖ₑ ∂P ≤
      ENNReal.ofReal K₀ * ∑ i ∈ S n, ∫⁻ g, ‖G n i g‖ₑ ∂P := by
    intro n
    rw [Finset.mul_sum]
    calc ∫⁻ g, ‖F n g‖ₑ ∂P ≤ ∫⁻ g, ∑ i ∈ S n, ‖G n i g * h (g i)‖ₑ ∂P :=
          lintegral_mono fun g => enorm_sum_le _ _
      _ = ∑ i ∈ S n, ∫⁻ g, ‖G n i g * h (g i)‖ₑ ∂P :=
          lintegral_finsetSum _ fun i _ =>
            ((hGm n i).mul (hh.comp (measurable_pi_apply i))).enorm
      _ ≤ ∑ i ∈ S n, ENNReal.ofReal K₀ * ∫⁻ g, ‖G n i g‖ₑ ∂P := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_mono fun g => ?_
          rw [enorm_mul, mul_comm]
          gcongr
          rw [← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (hhb _)
  have hFsum : ∑' n, ∫⁻ g, ‖F n g‖ₑ ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := K₀)) hsum) ?_
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hFle
  have hterm : ∀ n, ∫ g, F n g ∂P = ∫ y, Kn n y ∂(ν₁ : Measure ℝ) -
      ∫ y, Kn n y ∂(ν₀ : Measure ℝ) := by
    intro n
    have hGhint : ∀ i ∈ S n, Integrable (fun g => G n i g * h (g i)) P := by
      intro i hi
      refine ((hGint n i hi).norm.const_mul K₀).mono'
        ((hGm n i).mul (hh.comp (measurable_pi_apply i))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun g => ?_)
      rw [norm_mul, Real.norm_eq_abs (h (g i)), mul_comm]
      exact mul_le_mul_of_nonneg_right (hhb _) (norm_nonneg _)
    have hKint₀ : ∀ i ∈ S n, Integrable (K n i) (ν₀ : Measure ℝ) := fun i hi =>
      (hKint n i hi).of_measure_le_smul hc₀ hle₀
    have hKint₁ : ∀ i ∈ S n, Integrable (K n i) (ν₁ : Measure ℝ) := fun i hi =>
      (hKint n i hi).of_measure_le_smul hc₁ hle₁
    rw [hF, integral_finsetSum _ hGhint, hKn, integral_finsetSum _ hKint₁,
      integral_finsetSum _ hKint₀, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have e := integral_update ν i (G := fun g => G n i g * h (g i))
      ((hGm n i).mul (hh.comp (measurable_pi_apply i))) (hGhint i hi)
    simp_rw [Function.update_self, integral_mul_const] at e
    rw [e]
    exact hscore (K n i) (hKint n i hi)
  rw [integral_tsum (fun n => (hFm n).aestronglyMeasurable) hFsum, hE₀, hE₁,
    ← hS₁.tsum_sub hS₀]
  exact tsum_congr hterm

end

end PGM
