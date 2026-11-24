import PLAStochastic.ForMathlib.Probability.Kernel.Doeblin.ResidualSeries

/-! # The geometric total-variation bound and uniqueness

Every two initial probability measures have the same finite reset contribution
after `n` steps. Their remaining measures each have mass `(1 - β univ)^n`.
This proves the total-variation estimate directly, without assuming a
contraction theorem or an invariant measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal ProbabilityTheory Topology
namespace SwingRepair.Doeblin
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {S : Type*} [MeasurableSpace S]

/-- Total variation in the probability convention, the supremum of absolute
differences on measurable sets. -/
def totalVariation (μ η : Measure S) : ℝ≥0∞ :=
  ⨆ s : {s : Set S // MeasurableSet s}, ENNReal.ofReal |(μ s.1).toReal - (η s.1).toReal|

theorem iterate_of_invariant (P : Kernel S S) (μ : Measure S) (hμ : P.Invariant μ) (n : ℕ) :
    iterate P n μ = μ := by
  induction n with
  | zero => rfl
  | succ n ih => exact (congrArg (fun η => P ∘ₘ η) ih).trans hμ

variable (P : Kernel S S) [IsMarkovKernel P]
variable (β : Measure S) [IsFiniteMeasure β] (hminor : ∀ x, β ≤ P x)
include hminor

/-- The two iterates share a common positive measure, leaving only their
respective residual excursions. -/
theorem iterate_common_part (μ η : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (n : ℕ) : ∃ C : Measure S,
      iterate P n μ = C + iterate (residual P β hminor) n μ ∧
      iterate P n η = C + iterate (residual P β hminor) n η := by
  induction n with
  | zero => exact ⟨0, (zero_add _).symm, (zero_add _).symm⟩
  | succ n ih =>
    obtain ⟨C, hCμ, hCη⟩ := ih
    refine ⟨residual P β hminor ∘ₘ C + β, ?_, ?_⟩
    · rw [iterate_succ, transition_decomposition P β hminor, measure_univ, one_smul,
        hCμ, Measure.comp_add, iterate_succ]
      ac_rfl
    · rw [iterate_succ, transition_decomposition P β hminor, measure_univ, one_smul,
        hCη, Measure.comp_add, iterate_succ]
      ac_rfl

/-- Uniform geometric bound on each measurable set. -/
theorem iterate_set_bound (μ η : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (n : ℕ) (s : Set S) :
    |(iterate P n μ s).toReal - (iterate P n η s).toReal| ≤ (1 - β univ).toReal ^ n := by
  obtain ⟨C, hCμ, hCη⟩ := iterate_common_part P β hminor μ η n
  let R := residual P β hminor
  have hmμ : iterate R n μ univ = (1 - β univ)^n := by
    simp only [iterate_mass R (residual_mass P β hminor), measure_univ, mul_one]
  have hmη : iterate R n η univ = (1 - β univ)^n := by
    simp only [iterate_mass R (residual_mass P β hminor), measure_univ, mul_one]
  have hq : (1 - β univ)^n ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)
  have hrμ : iterate R n μ s ≠ ⊤ := ne_top_of_le_ne_top hq (by rw [← hmμ]; exact measure_mono (subset_univ _))
  have hrη : iterate R n η s ≠ ⊤ := ne_top_of_le_ne_top hq (by rw [← hmη]; exact measure_mono (subset_univ _))
  have hc : C s ≠ ⊤ := by
    apply ne_top_of_le_ne_top (measure_ne_top (iterate P n μ) s)
    rw [hCμ, Measure.add_apply]
    exact le_add_right le_rfl
  have hlμ : (iterate R n μ s).toReal ≤ (1 - β univ).toReal ^ n := by
    rw [← ENNReal.toReal_pow]
    exact ENNReal.toReal_mono hq (by rw [← hmμ]; exact measure_mono (subset_univ _))
  have hlη : (iterate R n η s).toReal ≤ (1 - β univ).toReal ^ n := by
    rw [← ENNReal.toReal_pow]
    exact ENNReal.toReal_mono hq (by rw [← hmη]; exact measure_mono (subset_univ _))
  rw [hCμ, hCη, Measure.add_apply, Measure.add_apply, ENNReal.toReal_add hc hrμ,
    ENNReal.toReal_add hc hrη]
  have hnμ : 0 ≤ (iterate R n μ s).toReal := ENNReal.toReal_nonneg
  have hnη : 0 ≤ (iterate R n η s).toReal := ENNReal.toReal_nonneg
  apply abs_le.mpr
  constructor <;> linarith

/-- Geometric total-variation bound for any two initial probability measures. -/
theorem iterate_totalVariation_bound (μ η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η] (n : ℕ) :
    totalVariation (iterate P n μ) (iterate P n η) ≤ (1 - β univ)^n := by
  apply iSup_le
  intro s
  have hb := ENNReal.ofReal_le_ofReal (iterate_set_bound P β hminor μ η n s.1)
  simpa only [← ENNReal.toReal_pow, ENNReal.ofReal_toReal
    (ENNReal.pow_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top))] using hb

omit hminor [IsFiniteMeasure β] in
theorem residual_rate_lt_one (hβ : 0 < β univ) : (1 - β univ).toReal < 1 := by
  have he : (1 : ℝ≥0∞) - β univ < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hβ.ne'
  exact (ENNReal.toReal_lt_toReal (ENNReal.sub_ne_top ENNReal.one_ne_top) ENNReal.one_ne_top).mpr he

/-- Uniqueness follows from the geometric estimate, rather than being an
assumption of the minorization argument. -/
theorem invariant_unique (hβ : 0 < β univ) (μ η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η] (hμ : P.Invariant μ) (hη : P.Invariant η) :
    μ = η := by
  ext s hs
  have hb (n : ℕ) : |(μ s).toReal - (η s).toReal| ≤ (1 - β univ).toReal^n := by
    simpa only [iterate_of_invariant P μ hμ, iterate_of_invariant P η hη] using
      iterate_set_bound P β hminor μ η n s
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (1 - β univ).toReal from ENNReal.toReal_nonneg)
    (residual_rate_lt_one β hβ)
  have hz : |(μ s).toReal - (η s).toReal| ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hb
  have he : (μ s).toReal = (η s).toReal := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ s) (measure_ne_top η s)).mp he

/-- The explicit invariant series is the unique invariant probability, with a
uniform geometric total-variation bound from every initial probability law. -/
theorem exists_unique_invariant (hβ : 0 < β univ) (hβ1 : β univ ≤ 1) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ P.Invariant π ∧
      (∀ μ : Measure S, IsProbabilityMeasure μ → P.Invariant μ → μ = π) ∧
      ∀ μ : Measure S, IsProbabilityMeasure μ → ∀ n : ℕ,
        totalVariation (iterate P n μ) π ≤ (1 - β univ)^n := by
  let π := invariantSeries P β hminor
  let : IsProbabilityMeasure π := invariantSeries_isProbabilityMeasure P β hminor hβ hβ1
  have hπ : P.Invariant π := invariantSeries_invariant P β hminor hβ hβ1
  refine ⟨π, inferInstance, hπ, ?_, ?_⟩
  · intro μ hμ hμP
    let := hμ
    exact invariant_unique P β hminor hβ μ π hμP hπ
  · intro μ hμ n
    let := hμ
    simpa only [iterate_of_invariant P π hπ] using iterate_totalVariation_bound P β hminor μ π n

end SwingRepair.Doeblin
