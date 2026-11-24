import PLAStochastic.ForMathlib.Probability.KingmanSum.ExponentialSeries

/-!
# Actual finite exponential sums and their CDF convolution

The convolution is derived from independence on kingmanMeasure. In particular,
the displayed integral recursion is not assumed as a law of a new process.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace BrownianAffine

theorem kingmanPartialSum_measurable (N : ℕ) : Measurable (kingmanPartialSum N) := by
  unfold kingmanPartialSum kingmanIncrement
  fun_prop

theorem kingmanPartialSum_succ (N : ℕ) (ω : ℕ → ℝ) :
    kingmanPartialSum (N + 1) ω = kingmanPartialSum N ω + kingmanIncrement N ω :=
  Finset.sum_range_succ _ _

theorem kingmanPartialSum_ae_nonneg (N : ℕ) :
    ∀ᵐ ω ∂kingmanMeasure, 0 ≤ kingmanPartialSum N ω := by
  filter_upwards [eventually_countable_forall.mpr kingmanIncrement_ae_pos] with ω hω
  exact Finset.sum_nonneg fun n _ => (hω n).le

theorem kingmanPartialSum_indep_next (N : ℕ) :
    IndepFun (kingmanPartialSum N) (kingmanIncrement N) kingmanMeasure := by
  have heq : kingmanPartialSum N = ∑ j ∈ Finset.range N, kingmanIncrement j := by
    funext ω
    simp only [kingmanPartialSum, Finset.sum_apply]
  rw [heq]
  exact kingmanIncrement_iIndepFun.indepFun_finsetSum_of_notMem kingmanIncrement_measurable
    (Finset.notMem_range_self (n := N))

/-- The CDF is defined directly by the actual partial-sum event. -/
def kingmanPartialCDF (N : ℕ) (s : ℝ) : ℝ :=
  kingmanMeasure.real {ω | kingmanPartialSum N ω ≤ s}

theorem kingmanPartialCDF_monotone (N : ℕ) : Monotone (kingmanPartialCDF N) := by
  intro s t hst
  exact measureReal_mono (fun _ h => h.trans hst)

theorem kingmanPartialCDF_measurable (N : ℕ) : Measurable (kingmanPartialCDF N) :=
  (kingmanPartialCDF_monotone N).measurable

theorem kingmanPartialCDF_of_neg (N : ℕ) {s : ℝ} (hs : s < 0) : kingmanPartialCDF N s = 0 := by
  have hn : kingmanMeasure {ω | kingmanPartialSum N ω ≤ s} = 0 := by
    have hnot : ∀ᵐ ω ∂kingmanMeasure, ¬ kingmanPartialSum N ω ≤ s := by
      filter_upwards [kingmanPartialSum_ae_nonneg N] with ω hω
      exact not_le_of_gt (hs.trans_le hω)
    simpa only [not_not] using (ae_iff.mp hnot)
  simp only [kingmanPartialCDF, measureReal_def, hn, ENNReal.toReal_zero]

theorem kingmanPartialCDF_zero {s : ℝ} (hs : 0 ≤ s) : kingmanPartialCDF 0 s = 1 := by
  simp [kingmanPartialCDF, kingmanPartialSum, hs]

/-- Real CDF convolution follows from the product measure and Tonelli's theorem. -/
theorem measureReal_halfPlane_prod (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (s : ℝ) :
    (μ.prod ν).real {p : ℝ × ℝ | p.1 + p.2 ≤ s} =
      ∫ x, ν.real (Iic (s - x)) ∂μ := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ≤ s} := by measurability
  have hslice (x : ℝ) : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ≤ s} = Iic (s - x) := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, mem_Iic]
    constructor <;> intro h <;> linarith
  rw [measureReal_def, Measure.prod_apply hm]
  rw [← integral_toReal (measurable_measure_prodMk_left hm).aemeasurable
    (Eventually.of_forall fun _ => measure_lt_top _ _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => congrArg ENNReal.toReal (congrArg ν (hslice x))

/-- The actual independent next coordinate gives the CDF convolution on the exponential law. -/
theorem kingmanPartialCDF_succ_integral (N : ℕ) (s : ℝ) :
    kingmanPartialCDF (N + 1) s =
      ∫ x, kingmanPartialCDF N (s - x) ∂expMeasure (kingmanRate N) := by
  let ν : Measure ℝ := kingmanMeasure.map (kingmanPartialSum N)
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map
    (kingmanPartialSum_measurable N).aemeasurable
  have hpair : HasLaw (fun ω => (kingmanIncrement N ω, kingmanPartialSum N ω))
      ((expMeasure (kingmanRate N)).prod ν) kingmanMeasure := by
    refine ⟨((kingmanIncrement_measurable N).prodMk (kingmanPartialSum_measurable N)).aemeasurable, ?_⟩
    rw [(kingmanPartialSum_indep_next N).symm.map_prod_eq_prod_map_map
      (kingmanIncrement_measurable N).aemeasurable (kingmanPartialSum_measurable N).aemeasurable,
      (kingmanIncrement_hasLaw N).map_eq]
  have hs := hpair.measureReal_eq (p := fun p : ℝ × ℝ => p.1 + p.2 ≤ s) (by measurability)
  have heq : {ω | kingmanPartialSum (N + 1) ω ≤ s} =
      {ω | kingmanIncrement N ω + kingmanPartialSum N ω ≤ s} := by
    ext ω
    simp only [mem_ofPred_eq, kingmanPartialSum_succ, add_comm]
  rw [← heq] at hs
  rw [measureReal_halfPlane_prod] at hs
  rw [kingmanPartialCDF, hs]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change (kingmanMeasure.map (kingmanPartialSum N)).real (Iic (s - x)) = _
  rw [map_measureReal_apply_of_aemeasurable (kingmanPartialSum_measurable N).aemeasurable measurableSet_Iic]
  rfl

/-- Positivity of the previous partial sum cuts the actual convolution down to the finite interval. -/
theorem kingmanPartialCDF_succ_convolution (N : ℕ) (s : ℝ) :
    kingmanPartialCDF (N + 1) s = ∫ x in Ioc 0 s,
      kingmanRate N * Real.exp (-(kingmanRate N * x)) * kingmanPartialCDF N (s - x) := by
  rw [kingmanPartialCDF_succ_integral, integral_expMeasure_density (kingmanRate_pos N)]
  have heq : (fun x : ℝ => kingmanRate N * Real.exp (-(kingmanRate N * x)) *
      kingmanPartialCDF N (s - x)) = (Iic s).indicator
        (fun x => kingmanRate N * Real.exp (-(kingmanRate N * x)) * kingmanPartialCDF N (s - x)) := by
    funext x
    by_cases hx : x ≤ s
    · exact (Set.indicator_of_mem (show x ∈ Iic s from hx)
        (fun x : ℝ => kingmanRate N * Real.exp (-(kingmanRate N * x)) *
          kingmanPartialCDF N (s - x))).symm
    · rw [Set.indicator_of_notMem (show x ∉ Iic s from hx),
        kingmanPartialCDF_of_neg N (by linarith : s - x < 0), mul_zero]
  conv_lhs => rw [heq]
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic s ∩ Ioi (0 : ℝ) = Ioc 0 s := by ext x; simp; tauto
  rw [hset]

/-- A finite exponential integral is obtained by subtracting two actual tail integrals. -/
theorem integral_exp_neg_Ioc {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    (∫ x in Ioc 0 s, Real.exp (-(r * x))) = (1 - Real.exp (-(r * s))) / r := by
  have h := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_exp_mul_Ioi (by linarith : -r < 0) 0)
    (integrableOn_exp_mul_Ioi (by linarith : -r < 0) s)
  rw [intervalIntegral.integral_of_le hs,
    integral_exp_mul_Ioi (by linarith : -r < 0) s,
    integral_exp_mul_Ioi (by linarith : -r < 0) 0] at h
  simp only [neg_mul, mul_zero, Real.exp_zero, neg_div_neg_eq] at h
  calc
    _ = 1 / r - Real.exp (-(r * s)) / r := by linarith
    _ = _ := by ring

theorem integral_exp_density_Ioc {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    (∫ x in Ioc 0 s, r * Real.exp (-(r * x))) = 1 - Real.exp (-(r * s)) := by
  rw [integral_const_mul, integral_exp_neg_Ioc hr hs]
  field_simp

/-- Integrating a previous exponential CDF mode against the new exponential density. -/
theorem integral_exp_convolution_mode {r b s : ℝ} (hbr : b < r) (hs : 0 ≤ s) :
    (∫ x in Ioc 0 s, r * Real.exp (-(r * x)) * Real.exp (-(b * (s - x)))) =
      r / (r - b) * (Real.exp (-(b * s)) - Real.exp (-(r * s))) := by
  have heq : (fun x : ℝ => r * Real.exp (-(r * x)) * Real.exp (-(b * (s - x)))) =
      (fun x => (r * Real.exp (-(b * s))) * Real.exp (-((r - b) * x))) := by
    funext x
    rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq, integral_const_mul, integral_exp_neg_Ioc (sub_pos.mpr hbr) hs]
  have he : Real.exp (-(b * s)) * Real.exp (-((r - b) * s)) = Real.exp (-(r * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = r / (r - b) * (Real.exp (-(b * s)) -
        Real.exp (-(b * s)) * Real.exp (-((r - b) * s))) := by ring
    _ = _ := by rw [he]

theorem kingmanRate_lt {n N : ℕ} (hn : n < N) : kingmanRate n < kingmanRate N := by
  have hcast : (n : ℝ) < N := by exact_mod_cast hn
  unfold kingmanRate
  nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n,
    show (0 : ℝ) ≤ N from Nat.cast_nonneg N]

/-- The exact finite convolution evaluated on a finite exponential expansion of the previous CDF. -/
theorem kingmanPartialCDF_succ_of_modes (N : ℕ) (A : ℕ → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → kingmanPartialCDF N t =
      1 + ∑ n ∈ Finset.range N, A n * Real.exp (-(kingmanRate n * t)))
    {s : ℝ} (hs : 0 ≤ s) :
    kingmanPartialCDF (N + 1) s = 1 - Real.exp (-(kingmanRate N * s)) +
      ∑ n ∈ Finset.range N, (A n * kingmanRate N / (kingmanRate N - kingmanRate n)) *
        (Real.exp (-(kingmanRate n * s)) - Real.exp (-(kingmanRate N * s))) := by
  have hI : IntegrableOn (fun x : ℝ => kingmanRate N * Real.exp (-(kingmanRate N * x)))
      (Ioc 0 s) := (by fun_prop : Continuous _).intervalIntegrable 0 s |>.1
  have hJ (n : ℕ) : IntegrableOn (fun x : ℝ => A n *
      (kingmanRate N * Real.exp (-(kingmanRate N * x)) * Real.exp (-(kingmanRate n * (s - x)))))
      (Ioc 0 s) := (by fun_prop : Continuous _).intervalIntegrable 0 s |>.1
  rw [kingmanPartialCDF_succ_convolution]
  calc
    _ = ∫ x in Ioc 0 s, kingmanRate N * Real.exp (-(kingmanRate N * x)) +
        ∑ n ∈ Finset.range N, A n * (kingmanRate N * Real.exp (-(kingmanRate N * x)) *
          Real.exp (-(kingmanRate n * (s - x)))) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [hA (s - x) (sub_nonneg.mpr hx.2), mul_add, mul_one, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by
      rw [integral_add hI (integrable_finsetSum _ (fun n _ => hJ n)),
        integral_exp_density_Ioc (kingmanRate_pos N) hs, integral_finsetSum _ (fun n _ => hJ n)]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul, integral_exp_convolution_mode
        (kingmanRate_lt (Finset.mem_range.mp hn)) hs]
      ring

/-- The CDF of the actual finite representative of the infinite exponential sum. -/
def kingmanCDF (s : ℝ) : ℝ := kingmanMeasure.real {ω | kingmanTotalReal ω ≤ s}

/-- Nonnegative partial sums converge to the total CDF even at atoms, by monotonicity of each path. -/
theorem kingmanPartialCDF_tendsto (s : ℝ) :
    Tendsto (fun N => kingmanPartialCDF N s) atTop (𝓝 (kingmanCDF s)) := by
  have hmeas (N : ℕ) : MeasurableSet {ω | kingmanPartialSum N ω ≤ s} :=
    measurableSet_le (kingmanPartialSum_measurable N) measurable_const
  have htotal : MeasurableSet {ω | kingmanTotalReal ω ≤ s} :=
    measurableSet_le kingmanTotalReal_measurable measurable_const
  have heq (N : ℕ) : kingmanPartialCDF N s = ∫ ω,
      ({ω | kingmanPartialSum N ω ≤ s}.indicator (1 : (ℕ → ℝ) → ℝ)) ω ∂kingmanMeasure :=
    (integral_indicator_one (hmeas N)).symm
  simp_rw [heq]
  unfold kingmanCDF
  rw [← integral_indicator_one htotal]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro N
    exact (measurable_const.indicator (hmeas N)).aestronglyMeasurable
  · exact integrable_const 1
  · intro N
    apply Eventually.of_forall
    intro ω
    by_cases h : kingmanPartialSum N ω ≤ s <;>
      simp [Set.indicator, h]
  · filter_upwards [kingmanIncrement_ae_hasSum,
      eventually_countable_forall.mpr kingmanIncrement_ae_pos] with ω hsum hpos
    by_cases h : kingmanTotalReal ω ≤ s
    · have hpartial (N : ℕ) : kingmanPartialSum N ω ≤ s := by
        apply le_trans _ h
        rw [← hsum.tsum_eq]
        exact hsum.summable.sum_le_tsum (Finset.range N) (fun n _ => (hpos n).le)
      simp only [Set.indicator, mem_ofPred_eq, if_pos h, Pi.one_apply]
      apply tendsto_const_nhds.congr'
      exact Eventually.of_forall fun N => by simp [hpartial N]
    · have hevent : ∀ᶠ N in atTop, s < kingmanPartialSum N ω :=
        hsum.tendsto_sum_nat.eventually_const_lt (lt_of_not_ge h)
      simp only [Set.indicator, mem_ofPred_eq, if_neg h]
      apply tendsto_const_nhds.congr'
      filter_upwards [hevent] with N hN
      simp [not_le.mpr hN]

end BrownianAffine
