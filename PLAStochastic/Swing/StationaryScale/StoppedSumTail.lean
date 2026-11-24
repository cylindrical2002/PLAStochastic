import PLAStochastic.Swing.SecondSegment.MeanLowerBound
import PLAStochastic.ForMathlib.Probability.Moments.NatMeanTailSumLower

/-! # A stopped-sum tail bound for the selected rejection increment

The increment that ends a segment is chosen by the stopping rule, so it has no
Gaussian law of its own.  Summing over the predictable survival events instead
gives the exact `E[N]` factor: this is the stopped-sum step
`eq:stationaryrawtail` of Appendix `app:margins`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

omit mΩ in
/-- Survival past the `k`-th fresh increment is decided before that increment. -/
theorem measurableSet_nativeRestartLength_ge_history (X : ℕ → Ω → ℝ) (E x : ℝ) (k : ℕ) :
    MeasurableSet[incrementIndexSpace X (Iio k)]
      {ω | ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω} := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio k)
  have hts : StrictMono (fun i : ℕ => (i : ℝ)) := by
    intro a b hab
    change (a : ℝ) < b
    exact_mod_cast hab
  have hY : ∀ i ∈ Finset.Icc 1 (k+1),
      Measurable (nativeCarriedSamples X (fun _ => x) i) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hik : i ≤ k+1 := (Finset.mem_Icc.mp hi).2
    obtain ⟨j, rfl⟩ : ∃ j, i = j+1 := ⟨i-1, by omega⟩
    have hcum : Measurable (cumulativeSamples X j) := by
      apply Finset.measurable_sum
      intro m hm
      exact incrementIndexSpace_eval (X := X)
        (show m ∈ Set.Iio k from Set.mem_Iio.mpr (by
          have := Finset.mem_range.mp hm
          omega))
    have heq : nativeCarriedSamples X (fun _ => x) (j+1) =
        fun ω => x+cumulativeSamples X j ω := by
      funext ω
      exact nativeCarriedSamples_succ X (fun _ => x) j ω
    rw [heq]
    exact measurable_const.add hcum
  have hset : {ω | ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω} =
      {ω | nativePrefixFeasible (fun i => (i : ℝ))
        (fun i => nativeCarriedSamples X (fun _ => x) i ω) E 0 (k+1) ((fun _ => (0 : ℝ)) ω)} := by
    ext ω
    exact le_nativePrefixLength_iff (nativeCarriedSamples X (fun _ => x)) (fun _ => 0) E ω (k+1)
  rw [hset]
  exact nativePrefixFeasible_measurableSet (fun i => (i : ℝ)) hts
    (nativeCarriedSamples X (fun _ => x)) E 0 (k+1) (by omega) measurable_const hY

/-- Independence of the survival event from the increment that may end the segment. -/
theorem measure_nativeRestart_survival_inter
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (E x : ℝ) (k : ℕ) {B : Set ℝ}
    (hB : MeasurableSet B) :
    μ ({ω | ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω} ∩ (X k) ⁻¹' B) =
      μ {ω | ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω}*gaussianReal 0 1 B := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set A : Set Ω := {ω | ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω} with hA
  have hAhist := measurableSet_nativeRestartLength_ge_history X E x k
  have hpair := (@iid_two_fresh_gaussians_of_history Ω Ω mΩ
    (incrementIndexSpace X (Iio k)) μ X hX hi hG k id measurable_id).1
  have hind : @IndepFun Ω Ω ℝ mΩ (incrementIndexSpace X (Iio k)) Real.measurableSpace
      (fun w => w) (fun w => X k w) μ := by
    simpa only [Function.comp_def, id_eq] using hpair.comp measurable_id measurable_fst
  have hmul := hind.measure_inter_preimage_eq_mul (s := A) (t := B) hAhist hB
  simp only [Set.preimage_id'] at hmul
  have hlaw : μ ((X k) ⁻¹' B) = gaussianReal 0 1 B := by
    rw [← hG k, Measure.map_apply (hX k) hB]
  rw [hlaw] at hmul
  exact hmul

/-- Survival events and the natural-valued length agree off the null infinite set. -/
theorem measure_nativeRestart_survival_eq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (x : ℝ) (k : ℕ) :
    μ {ω | ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω} =
      μ {ω | k < nativeRestartLengthNat X E x ω} := by
  apply measure_congr
  filter_upwards [nativeRestartLength_ae_finite hX hi hG hE x] with ω hfin
  have hcast := nativeRestartLengthNat_cast_of_finite X E x ω hfin
  refine propext ⟨fun hω => ?_, fun hω => ?_⟩
  · have hω' : ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω := hω
    show k < nativeRestartLengthNat X E x ω
    rw [← hcast] at hω'
    have hle : k+1 ≤ nativeRestartLengthNat X E x ω := WithTop.coe_le_coe.mp hω'
    omega
  · have hω' : k < nativeRestartLengthNat X E x ω := hω
    show ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω
    rw [← hcast]
    exact WithTop.coe_le_coe.mpr (by omega : k+1 ≤ nativeRestartLengthNat X E x ω)

/-- Equation `eq:stationaryrawtail`: the selected rejection increment has the mean
segment length as its only extra factor. -/
theorem measureReal_nativeRestart_selected_increment_tail
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X (nativeRestartLengthNat X E x ω-1) ω|} ≤
      nativeRestartMean X μ E x*(2*Real.exp (-t^2/2)) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set B : Set ℝ := {y : ℝ | t ≤ |y|} with hBdef
  have hBm : MeasurableSet B := measurableSet_le measurable_const measurable_id.abs
  set A : ℕ → Set Ω := fun k => {ω | ((k+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω}
    with hAdef
  have hmeanpos : 0 ≤ nativeRestartMean X μ E x := by
    have hb := nativeRestartMean_bounds hX hi hG hE x
    linarith [hb.1]
  have hcov : {ω | t ≤ |X (nativeRestartLengthNat X E x ω-1) ω|} ≤ᵐ[μ]
      ⋃ k, (A k ∩ (X k) ⁻¹' B) := by
    filter_upwards [nativeRestartLength_ae_finite hX hi hG hE x] with ω hfin hω
    have hpos := nativeRestartLengthNat_pos_of_finite X hE.le x ω hfin
    refine mem_iUnion.mpr ⟨nativeRestartLengthNat X E x ω-1, ?_, hω⟩
    show ((nativeRestartLengthNat X E x ω-1+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength X E x ω
    rw [Nat.sub_add_cancel hpos, nativeRestartLengthNat_cast_of_finite X E x ω hfin]
  have hterm : ∀ k, μ (A k ∩ (X k) ⁻¹' B) = μ (A k)*gaussianReal 0 1 B :=
    fun k => measure_nativeRestart_survival_inter hX hi hG E x k hBm
  have hNint := nativeRestartLengthNat_integrable hX hi hG hE x
  have hNmeas : Measurable (nativeRestartLengthNat X E x) :=
    nativeRestartLengthNat_measurable X hX E |>.comp ((measurable_const (a := x)).prodMk measurable_id)
  have hpartial : ∀ n : ℕ, (∑ k ∈ Finset.range n, μ (A k)) ≤
      ENNReal.ofReal (nativeRestartMean X μ E x) := by
    intro n
    have hreal := sum_tail_le_integral_natCast (μ := μ) hNmeas hNint n
    have hcast : (∑ k ∈ Finset.range n, μ (A k)) =
        ENNReal.ofReal (∑ k ∈ Finset.range n, μ.real {ω | k < nativeRestartLengthNat X E x ω}) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => measureReal_nonneg)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [measure_nativeRestart_survival_eq hX hi hG hE x k, Measure.real,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hreal
  have htsum : (∑' k, μ (A k)) ≤ ENNReal.ofReal (nativeRestartMean X μ E x) := by
    rw [ENNReal.tsum_eq_iSup_nat]
    exact iSup_le hpartial
  have hgauss : gaussianReal 0 1 B ≤ ENNReal.ofReal (2*Real.exp (-t^2/2)) := by
    have hb := gaussianReal_absolute_tail_bound 1 ht
    simp only [NNReal.coe_one, mul_one] at hb
    calc
      gaussianReal 0 1 B = ENNReal.ofReal ((gaussianReal 0 1).real B) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb
  have hchain : μ {ω | t ≤ |X (nativeRestartLengthNat X E x ω-1) ω|} ≤
      ENNReal.ofReal (nativeRestartMean X μ E x*(2*Real.exp (-t^2/2))) := by
    calc
      μ {ω | t ≤ |X (nativeRestartLengthNat X E x ω-1) ω|} ≤ μ (⋃ k, (A k ∩ (X k) ⁻¹' B)) :=
        measure_mono_ae hcov
      _ ≤ ∑' k, μ (A k ∩ (X k) ⁻¹' B) := measure_iUnion_le _
      _ = ∑' k, μ (A k)*gaussianReal 0 1 B := by
        exact tsum_congr fun k => hterm k
      _ = (∑' k, μ (A k))*gaussianReal 0 1 B := ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal (nativeRestartMean X μ E x)*ENNReal.ofReal (2*Real.exp (-t^2/2)) :=
        mul_le_mul' htsum hgauss
      _ = ENNReal.ofReal (nativeRestartMean X μ E x*(2*Real.exp (-t^2/2))) :=
        (ENNReal.ofReal_mul hmeanpos).symm
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain
  rwa [ENNReal.toReal_ofReal (by positivity)] at h

end SwingRepair
