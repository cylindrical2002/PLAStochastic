import PLAStochastic.Swing.StationaryScale.StoppedSumTail

/-! # Wald's second-moment identity for a predictable guard family

A guarded walk adds the `k`-th fresh increment only on an event decided before
that increment.  Its square has the exact expectation `∑ P(S k)`: this is
Wald's second identity in the form needed for the stopped maximal bound of
Appendix `app:margins`, proved directly from independence rather than from a
martingale structure.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The walk that accumulates the `k`-th increment only on the guard `S k`. -/
def guardedWalk (X : ℕ → Ω → ℝ) (S : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, (S k).indicator (fun ω' => X k ω') ω

omit mΩ in
@[simp] theorem guardedWalk_zero (X : ℕ → Ω → ℝ) (S : ℕ → Set Ω) (ω : Ω) :
    guardedWalk X S 0 ω = 0 := by simp [guardedWalk]

omit mΩ in
theorem guardedWalk_succ (X : ℕ → Ω → ℝ) (S : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    guardedWalk X S (n+1) ω = guardedWalk X S n ω+(S n).indicator (fun ω' => X n ω') ω := by
  simp [guardedWalk, Finset.sum_range_succ]

omit mΩ in
theorem guardedWalk_measurable_history {S : ℕ → Set Ω}
    (hS : ∀ k, MeasurableSet[incrementIndexSpace X (Iio k)] (S k)) (n : ℕ) :
    Measurable[incrementIndexSpace X (Iio n)] (guardedWalk X S n) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Iio n)
  apply Finset.measurable_sum
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  have hSk : MeasurableSet[incrementIndexSpace X (Iio n)] (S k) :=
    incrementIndexSpace_mono (fun j hj => lt_trans (Set.mem_Iio.mp hj) hkn) _ (hS k)
  have hXk : Measurable[incrementIndexSpace X (Iio n)] (X k) :=
    incrementIndexSpace_eval (X := X) (Set.mem_Iio.mpr hkn)
  exact hXk.indicator hSk

omit mΩ in
/-- The guard indicator is itself decided before the increment it guards. -/
theorem guardIndicator_measurable_history {S : ℕ → Set Ω}
    (hS : ∀ k, MeasurableSet[incrementIndexSpace X (Iio k)] (S k)) (n : ℕ) :
    Measurable[incrementIndexSpace X (Iio n)]
      (fun ω => (S n).indicator (fun _ => (1 : ℝ)) ω) := by
  exact measurable_const.indicator (hS n)

/-! ## The two Gaussian moments used in the identity -/

theorem integral_gaussian_increment (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (∫ ω, X n ω ∂μ) = 0 := by
  have h := integral_map (φ := X n) (μ := μ) (hX n).aemeasurable
    (Measurable.aestronglyMeasurable (f := fun y : ℝ => y) measurable_id)
  rw [hG n] at h
  rw [← h]
  simp [integral_id_gaussianReal (μ := 0) (v := (1 : ℝ≥0))]

theorem integral_gaussian_increment_sq (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (∫ ω, (X n ω)^2 ∂μ) = 1 := by
  have h := integral_map (φ := X n) (μ := μ) (hX n).aemeasurable
    (Measurable.aestronglyMeasurable (f := fun y : ℝ => y^2) (measurable_id.pow_const 2))
  rw [hG n] at h
  rw [← h]
  have hv := variance_of_integral_eq_zero (X := (id : ℝ → ℝ))
    (μ := gaussianReal 0 (1 : ℝ≥0)) measurable_id.aemeasurable
    (by simpa only [id_eq] using integral_id_gaussianReal (μ := 0) (v := (1 : ℝ≥0)))
  simpa only [variance_id_gaussianReal, NNReal.coe_one, id_eq] using hv.symm

theorem integrable_gaussian_increment (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) : Integrable (X n) μ := by
  have hmap : Integrable (id : ℝ → ℝ) (μ.map (X n)) := by
    rw [hG n]
    exact (memLp_id_gaussianReal (μ := 0) (v := (1 : ℝ≥0)) 1).integrable (by norm_num)
  have h := (integrable_map_measure
    (Measurable.aestronglyMeasurable (f := (id : ℝ → ℝ)) measurable_id)
    (hX n).aemeasurable).mp hmap
  simpa only [Function.comp_def, id_eq] using h

theorem integrable_gaussian_increment_sq (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    Integrable (fun ω => (X n ω)^2) μ := by
  have hmap : Integrable (fun y : ℝ => y^2) (μ.map (X n)) := by
    rw [hG n]
    exact (memLp_id_gaussianReal (μ := 0) (v := (1 : ℝ≥0)) 2).integrable_sq
  exact (integrable_map_measure
    (Measurable.aestronglyMeasurable (f := fun y : ℝ => y^2) (measurable_id.pow_const 2))
    (hX n).aemeasurable).mp hmap

/-! ## The identity -/

theorem memLp_gaussian_increment (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) : MemLp (X n) 2 μ :=
  (memLp_two_iff_integrable_sq (hX n).aestronglyMeasurable).mpr
    (integrable_gaussian_increment_sq hX hG n)

omit mΩ in
theorem guardedWalk_eq_finsetSum (X : ℕ → Ω → ℝ) (S : ℕ → Set Ω) (n : ℕ) :
    guardedWalk X S n = ∑ k ∈ Finset.range n, (S k).indicator (X k) := by
  funext ω
  simp [guardedWalk, Finset.sum_apply]

theorem memLp_guardedWalk (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {S : ℕ → Set Ω}
    (hSamb : ∀ k, MeasurableSet (S k)) (n : ℕ) : MemLp (guardedWalk X S n) 2 μ := by
  rw [guardedWalk_eq_finsetSum]
  exact memLp_finsetSum' _ (fun k _ => MemLp.indicator (hSamb k) (memLp_gaussian_increment hX hG k))

omit mΩ in
theorem guardedWalk_indicator_mul (X : ℕ → Ω → ℝ) (S : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    (S n).indicator (fun ω' => X n ω') ω =
      (S n).indicator (fun _ => (1 : ℝ)) ω*X n ω := by
  by_cases h : ω ∈ S n
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

/-- Wald's second-moment identity for a predictable guard family. -/
theorem integral_guardedWalk_sq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {S : ℕ → Set Ω} (hS : ∀ k, MeasurableSet[incrementIndexSpace X (Iio k)] (S k)) (n : ℕ) :
    (∫ ω, (guardedWalk X S n ω)^2 ∂μ) = ∑ k ∈ Finset.range n, μ.real (S k) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hSamb : ∀ k, MeasurableSet (S k) := fun k => (incrementIndexSpace_le hX (Iio k)) _ (hS k)
  induction n with
  | zero => simp
  | succ n ih =>
    set ind : Ω → ℝ := fun ω => (S n).indicator (fun _ => (1 : ℝ)) ω with hindf
    set A : Ω → ℝ := fun ω => guardedWalk X S n ω*ind ω with hAf
    have hindm : Measurable ind := measurable_const.indicator (hSamb n)
    have hgm : Measurable (guardedWalk X S n) :=
      (guardedWalk_measurable_history hS n).mono (incrementIndexSpace_le hX _) le_rfl
    have hAm : Measurable A := hgm.mul hindm
    have hAeq : A = (S n).indicator (guardedWalk X S n) := by
      funext ω
      by_cases h : ω ∈ S n
      · rw [hAf, hindf]
        simp [Set.indicator_of_mem h]
      · rw [hAf, hindf]
        simp [Set.indicator_of_notMem h]
    have hAL2 : MemLp A 2 μ := by
      rw [hAeq]
      exact MemLp.indicator (hSamb n) (memLp_guardedWalk hX hG hSamb n)
    have hgL2 : MemLp (guardedWalk X S n) 2 μ := memLp_guardedWalk hX hG hSamb n
    have hXL2 : MemLp (X n) 2 μ := memLp_gaussian_increment hX hG n
    have hgsq : Integrable (fun ω => (guardedWalk X S n ω)^2) μ := hgL2.integrable_sq
    have hXsq : Integrable (fun ω => (X n ω)^2) μ := integrable_gaussian_increment_sq hX hG n
    have hAsq : Integrable (fun ω => (A ω)^2) μ := hAL2.integrable_sq
    have hcross : Integrable (fun ω => A ω*X n ω) μ := by
      refine Integrable.mono' ((hAsq.add hXsq).div_const 2) (hAm.mul (hX n)).aestronglyMeasurable ?_
      filter_upwards with ω
      dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_mul]
      have hsq1 : |A ω|^2 = (A ω)^2 := sq_abs _
      have hsq2 : |X n ω|^2 = (X n ω)^2 := sq_abs _
      nlinarith [sq_nonneg (|A ω|-|X n ω|), hsq1, hsq2]
    have hlast : Integrable (fun ω => ind ω*(X n ω)^2) μ := by
      refine Integrable.mono' hXsq (hindm.mul ((hX n).pow_const 2)).aestronglyMeasurable ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_mul]
      have hib : |ind ω| ≤ 1 := by
        rw [hindf]
        by_cases h : ω ∈ S n
        · simp [Set.indicator_of_mem h]
        · simp [Set.indicator_of_notMem h]
      have hs : |(X n ω)^2| = (X n ω)^2 := abs_of_nonneg (sq_nonneg _)
      rw [hs]
      calc |ind ω| * (X n ω)^2 ≤ 1 * (X n ω)^2 :=
            mul_le_mul_of_nonneg_right hib (sq_nonneg _)
        _ = (X n ω)^2 := one_mul _
    -- expand the square
    have hexp : ∀ ω, (guardedWalk X S (n+1) ω)^2 =
        (guardedWalk X S n ω)^2+2*(A ω*X n ω)+ind ω*(X n ω)^2 := by
      intro ω
      rw [guardedWalk_succ, guardedWalk_indicator_mul]
      have hi2 : ind ω*ind ω = ind ω := by
        rw [hindf]
        by_cases h : ω ∈ S n
        · simp [Set.indicator_of_mem h]
        · simp [Set.indicator_of_notMem h]
      rw [hAf]
      nlinarith [hi2]
    -- the cross term vanishes and the last term is the guard probability
    have hpair := (@iid_two_fresh_gaussians_of_history Ω Ω mΩ
      (incrementIndexSpace X (Iio n)) μ X hX hi hG n id measurable_id).1
    have hindep : @IndepFun Ω Ω ℝ mΩ (incrementIndexSpace X (Iio n)) Real.measurableSpace
        (fun w => w) (fun w => X n w) μ := by
      simpa only [Function.comp_def, id_eq] using hpair.comp measurable_id measurable_fst
    have hAhist : Measurable[incrementIndexSpace X (Iio n)] A :=
      (guardedWalk_measurable_history hS n).mul (guardIndicator_measurable_history hS n)
    have hindhist : Measurable[incrementIndexSpace X (Iio n)] ind :=
      guardIndicator_measurable_history hS n
    have hAind : IndepFun A (X n) μ := by
      simpa only [Function.comp_def, id_eq] using hindep.comp hAhist measurable_id
    have hindind : IndepFun ind (fun ω => (X n ω)^2) μ := by
      simpa only [Function.comp_def, id_eq] using hindep.comp hindhist (measurable_id.pow_const 2)
    have hcrossval : (∫ ω, A ω*X n ω ∂μ) = 0 := by
      have h := hAind.integral_mul_eq_mul_integral hAm.aestronglyMeasurable
        (hX n).aestronglyMeasurable
      simp only [Pi.mul_apply] at h
      rw [h, integral_gaussian_increment hX hG n, mul_zero]
    have hlastval : (∫ ω, ind ω*(X n ω)^2 ∂μ) = μ.real (S n) := by
      have h := hindind.integral_mul_eq_mul_integral hindm.aestronglyMeasurable
        ((hX n).pow_const 2).aestronglyMeasurable
      simp only [Pi.mul_apply] at h
      rw [h, integral_gaussian_increment_sq hX hG n, mul_one, hindf,
        integral_indicator_const _ (hSamb n), smul_eq_mul, mul_one]
    have e1 := integral_add (μ := μ)
      (f := fun ω => guardedWalk X S n ω^2+2*(A ω*X n ω))
      (g := fun ω => ind ω*(X n ω)^2) (hgsq.add (hcross.const_mul 2)) hlast
    have e2 := integral_add (μ := μ)
      (f := fun ω => guardedWalk X S n ω^2)
      (g := fun ω => 2*(A ω*X n ω)) hgsq (hcross.const_mul 2)
    rw [integral_congr_ae (Eventually.of_forall hexp), e1, e2, integral_const_mul, ih,
      hcrossval, hlastval, Finset.sum_range_succ]
    ring

end SwingRepair
