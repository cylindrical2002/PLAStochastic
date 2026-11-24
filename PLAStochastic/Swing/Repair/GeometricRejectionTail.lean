import PLAStochastic.Swing.Repair.FirstRejectionStopping
import PLAStochastic.ForMathlib.Probability.Moments.NatGeometricEvenTail
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Geometric rejection tails from independent increment pairs

An accepted prefix bounds the difference of each pair of consecutive increments
by twice the final tolerance. Disjoint future pairs therefore give a geometric
tail for the actual repair rejection. The probability of staying in the pair
bound is computed from the original increment law, not from a restart assumption.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace SwingRepair

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
variable {X : ℕ → Ω → ℝ}

/-- A fresh increment pair separates from the current survival event. -/
theorem repair_pair_survival_factor (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (ε : ℝ) (k : ℕ) :
    μ ({ω | (2 * k : WithTop ℕ) < firstRepairReject X ε ω} ∩
      {ω | |X (2 * k + 2) ω - X (2 * k + 1) ω| ≤ 2 * ε}) =
      μ {ω | (2 * k : WithTop ℕ) < firstRepairReject X ε ω} *
        μ {ω | |X 1 ω - X 0 ω| ≤ 2 * ε} := by
  let B : Set (Fin 2 → ℝ) := {v | |v 1 - v 0| ≤ 2 * ε}
  have hB : MeasurableSet B :=
    measurableSet_le ((measurable_pi_apply 1).sub (measurable_pi_apply 0)).abs measurable_const
  have hA := (firstRepairReject_isStoppingTime hX ε).measurableSet_gt (2 * k)
  have hpre : MeasurableSet[MeasurableSpace.comap
      (fun ω (j : Fin 2) => X (2 * k + 1 + j.val) ω) inferInstance]
      ((fun ω (j : Fin 2) => X (2 * k + 1 + j.val) ω) ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := (Indep_iff _ _ μ).mp (futureBlock_indep_incrementFiltration hX hi (2 * k) 2)
    _ _ hpre hA
  rw [(futureBlock_identDistrib hX hi hid (2 * k) 2).measure_mem_eq hB] at h
  simpa [B, Set.preimage, Nat.add_assoc, Set.inter_comm, mul_comm] using h

/-- Surviving one more independent pair costs its original stay probability. -/
theorem firstRepairReject_survival_step (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    μ {ω | (2 * (k + 1) : WithTop ℕ) < firstRepairReject X ε ω} ≤
      μ {ω | (2 * k : WithTop ℕ) < firstRepairReject X ε ω} *
        μ {ω | |X 1 ω - X 0 ω| ≤ 2 * ε} := by
  rw [← repair_pair_survival_factor hX hi hid ε k]
  apply measure_mono
  intro ω hω
  have hkk : (2 * k : WithTop ℕ) ≤ 2 * (k + 1) := by
    exact_mod_cast (show 2 * k ≤ 2 * (k + 1) by omega)
  refine ⟨lt_of_le_of_lt hkk hω, ?_⟩
  by_contra hnot
  have hstop := firstRepairReject_le_of_increment_difference X hε ω (2 * k + 1)
    (by simpa [Nat.add_assoc] using (lt_of_not_ge hnot))
  have heq : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
  exact (not_le_of_gt hω) (by simpa only [heq, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat] using hstop)

/-- A geometric tail bound for the actual rejection index, using only the original iid sequence. -/
theorem firstRepairReject_survival_le_pow [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    μ {ω | (2 * k : WithTop ℕ) < firstRepairReject X ε ω} ≤
      (μ {ω | |X 1 ω - X 0 ω| ≤ 2 * ε}) ^ k := by
  induction k with
  | zero => simpa using (prob_le_one (μ := μ)
      (s := {ω | (0 : WithTop ℕ) < firstRepairReject X ε ω}))
  | succ k ih =>
    exact (firstRepairReject_survival_step hX hi hid hε k).trans
      (by simpa [pow_succ] using (mul_le_mul_left ih
        (μ {ω | |X 1 ω - X 0 ω| ≤ 2 * ε})))

/-- Positive probability of pair escape implies that the actual rejection is almost surely finite. -/
theorem firstRepairReject_ae_finite_of_pairStay_lt_one [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) {ε : ℝ} (hε : 0 ≤ ε)
    (hq : μ {ω | |X 1 ω - X 0 ω| ≤ 2 * ε} < 1) :
    ∀ᵐ ω ∂μ, firstRepairReject X ε ω ≠ ⊤ := by
  have hzero : μ {ω | firstRepairReject X ε ω = ⊤} = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
    intro k
    apply le_trans _ (firstRepairReject_survival_le_pow hX hi hid hε k)
    apply measure_mono
    intro ω hω
    change firstRepairReject X ε ω = ⊤ at hω
    change (2 * k : WithTop ℕ) < firstRepairReject X ε ω
    rw [hω]
    exact WithTop.coe_lt_top (2 * k)
  simpa only [ae_iff, not_not] using hzero

/-- Standard normal marginals give every pair a strictly positive escape probability. -/
theorem gaussian_pairStay_lt_one [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (ε : ℝ) :
    μ {ω | |X 1 ω - X 0 ω| ≤ 2 * ε} < 1 := by
  have hleft : 0 < μ (X 0 ⁻¹' Set.Iio 0) := by
    rw [← Measure.map_apply (hX 0) measurableSet_Iio, hG 0]
    apply pos_iff_ne_zero.mpr
    intro hz
    have hv := gaussianReal_absolutelyContinuous' 0 (show (1 : ℝ≥0) ≠ 0 by norm_num) hz
    exact ENNReal.top_ne_zero (by simpa only [Real.volume_Iio] using hv)
  have hright : 0 < μ (X 1 ⁻¹' Set.Ioi (2 * ε)) := by
    rw [← Measure.map_apply (hX 1) measurableSet_Ioi, hG 1]
    apply pos_iff_ne_zero.mpr
    intro hz
    have hv := gaussianReal_absolutelyContinuous' 0 (show (1 : ℝ≥0) ≠ 0 by norm_num) hz
    exact ENNReal.top_ne_zero (by simpa only [Real.volume_Ioi] using hv)
  have hpair : 0 < μ (X 0 ⁻¹' Set.Iio 0 ∩ X 1 ⁻¹' Set.Ioi (2 * ε)) := by
    rw [(hi.indepFun (show (0 : ℕ) ≠ 1 by decide)).measure_inter_preimage_eq_mul
      _ _ measurableSet_Iio measurableSet_Ioi]
    exact ENNReal.mul_pos hleft.ne' hright.ne'
  let S : Set Ω := {ω | |X 1 ω - X 0 ω| ≤ 2 * ε}
  have hS : MeasurableSet S :=
    measurableSet_le ((hX 1).sub (hX 0)).abs measurable_const
  have hsub : X 0 ⁻¹' Set.Iio 0 ∩ X 1 ⁻¹' Set.Ioi (2 * ε) ⊆ Sᶜ := by
    intro ω ⟨h₀, h₁⟩ hω
    have ha := le_abs_self (X 1 ω - X 0 ω)
    change X 0 ω < 0 at h₀
    change 2 * ε < X 1 ω at h₁
    change |X 1 ω - X 0 ω| ≤ 2 * ε at hω
    linarith
  have hcomp : 0 < μ Sᶜ := hpair.trans_le (measure_mono hsub)
  change μ S < 1
  by_contra! hnot
  have hμS : μ S = 1 := le_antisymm prob_le_one hnot
  have hzero : μ Sᶜ = 0 := by
    rw [measure_compl hS (measure_ne_top μ S), measure_univ, hμS]
    simp
  exact hcomp.ne' hzero

/-- Equal Gaussian laws supply the identical-distribution hypothesis used by restart. -/
theorem gaussianIncrements_identDistrib (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    IdentDistrib (X n) (X 0) μ μ :=
  ⟨(hX n).aemeasurable, (hX 0).aemeasurable, (hG n).trans (hG 0).symm⟩

/-- For actual iid standard normal increments, the actual first cone rejection is a.s. finite. -/
theorem firstRepairReject_ae_finite_gaussian [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ ω ∂μ, firstRepairReject X ε ω ≠ ⊤ :=
  firstRepairReject_ae_finite_of_pairStay_lt_one hX hi (gaussianIncrements_identDistrib hX hG)
    hε (gaussian_pairStay_lt_one hX hi hG ε)

/-- Actual Gaussian repair rejection leaves each finite future block with the original joint law. -/
theorem firstRepairReject_gaussian_block_identDistrib [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {ε : ℝ} (hε : 0 ≤ ε) (r : ℕ) :
    IdentDistrib (fun ω (j : Fin r) => X ((firstRepairReject X ε ω).untopD 0 + 1 + j.val) ω)
      (fun ω (j : Fin r) => X j.val ω) μ μ :=
  firstRepairReject_block_identDistrib hX hi (gaussianIncrements_identDistrib hX hG) ε
    (firstRepairReject_ae_finite_gaussian hX hi hG hε) r

/-- Actual Gaussian repair rejection leaves each finite future block independent of the past. -/
theorem firstRepairReject_gaussian_block_indep [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {ε : ℝ} (hε : 0 ≤ ε) (r : ℕ) :
    Indep (MeasurableSpace.comap
      (fun ω (j : Fin r) => X ((firstRepairReject X ε ω).untopD 0 + 1 + j.val) ω) inferInstance)
      (firstRepairReject_isStoppingTime hX ε).measurableSpace μ :=
  firstRepairReject_block_indep hX hi (gaussianIncrements_identDistrib hX hG) ε
    (firstRepairReject_ae_finite_gaussian hX hi hG hε) r

/-- The paper's rejected sample index / cycle span J = K + 1, defaulting to 1 at infinity. -/
def firstRepairSpan (X : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) : ℕ :=
  (firstRepairReject X ε ω).untopD 0 + 1

/-- The actual first-cycle span is measurable as a function of the input increments. -/
theorem firstRepairSpan_measurable (hX : ∀ n, Measurable (X n)) (ε : ℝ) :
    Measurable (firstRepairSpan X ε) :=
  ((firstRepairReject_isStoppingTime hX ε).measurable'.untopD 0).add_const 1

omit mΩ in
/-- On each finite rejection fiber the paper's span is exactly the sample index K + 1. -/
theorem firstRepairSpan_eq_of_reject (X : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) (n : ℕ)
    (hn : firstRepairReject X ε ω = (n : WithTop ℕ)) :
    firstRepairSpan X ε ω = n + 1 := by
  unfold firstRepairSpan
  rw [hn]
  rfl

/-- The finite-value convention only defines the variable; original survival events control its tails. -/
theorem firstRepairReject_untop_survival_le_pow [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    μ {ω | 2 * k < (firstRepairReject X ε ω).untopD 0} ≤
      (μ {ω | |X 1 ω - X 0 ω| ≤ 2 * ε}) ^ k := by
  apply le_trans _ (firstRepairReject_survival_le_pow hX hi hid hε k)
  apply measure_mono
  intro ω hω
  change 2 * k < (firstRepairReject X ε ω).untopD 0 at hω
  change (2 * k : WithTop ℕ) < firstRepairReject X ε ω
  by_cases ht : firstRepairReject X ε ω = ⊤
  · simp [ht] at hω
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ht
    have hindex : (firstRepairReject X ε ω).untopD 0 = n := by rw [← hn]; rfl
    rw [hindex] at hω
    rw [← hn]
    exact WithTop.coe_lt_coe.mpr hω

/-- The actual rejection index is integrable under the independent-pair escape condition. -/
theorem firstRepairReject_integrable_of_pairStay_lt_one [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) {ε : ℝ} (hε : 0 ≤ ε)
    (hq : μ {ω | |X 1 ω - X 0 ω| ≤ 2 * ε} < 1) :
    Integrable (fun ω => (((firstRepairReject X ε ω).untopD 0 : ℕ) : ℝ)) μ :=
  integrable_natCast_of_geometric_even_tail
    ((firstRepairReject_isStoppingTime hX ε).measurable'.untopD 0) hq
    (firstRepairReject_untop_survival_le_pow hX hi hid hε)

/-- The actual Gaussian repair cycle span has finite mean. -/
theorem firstRepairSpan_integrable_gaussian [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {ε : ℝ} (hε : 0 ≤ ε) :
    Integrable (fun ω => (firstRepairSpan X ε ω : ℝ)) μ := by
  have hI := firstRepairReject_integrable_of_pairStay_lt_one hX hi
    (gaussianIncrements_identDistrib hX hG) hε (gaussian_pairStay_lt_one hX hi hG ε)
  simpa [firstRepairSpan, Nat.cast_add, Nat.cast_one] using hI.add (integrable_const (1 : ℝ))

/-- In particular the mean cycle span used in renewal inversion has a positive denominator. -/
theorem one_le_integral_firstRepairSpan_gaussian [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {ε : ℝ} (hε : 0 ≤ ε) :
    1 ≤ ∫ ω, (firstRepairSpan X ε ω : ℝ) ∂μ := by
  have h := integral_mono (integrable_const (1 : ℝ))
    (firstRepairSpan_integrable_gaussian hX hi hG hε)
    (show (fun _ω : Ω => (1 : ℝ)) ≤ (fun ω => (firstRepairSpan X ε ω : ℝ)) from
      fun ω => by simp [firstRepairSpan])
  simpa using h

end SwingRepair
