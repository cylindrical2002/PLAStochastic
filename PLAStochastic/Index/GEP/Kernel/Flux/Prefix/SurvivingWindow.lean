import PLAStochastic.Index.GEP.Kernel.Flux.Prefix.OneGapPrimitive

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset

/-- A predetermined surviving window avoiding the inserted coordinate. -/
def fluxWindow (eps : ℝ) (k i : ℕ) : Set (ℕ → ℝ) :=
  if k - 1 - i ≤ i then {g | (i : ℕ∞) < gapSegLen eps g}
  else {g | ((k - 1 - i : ℕ) : ℕ∞) < gapSegLen eps (fun s => g (i + 1 + s))}

theorem measurableSet_fluxWindow (eps : ℝ) (k i : ℕ) :
    MeasurableSet (fluxWindow eps k i) := by
  unfold fluxWindow
  split
  · exact measurableSet_lt_gapSegLen eps i
  · exact (measurableSet_lt_gapSegLen eps (k - 1 - i)).preimage (measurable_shiftGap (i + 1))

theorem flux_survival_subset_window {eps x : ℝ} {k i : ℕ} (hi : i < k) :
    {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)} ⊆ fluxWindow eps k i := by
  intro g hg
  unfold fluxWindow
  split
  · exact pw_left_of_lt hi hg
  · exact pw_window_of_lt hi hg

/-- The derivative of the actual one-gap survival probability has exponentially
small total mass whenever the predetermined unmarked window is unlikely. -/
theorem flux_pwQ_window_primitive {ν : ProbabilityMeasure ℝ}
    (hac : (ν : Measure ℝ) ≪ volume) (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    (eps : ℝ) {k i : ℕ} (hk : 2 ≤ k) (hi : i < k) :
    ∃ j : ℝ → ℝ, AEPrimitive (pwQ eps ν k i) j ∧ Integrable j ∧
      (∫ x, ‖j x‖) ≤ 2 * (iidLaw ν).real (fluxWindow eps k i) := by
  let S := fluxWindow eps k i
  let P := (iidLaw ν).restrict S
  obtain ⟨j, hj, hiJ, hb⟩ := flux_prefix_measure_aePrimitive hac hpos P
    Measure.absolutelyContinuous_restrict eps hk hi
  have he : (fun x => P.real {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}) =
      pwQ eps ν k i := by
    funext x
    have hm : MeasurableSet {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)} :=
      (measurableSet_lt_gapSegLen eps k).preimage
        ((measurable_update_pair i).comp (measurable_const.prodMk measurable_id))
    rw [show P = (iidLaw ν).restrict S from rfl, measureReal_restrict_apply hm]
    rw [inter_eq_left.mpr (flux_survival_subset_window hi)]
    rfl
  rw [he] at hj
  rw [show P = (iidLaw ν).restrict S from rfl, measureReal_restrict_apply_univ] at hb
  exact ⟨j, hj, hiJ, hb⟩

/-- The window mass has the same summable geometric majorant as `pwQ`, uniformly
in the inserted value. It therefore also bounds the whole derivative mass. -/
theorem fluxWindow_le {ν : ProbabilityMeasure ℝ} {eps q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (htail : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m)) {i k : ℕ} (hi : i < k) :
    (iidLaw ν).real (fluxWindow eps k i) ≤ 72 / 71 * q ^ (2 * (k - 1)) := by
  have hmono : ∀ {m n : ℕ}, n ≤ m → 72 / 71 * q ^ m ≤ 72 / 71 * q ^ n := fun hnm =>
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 hnm) (by norm_num)
  unfold fluxWindow
  split_ifs with h
  · refine (ENNReal.toReal_le_of_le_ofReal (by positivity) (htail i)).trans ?_
    rw [← pow_mul]
    exact hmono (by omega)

  · rw [Measure.real, measure_lt_gapSegLen_shift]
    refine (ENNReal.toReal_le_of_le_ofReal (by positivity) (htail (k - 1 - i))).trans ?_
    rw [← pow_mul]
    exact hmono (by omega)

/-- At the first gap, a constant line already fits both keys when `eps ≥ 1`. -/
theorem flux_pwQ_one {eps : ℝ} (heps : 1 ≤ eps) (ν : ProbabilityMeasure ℝ) (x : ℝ) :
    pwQ eps ν 1 0 x = 1 := by
  have he : {g : ℕ → ℝ | ((1 : ℕ) : ℕ∞) < gapSegLen eps (Function.update g 0 x)} = univ := by
    apply Set.eq_univ_of_forall
    intro g
    change ((1 : ℕ) : ℕ∞) < gapSegLen eps (Function.update g 0 x)
    rw [gapSegLen, lt_segLen_iff]
    refine ⟨0, 1, fun j hj => ?_⟩
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · simpa only [Nat.cast_zero, zero_mul, zero_add, zero_sub, abs_neg, abs_one] using heps
    · simpa only [Nat.cast_one, zero_mul, zero_add, sub_self, abs_zero] using
        (by linarith : (0 : ℝ) ≤ eps)
  rw [pwQ, he]
  simp [Measure.real]

/-- Uniform derivative-mass control, now including all finite prefixes. -/
theorem flux_pwQ_window_primitive_all {ν : ProbabilityMeasure ℝ}
    (hac : (ν : Measure ℝ) ≪ volume) (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    {eps : ℝ} (heps : 1 ≤ eps) {k i : ℕ} (hi : i < k) :
    ∃ j : ℝ → ℝ, AEPrimitive (pwQ eps ν k i) j ∧ Integrable j ∧
      (∫ x, ‖j x‖) ≤ 2 * (iidLaw ν).real (fluxWindow eps k i) := by
  by_cases hk : 2 ≤ k
  · exact flux_pwQ_window_primitive hac hpos eps hk hi
  · have hk1 : k = 1 := by omega
    have hi0 : i = 0 := by omega
    subst k i
    refine ⟨fun _ => 0, ⟨fun R => (integrable_zero _ _ _).intervalIntegrable, 1, ?_⟩,
      integrable_zero _ _ _, ?_⟩
    · exact Eventually.of_forall fun x => by simp [flux_pwQ_one heps ν x]
    · simpa only [norm_zero, integral_zero] using
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (measureReal_nonneg (μ := iidLaw ν) (s := fluxWindow eps 1 0))

end

end PGM
