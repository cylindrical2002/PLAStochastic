import PLAStochastic.Index.GEP.StrongApprox.Coupling.BlockLaws

/-! # Measurable bad events and block union bounds -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- A centered walk exceeds `x` before time `n`. -/
def saWalkBad (n : ℕ) (c x : ℝ) : Set (ℕ → ℝ) :=
  {z | ∃ k ≤ n, x < |gapKeys z k - c * k|}

theorem measurableSet_saWalkBad (n : ℕ) (c x : ℝ) : MeasurableSet (saWalkBad n c x) := by
  have he : saWalkBad n c x = ⋃ k, ⋃ (_ : k ≤ n), {z | x < |gapKeys z k - c * k|} := by
    ext z
    simp [saWalkBad]
  rw [he]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
    measurableSet_lt measurable_const ((measurable_gapKeys_apply k).sub_const _).abs

/-- A centered within-block increment exceeds `x` in one of the first `L+1` blocks. -/
def saBlocksBad (m L : ℕ) (c x : ℝ) : Set (ℕ → ℝ) :=
  {z | ∃ j ≤ L, ∃ k ≤ m, x < |gapKeys z (j * m + k) - gapKeys z (j * m) - c * k|}

theorem saBlocksBad_eq_union (m L : ℕ) (c x : ℝ) :
    saBlocksBad m L c x = ⋃ j ∈ Finset.range (L + 1),
      (fun z i => z (j * m + i)) ⁻¹' saWalkBad m c x := by
  ext z
  simp [saBlocksBad, saWalkBad, gapKeys_shift]

theorem measurableSet_saBlocksBad (m L : ℕ) (c x : ℝ) : MeasurableSet (saBlocksBad m L c x) := by
  rw [saBlocksBad_eq_union]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
    (by fun_prop : Measurable (fun z : ℕ → ℝ => fun i => z (j * m + i)))
      (measurableSet_saWalkBad m c x)

/-- Stationarity and a finite union bound suffice; independence of the block events is unnecessary. -/
theorem saBlocksBad_measure_le (ν : ProbabilityMeasure ℝ) (m L : ℕ) (c x : ℝ) :
    (iidLaw ν).real (saBlocksBad m L c x) ≤
      (L + 1) * (iidLaw ν).real (saWalkBad m c x) := by
  rw [saBlocksBad_eq_union]
  refine (measureReal_biUnion_finset_le _ _).trans_eq ?_
  have he : ∀ j : ℕ, (iidLaw ν).real ((fun z i => z (j * m + i)) ⁻¹' saWalkBad m c x) =
      (iidLaw ν).real (saWalkBad m c x) := by
    intro j
    rw [← map_measureReal_apply (by fun_prop) (measurableSet_saWalkBad _ _ _), map_shift_iidLaw]
  simp_rw [he]
  simp

theorem saBlocksBad_source_bound {θ B : ℝ} (hθ : 0 < θ) {ν : ProbabilityMeasure ℝ}
    (hpos : (ν : Measure ℝ) (Iic 0) = 0) (hmean : lawMean ν = 1) (hexp : ExpMom θ B ν)
    {m : ℕ} (hm : 1 ≤ m) (L : ℕ) {x : ℝ} (hx : 0 < x) :
    (iidLaw ν).real (saBlocksBad m L 1 x) ≤
      (L + 1) * (2 * Real.exp (-(bernsteinRate θ B * min (x ^ 2 / m) x))) := by
  apply (saBlocksBad_measure_le ν m L 1 x).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [saWalkBad, one_mul] using iid_maximal_bernstein hθ hpos hmean hexp m hm hx

theorem saBlocksBad_gaussian_bound (m L : ℕ) {x : ℝ} (hx : 0 < x) :
    (iidLaw gaussPM).real (saBlocksBad m L 0 x) ≤
      (L + 1) * (2 * (m + 1) * Real.exp (-(x ^ 2 / (2 * m)))) := by
  apply (saBlocksBad_measure_le gaussPM m L 0 x).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [saWalkBad, zero_mul, sub_zero] using sa_gaussian_walk_max_tail m hx

/-- The bad event on a pair of finite leaf vectors. -/
def saLeafBad (L : ℕ) (a : ℝ) : Set ((Fin L → ℝ) × (Fin L → ℝ)) :=
  {q | ∃ k ≤ L, a < |vkeys q.1 k - vkeys q.2 k|}

theorem measurableSet_saLeafBad (L : ℕ) (a : ℝ) : MeasurableSet (saLeafBad L a) := by
  have he : saLeafBad L a = ⋃ k, ⋃ (_ : k ≤ L), {q | a < |vkeys q.1 k - vkeys q.2 k|} := by
    ext q
    simp [saLeafBad]
  rw [he]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_lt measurable_const
    (((measurable_pi_apply k).comp ((measurable_vkeys L).comp measurable_fst)).sub
      ((measurable_pi_apply k).comp ((measurable_vkeys L).comp measurable_snd))).abs

end

end PGM
