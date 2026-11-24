import PLAStochastic.Swing.Ladder.Drift.JointMeasurability

/-! # The ladder-height law as a measurable family in the drift

The drift dependence of the ladder tail and of the ladder mean is what turns
`eq:equilibriumovershoot` into a probability kernel.  The tail is also bounded
below by the one-step crossing probability, which is the only positivity input
needed later.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The drift-indexed ladder tail is jointly measurable in the drift and the level. -/
theorem gaussianAscendingLadderLaw_tail_joint_measurable [SFinite μ]
    (hX : ∀ n, Measurable (X n)) :
    Measurable (fun q : ℝ × ℝ => gaussianAscendingLadderLaw X μ q.1 (Ioi q.2)) := by
  have hH := gaussianAscendingLadderHeight_joint_measurable (X := X) hX
  have hproj : Measurable (fun z : (ℝ × ℝ) × Ω => ((z.1.1 : ℝ), z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hHz : Measurable
      (fun z : (ℝ × ℝ) × Ω => gaussianAscendingLadderHeight X z.1.1 z.2) := hH.comp hproj
  have hset : MeasurableSet
      {z : (ℝ × ℝ) × Ω | z.1.2 < gaussianAscendingLadderHeight X z.1.1 z.2} :=
    measurableSet_lt (measurable_snd.comp measurable_fst) hHz
  have hF : Measurable (fun z : (ℝ × ℝ) × Ω =>
      Set.indicator {z : (ℝ × ℝ) × Ω | z.1.2 < gaussianAscendingLadderHeight X z.1.1 z.2}
        (fun _ => (1 : ℝ≥0∞)) z) := (measurable_const (a := (1 : ℝ≥0∞))).indicator hset
  have heq : (fun q : ℝ × ℝ => gaussianAscendingLadderLaw X μ q.1 (Ioi q.2)) =
      fun q : ℝ × ℝ => ∫⁻ ω,
        Set.indicator {z : (ℝ × ℝ) × Ω | z.1.2 < gaussianAscendingLadderHeight X z.1.1 z.2}
          (fun _ => (1 : ℝ≥0∞)) (q, ω) ∂μ := by
    funext q
    rw [gaussianAscendingLadderLaw,
      Measure.map_apply (gaussianAscendingLadderHeight_measurable hX q.1) measurableSet_Ioi]
    rw [← lintegral_indicator_one
      ((gaussianAscendingLadderHeight_measurable hX q.1) measurableSet_Ioi)]
    rfl
  rw [heq]
  exact hF.lintegral_prod_right'

/-- The ladder mean is measurable in the drift. -/
theorem gaussianAscendingLadderLaw_mean_measurable [SFinite μ]
    (hX : ∀ n, Measurable (X n)) :
    Measurable (fun a : ℝ => ladderMeanENN (gaussianAscendingLadderLaw X μ a)) := by
  have hH := gaussianAscendingLadderHeight_joint_measurable (X := X) hX
  have heq : (fun a : ℝ => ladderMeanENN (gaussianAscendingLadderLaw X μ a)) =
      fun a : ℝ => ∫⁻ ω, ENNReal.ofReal (gaussianAscendingLadderHeight X a ω) ∂μ := by
    funext a
    rw [ladderMeanENN, gaussianAscendingLadderLaw,
      lintegral_map ENNReal.measurable_ofReal (gaussianAscendingLadderHeight_measurable hX a)]
  rw [heq]
  exact (ENNReal.measurable_ofReal.comp hH).lintegral_prod_right'

/-! ### The one-step crossing lower bound -/

omit [MeasurableSpace Ω] in
/-- If the drifted walk is already above a nonnegative level at index one, the
ladder time is one and the ladder height is that value. -/
theorem gaussianAscendingLadderHeight_eq_of_first_step {a o : ℝ} (ho : 0 ≤ o) {ω : Ω}
    (hω : o < gaussianDriftWalk X 0 a 1 ω) :
    gaussianAscendingLadderTime X a ω = (1 : ℕ) ∧
      gaussianAscendingLadderHeight X a ω = gaussianDriftWalk X 0 a 1 ω := by
  have hpos : gaussianDriftWalk X 0 a 1 ω ∈ Ioi (0 : ℝ) := by
    simp only [mem_Ioi]
    linarith
  have hle : gaussianAscendingLadderTime X a ω ≤ ((1 : ℕ) : WithTop ℕ) := by
    rw [gaussianAscendingLadderTime_eq_hittingAfter]
    exact hittingAfter_le_of_mem (Nat.zero_le 1) hpos
  have hge : ((1 : ℕ) : WithTop ℕ) ≤ gaussianAscendingLadderTime X a ω := by
    have h0 := gaussianAscendingLadderTime_pos (X := X) a ω
    exact Order.succ_le_of_lt h0
  have hT : gaussianAscendingLadderTime X a ω = ((1 : ℕ) : WithTop ℕ) := le_antisymm hle hge
  refine ⟨hT, ?_⟩
  have hne : gaussianAscendingLadderTime X a ω ≠ ⊤ := by
    rw [hT]
    exact WithTop.coe_ne_top
  rw [gaussianAscendingLadderHeight_eq_position hne, hT]
  rfl

omit [MeasurableSpace Ω] in
theorem gaussianDriftWalk_one (a : ℝ) (ω : Ω) :
    gaussianDriftWalk X 0 a 1 ω = X 0 ω + a := by
  simp [gaussianDriftWalk, cumulativeSamples]

/-- The ladder tail is strictly positive at every nonnegative level and every
drift: the walk can already cross on its first step. -/
theorem gaussianAscendingLadderLaw_tail_pos
    (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a o : ℝ} (ho : 0 ≤ o) :
    0 < gaussianAscendingLadderLaw X μ a (Ioi o) := by
  have hsub : {ω : Ω | o - a < X 0 ω} ⊆
      (gaussianAscendingLadderHeight X a) ⁻¹' (Ioi o) := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    have hstep : o < gaussianDriftWalk X 0 a 1 ω := by
      rw [gaussianDriftWalk_one]
      linarith
    have := (gaussianAscendingLadderHeight_eq_of_first_step ho hstep).2
    simp only [mem_preimage, mem_Ioi]
    rw [this]
    exact hstep
  have hmeas : MeasurableSet {ω : Ω | o - a < X 0 ω} :=
    measurableSet_lt measurable_const (hX 0)
  have hpos : 0 < μ {ω : Ω | o - a < X 0 ω} := by
    have : μ {ω : Ω | o - a < X 0 ω} = gaussianReal 0 1 (Ioi (o - a)) := by
      rw [← hG 0, Measure.map_apply (hX 0) measurableSet_Ioi]
      rfl
    rw [this]
    exact gaussianReal_Ioi_pos _
  rw [gaussianAscendingLadderLaw,
    Measure.map_apply (gaussianAscendingLadderHeight_measurable hX a) measurableSet_Ioi]
  exact lt_of_lt_of_le hpos (measure_mono hsub)

/-! ### The equilibrium overshoot law at a positive drift -/

theorem gaussianAscendingLadderLaw_nonneg_ae (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    0 ≤ᵐ[gaussianAscendingLadderLaw X μ a] fun x : ℝ => x := by
  have hmeas : Measurable (gaussianAscendingLadderHeight X a) :=
    gaussianAscendingLadderHeight_measurable hX a
  rw [Filter.EventuallyLE, ae_iff]
  have hset : {x : ℝ | ¬ (0 : ℝ) ≤ x} = {x : ℝ | x < 0} := by
    ext x
    simp
  have hmsIio : MeasurableSet {x : ℝ | x < 0} := by
    have h : {x : ℝ | x < 0} = Iio (0 : ℝ) := by ext x; simp
    rw [h]
    exact measurableSet_Iio
  have hpre : (gaussianAscendingLadderHeight X a) ⁻¹' {x : ℝ | x < 0} = (∅ : Set Ω) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact gaussianAscendingLadderHeight_nonneg (X := X) a ω
  show gaussianAscendingLadderLaw X μ a {x : ℝ | ¬ (0 : ℝ) ≤ x} = 0
  rw [hset, show gaussianAscendingLadderLaw X μ a =
    μ.map (gaussianAscendingLadderHeight X a) from rfl,
    Measure.map_apply hmeas hmsIio, hpre, measure_empty]

/-- The equilibrium overshoot law is a probability measure at every positive
drift; the compact-interval statement is instantiated at the single point. -/
theorem gaussianAscendingLadderEquilibrium_isProbability
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure
      (equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a)) :=
  gaussianAscendingLadderEquilibrium_isProbabilityMeasure hX hi hG ha le_rfl le_rfl

end SwingRepair
