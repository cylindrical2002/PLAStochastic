import PLAStochastic.Swing.Ladder.ZeroDrift.AgeResidual

/-!
# The joint tail of the zero-drift age and residual (E15)

For an i.i.d. standard Gaussian sequence `X`, the zero-drift walk `W = cumulativeSamples X`
and `ν₀ = gaussianAscendingLadderLaw X μ 0`:

* the walk a.s. exceeds every level and a.s. visits no fixed nonzero level, so for `D > 0`
  both the age `U_D` and the residual `O_D` are a.s. strictly positive;
* for `0 ≤ u < D` and `o ≥ 0`,
  `P(U_D > u, O_D > o) = ∫_{[0,D-u]} ν₀((D+o-s,∞)) U₀(ds)`;
* consequently, by the key renewal theorem for the spread-out law `ν₀`, for all real `u, o`
  `P(U_D > u, O_D > o) → (∫_{u⁺+o⁺}^∞ ν₀((w,∞)) dw) / E H₀` as `D → ∞`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The zero-drift walk a.s. never visits a fixed level after time `0`. -/
theorem zeroDriftWalk_ne_ae (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (b : ℝ) :
    ∀ᵐ ω ∂μ, ∀ j : ℕ, 1 ≤ j → entrancePath X ω j ≠ b := by
  have := hi.isProbabilityMeasure
  filter_upwards [gaussianDriftWalk_nonzero_ae hX hi hG (-b) 0] with ω hω j hj heq
  apply hω j hj
  simp only [gaussianDriftWalk, zero_mul, add_zero]
  change -b + entrancePath X ω j = 0
  rw [heq]
  ring

/-- The zero-drift walk a.s. crosses every nonnegative level. -/
theorem zeroDriftCrossing_ne_top_ae (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, ∀ D : ℝ, 0 ≤ D → zeroDriftCrossing X D ω ≠ ⊤ := by
  have := hi.isProbabilityMeasure
  filter_upwards [gaussianZeroWalk_exists_gt_ae hX hi hG] with ω hω D hD htop
  obtain ⟨m, hm⟩ := hω D
  have hall := (levelCrossing_eq_top_iff _ _).mp htop
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · rw [cumulativeSamples_zero] at hm
    linarith
  · exact absurd (hall m hm0) (not_le.mpr hm)

/-- For `D > 0` the age and the residual are a.s. strictly positive. -/
theorem zeroDrift_age_residual_pos_ae (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {D : ℝ} (hD : 0 < D) :
    ∀ᵐ ω ∂μ, 0 < zeroDriftUndershoot X D ω ∧ 0 < zeroDriftOvershoot X D ω := by
  filter_upwards [zeroDriftCrossing_ne_top_ae hX hi hG, zeroDriftWalk_ne_ae hX hi hG D]
    with ω hcross hne
  exact ⟨levelUndershoot_pos (entrancePath_zero X ω) hD (hcross D hD.le) hne,
    levelOvershoot_pos (hcross D hD.le)⟩

/-- The residual of the zero-drift walk has the residual-life tail of `ν₀`. -/
theorem zeroDriftOvershoot_tail_eq (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    μ {ω | t < zeroDriftOvershoot X b ω} =
      renewalOvershootTail (gaussianAscendingLadderLaw X μ 0) b t := by
  have := hi.isProbabilityMeasure
  have hcong : {ω | t < zeroDriftOvershoot X b ω} =ᵐ[μ]
      {ω | t < gaussianWalkOvershoot X 0 b ω} := by
    filter_upwards [gaussianZeroWalk_exists_gt_ae hX hi hG] with ω hω
    refine propext ?_
    show t < zeroDriftOvershoot X b ω ↔ t < gaussianWalkOvershoot X 0 b ω
    rw [zeroDriftOvershoot_eq_walkOvershoot X hb (hω b)]
  rw [measure_congr hcong]
  exact gaussianZeroWalkOvershoot_tail_eq hX hi hG hb ht

/-- **The joint tail identity (E15).**  For `0 ≤ u < D` and `o ≥ 0`,
`P(U_D > u, O_D > o) = ∫_{[0,D-u]} ν₀((D+o-s,∞)) U₀(ds)`. -/
theorem zeroDrift_joint_tail_eq (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {D u o : ℝ} (hu : 0 ≤ u) (ho : 0 ≤ o)
    (huD : u < D) :
    μ {ω | u < zeroDriftUndershoot X D ω ∧ o < zeroDriftOvershoot X D ω} =
      renewalOvershootTail (gaussianAscendingLadderLaw X μ 0) (D - u) (u + o) := by
  have hcong : {ω | u < zeroDriftUndershoot X D ω ∧ o < zeroDriftOvershoot X D ω} =ᵐ[μ]
      {ω | u + o < zeroDriftOvershoot X (D - u) ω} := by
    filter_upwards [zeroDriftWalk_ne_ae hX hi hG (D - u)] with ω hne
    refine propext ?_
    exact level_age_residual_iff (entrancePath_zero X ω) hu ho huD hne
  rw [measure_congr hcong]
  exact zeroDriftOvershoot_tail_eq hX hi hG (by linarith) (by linarith)

/-- **The joint tail limit.**  For all real `u, o`,
`P(U_D > u, O_D > o) → Q̄₀(u⁺ + o⁺)` as `D → ∞`, where `Q̄₀` is the equilibrium overshoot
tail of `ν₀`. -/
theorem zeroDrift_joint_tail_tendsto (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (u o : ℝ) :
    Tendsto (fun D : ℝ =>
        μ.real {ω | u < zeroDriftUndershoot X D ω ∧ o < zeroDriftOvershoot X D ω}) atTop
      (𝓝 (equilibriumOvershootTail (gaussianAscendingLadderLaw X μ 0)
        (max u 0 + max o 0)).toReal) := by
  set u' := max u 0 with hu'
  set o' := max o 0 with ho'
  have hu0 : 0 ≤ u' := le_max_right _ _
  have ho0 : 0 ≤ o' := le_max_right _ _
  have hlim := (gaussianZeroLadder_renewalOvershootTail_tendsto hX hi hG
    (add_nonneg hu0 ho0)).comp (tendsto_atTop_add_const_right atTop (-u') tendsto_id)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop u'] with D hD
  have hDpos : 0 < D := lt_of_le_of_lt hu0 hD
  have hcong : {ω | u < zeroDriftUndershoot X D ω ∧ o < zeroDriftOvershoot X D ω} =ᵐ[μ]
      {ω | u' < zeroDriftUndershoot X D ω ∧ o' < zeroDriftOvershoot X D ω} := by
    filter_upwards [zeroDrift_age_residual_pos_ae hX hi hG hDpos] with ω hω
    refine propext ?_
    show (u < zeroDriftUndershoot X D ω ∧ o < zeroDriftOvershoot X D ω) ↔
      (u' < zeroDriftUndershoot X D ω ∧ o' < zeroDriftOvershoot X D ω)
    rw [hu', ho', max_lt_iff, max_lt_iff]
    tauto
  simp only [Function.comp_apply, id]
  rw [Measure.real, measure_congr hcong, zeroDrift_joint_tail_eq hX hi hG hu0 ho0 hD,
    ← sub_eq_add_neg]

end SwingRepair
