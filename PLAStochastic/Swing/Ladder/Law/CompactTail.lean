import PLAStochastic.Swing.Ladder.Law.AscendingLaw
import PLAStochastic.Swing.FrozenCarry.Interior.GoodTail

/-!
# Uniform tails of the actual positive-drift Gaussian ladder height

The ladder time is controlled by the Gaussian endpoint.  Before that time
the walk is nonpositive, so its ladder height is bounded by the selected
last increment plus the drift.  A finite union bound then gives a genuine
uniform exponential tail on every compact positive drift interval.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem gaussianAscendingLadderTime_tail_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 0 < N) :
    μ.real {ω | (N : WithTop ℕ) < gaussianAscendingLadderTime X a ω} ≤
      2 * Real.exp (-a^2 * (N : ℝ) / 2) := by
  have := hi.isProbabilityMeasure
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : {ω | (N : WithTop ℕ) < gaussianAscendingLadderTime X a ω} ⊆
      {ω | a * (N : ℝ) ≤ |cumulativeSamples X N ω|} := by
    intro ω hω
    have hs := (lt_gaussianHalfLineExit_iff (fun n ω => -X n ω) 0 (-a) N ω).mp hω
    have hp := hs N le_rfl
    rw [gaussianDriftWalk_reflect_neg_drift] at hp
    have hwalk : cumulativeSamples X N ω + a * (N : ℝ) ≤ 0 := by
      simpa [gaussianDriftWalk] using neg_nonneg.mp hp
    change a * (N : ℝ) ≤ |cumulativeSamples X N ω|
    linarith [neg_le_abs (cumulativeSamples X N ω)]
  have ht := cumulativeSamples_abs_tail_bound hX hi hG N
    (show 0 ≤ a * (N : ℝ) by positivity)
  have heq : -(a * (N : ℝ))^2 / (2 * (N : ℝ)) = -a^2 * (N : ℝ) / 2 := by
    field_simp
  rw [heq] at ht
  exact (measureReal_mono hsub).trans ht

omit [MeasurableSpace Ω] in
theorem gaussianAscendingLadderHeight_le_last_increment
    {a : ℝ} {n : ℕ} {ω : Ω}
    (hT : gaussianAscendingLadderTime X a ω = (n+1 : ℕ)) :
    gaussianAscendingLadderHeight X a ω ≤ X n ω + a := by
  have hs := (gaussianHalfLineExit_eq_succ_iff (fun n ω => -X n ω) 0 (-a) n ω).mp hT
  have hp := hs.1 n le_rfl
  have he := gaussianHalfLineOvershoot_of_slice hs
  change gaussianAscendingLadderHeight X a ω =
    -gaussianDriftWalk (fun n ω => -X n ω) 0 (-a) (n+1) ω at he
  rw [gaussianDriftWalk_succ] at he
  linarith

omit [MeasurableSpace Ω] in
theorem gaussianAscendingLadderHeight_tail_subset
    {a t : ℝ} (_ht : 0 ≤ t) (N : ℕ) :
    {ω | t < gaussianAscendingLadderHeight X a ω} ⊆
      {ω | (N : WithTop ℕ) < gaussianAscendingLadderTime X a ω} ∪
        ⋃ n ∈ Finset.range N, {ω | t-a < X n ω} := by
  intro ω hω
  by_cases hlate : (N : WithTop ℕ) < gaussianAscendingLadderTime X a ω
  · exact Or.inl hlate
  · apply Or.inr
    have hle : gaussianAscendingLadderTime X a ω ≤ (N : WithTop ℕ) := le_of_not_gt hlate
    have hfinite : gaussianAscendingLadderTime X a ω ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hle
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hmpos : 0 < m := by
      have hp := gaussianAscendingLadderTime_pos (X := X) a ω
      rw [← hm] at hp
      exact WithTop.coe_lt_coe.mp hp
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    have hn : n < N := by
      rw [← hm] at hle
      have hh : n+1 ≤ N := WithTop.coe_le_coe.mp hle
      omega
    refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨Finset.mem_range.mpr hn, ?_⟩⟩
    have hb := gaussianAscendingLadderHeight_le_last_increment hm.symm
    change t-a < X n ω
    change t < gaussianAscendingLadderHeight X a ω at hω
    linarith

theorem gaussianAscendingLadderHeight_cutoff_tail_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) {N : ℕ} (hN : 0 < N) :
    μ.real {ω | t < gaussianAscendingLadderHeight X a ω} ≤
      2 * Real.exp (-a^2 * (N : ℝ) / 2) +
        (N : ℝ) * Real.exp (-(t-a)^2 / 2) := by
  have := hi.isProbabilityMeasure
  have hb (n : ℕ) : μ.real {ω | t-a < X n ω} ≤ Real.exp (-(t-a)^2/2) := by
    have hmap : μ.real {ω | t-a ≤ X n ω} =
        (gaussianReal 0 1).real {z | t-a ≤ z} := by
      have hl : HasLaw (X n) (gaussianReal 0 1) μ := ⟨(hX n).aemeasurable, hG n⟩
      exact hl.measureReal_eq (p := fun z => t-a ≤ z)
        (measurableSet_le measurable_const measurable_id)
    calc
      _ ≤ μ.real {ω | t-a ≤ X n ω} :=
        measureReal_mono (fun ω h => show t-a ≤ X n ω from le_of_lt h)
      _ = _ := hmap
      _ ≤ _ := by simpa using gaussianReal_nonnegative_tail_bound 1 (sub_nonneg.mpr hat)
  have hu : μ.real (⋃ n ∈ Finset.range N, {ω | t-a < X n ω}) ≤
      (N : ℝ) * Real.exp (-(t-a)^2/2) := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, μ.real {ω | t-a < X n ω} :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, Real.exp (-(t-a)^2/2) :=
        Finset.sum_le_sum (fun n _ => hb n)
      _ = _ := by simp
  exact ((measureReal_mono (gaussianAscendingLadderHeight_tail_subset (ha.trans hat) N)).trans
    (measureReal_union_le _ _)).trans
      (add_le_add (gaussianAscendingLadderTime_tail_le hX hi hG ha hN) hu)

def gaussianAscendingLadderTailRate (δ : ℝ) : ℝ := min (δ^2 / 2) (1/4)

theorem gaussianAscendingLadderTailRate_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < gaussianAscendingLadderTailRate δ := by
  unfold gaussianAscendingLadderTailRate
  exact lt_min (by positivity) (by norm_num)

private theorem mul_exp_neg_sq_le_exp_neg_quarter (x : ℝ) :
    x * Real.exp (-x^2/2) ≤ Real.exp (-x/4) := by
  have hx : x ≤ Real.exp (x^2/2-x/4) := by
    have he := Real.add_one_le_exp (x^2/2-x/4)
    nlinarith [sq_nonneg (x-5/4)]
  calc
    _ ≤ Real.exp (x^2/2-x/4) * Real.exp (-x^2/2) :=
      mul_le_mul_of_nonneg_right hx (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- A genuine uniform exponential tail on every interval `δ ≤ a ≤ M` with
`δ > 0`.  The shift by `M` accounts for the last positive drift increment. -/
theorem gaussianAscendingLadderHeight_compact_tail
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    {N : ℕ} (hN : 0 < N) :
    μ.real {ω | M + (N : ℝ) < gaussianAscendingLadderHeight X a ω} ≤
      3 * Real.exp (-gaussianAscendingLadderTailRate δ * (N : ℝ)) := by
  have ha : 0 ≤ a := hδ.le.trans hδa
  have hNR : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hbase := gaussianAscendingLadderHeight_cutoff_tail_le hX hi hG ha
    (show a ≤ M + (N : ℝ) by linarith) hN
  have htime : Real.exp (-a^2 * (N : ℝ) / 2) ≤
      Real.exp (-(δ^2/2) * (N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hsq : δ^2 ≤ a^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq hNR]
  have hlast : Real.exp (-(M + (N : ℝ)-a)^2 / 2) ≤
      Real.exp (-(N : ℝ)^2 / 2) := by
    apply Real.exp_le_exp.mpr
    have hh : (N : ℝ) ≤ M + (N : ℝ)-a := by linarith
    nlinarith
  have hcδ : gaussianAscendingLadderTailRate δ ≤ δ^2/2 := min_le_left _ _
  have hcq : gaussianAscendingLadderTailRate δ ≤ (1/4 : ℝ) := min_le_right _ _
  have htime' : Real.exp (-(δ^2/2) * (N : ℝ)) ≤
      Real.exp (-gaussianAscendingLadderTailRate δ * (N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hcδ hNR]
  have hlast' : Real.exp (-(N : ℝ)/4) ≤
      Real.exp (-gaussianAscendingLadderTailRate δ * (N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hcq hNR]
  have hproduct : (N : ℝ) * Real.exp (-(M+(N : ℝ)-a)^2/2) ≤
      Real.exp (-gaussianAscendingLadderTailRate δ * (N : ℝ)) := by
    exact ((mul_le_mul_of_nonneg_left hlast hNR).trans
      (mul_exp_neg_sq_le_exp_neg_quarter (N : ℝ))).trans hlast'
  have ht := htime.trans htime'
  linarith

theorem gaussianAscendingLadderLaw_compact_tail
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    {N : ℕ} (hN : 0 < N) :
    (gaussianAscendingLadderLaw X μ a).real (Ioi (M + (N : ℝ))) ≤
      3 * Real.exp (-gaussianAscendingLadderTailRate δ * (N : ℝ)) := by
  have hl : HasLaw (gaussianAscendingLadderHeight X a) (gaussianAscendingLadderLaw X μ a) μ :=
    ⟨(gaussianAscendingLadderHeight_measurable hX a).aemeasurable, rfl⟩
  have he := hl.measureReal_eq (p := fun u => M + (N : ℝ) < u) measurableSet_Ioi
  change (gaussianAscendingLadderLaw X μ a).real {u | M + (N : ℝ) < u} ≤ _
  rw [← he]
  exact gaussianAscendingLadderHeight_compact_tail hX hi hG hδ hδa haM hN

end SwingRepair
