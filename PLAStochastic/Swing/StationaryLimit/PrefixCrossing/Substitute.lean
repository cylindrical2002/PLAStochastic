import PLAStochastic.Swing.StationaryLimit.Slope.EarlyLocalization
import PLAStochastic.Swing.Ladder.Renewal.WalkOvershootLimit
import PLAStochastic.Swing.Restart.Chain.Specification
import PLAStochastic.Swing.FirstSegment.LowerRejectionReflection
import PLAStochastic.Swing.StationaryLimit.MarginKernel.FiniteBudget
import PLAStochastic.Swing.FirstSegment.DurationMeasurability

/-!
# The finite-prefix crossing substitute

This file records the object used in the distant-crossing paragraph of
Appendix `app:limit`.  The prefix is indexed by `J ≥ 1`; its slope is the
maximum of the lower-cone ratios through `W_(J-1)`, and the remaining upper
constraint is represented by a positive-drift walk with reflected increments.

The probabilistic statement that the true constrained output eventually agrees
with this substitute still needs the strong-law/least-squares localization
argument.  We nevertheless make the substitute a genuine measurable random
variable and prove the exact algebraic bridge on any path on which the finite
recording length and the first crossing index are identified.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Prefix data -/

/-- The prefix slope `A_{r,J}`.  The zero-prefix value is only a totality
fallback; all crossing statements below assume `1 ≤ J`. -/
def prefixCrossingSlope (X : ℕ → Ω → ℝ) (r : ℝ) (J : ℕ) : Ω → ℝ :=
  if _hJ : 0 < J then swingEarlySlope X r (J - 1) else 0

/-- The level at which the reflected future walk must cross. -/
def prefixCrossingLevel (X : ℕ → Ω → ℝ) (E r : ℝ) (J : ℕ) : Ω → ℝ :=
  fun ω => 2*E-r-prefixCrossingSlope X r J ω*(J : ℝ) +
    cumulativeSamples X (J-1) ω

/-- The future walk after the prefix, with the rejected upper constraint
written as a positive-drift walk by reflecting the Gaussian increments. -/
def prefixCrossingOvershoot (X : ℕ → Ω → ℝ) (E r : ℝ) (J : ℕ) : Ω → ℝ :=
  fun ω => gaussianWalkOvershoot
    (negIncrements (fun j => X (J-1+j)))
    (prefixCrossingSlope X r J ω) (prefixCrossingLevel X E r J ω) ω

/-- Substitute output in `eq:prefixcrossinglevel`; exceptional nonpositive
prefix/level cases are sent to zero exactly as in the paper. -/
def prefixCrossingSubstitute (X : ℕ → Ω → ℝ) (E r : ℝ) (J : ℕ) : Ω → ℝ :=
  fun ω => if 0 < prefixCrossingSlope X r J ω ∧ 0 < prefixCrossingLevel X E r J ω then
    prefixCrossingSlope X r J ω - prefixCrossingOvershoot X E r J ω
  else 0

omit [MeasurableSpace Ω] in
theorem prefixCrossingSlope_eq_early {X : ℕ → Ω → ℝ} {r : ℝ} {J : ℕ}
    (hJ : 1 ≤ J) :
    prefixCrossingSlope X r J = swingEarlySlope X r (J-1) := by
  funext ω
  rw [prefixCrossingSlope]
  rw [dif_pos (lt_of_lt_of_le Nat.zero_lt_one hJ)]

/-! The lower-cone half of prefix feasibility is already deterministic.  For
an observation `i` in the prefix, its carried value is `E-r+W_(i-1)`, so the
lower endpoint `(D_i-E)/i` is exactly the corresponding early-slope ratio. -/
omit [MeasurableSpace Ω] in
theorem prefixCrossingSlope_lower_cone
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) (i : ℕ) (hi : i ∈ Finset.Icc 1 (J-1)) :
    (nativeCarriedSamples X (fun _ => E-r) i ω - E) / (i : ℝ) ≤
      prefixCrossingSlope X r J ω := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hiJ : i ≤ J-1 := (Finset.mem_Icc.mp hi).2
  have hindex : i - 1 ≤ J - 1 := by omega
  have hterm := swingSlopeTerm_le_swingEarlySlope X r ω hindex
  rw [prefixCrossingSlope_eq_early (X := X) (r := r) (J := J) hJ]
  have hcar : nativeCarriedSamples X (fun _ => E-r) i ω =
      E-r + cumulativeSamples X (i-1) ω := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    simp [nativeCarriedSamples_succ]
  rw [hcar]
  have hcast : (i : ℝ) = ((i-1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ i)]
    norm_num
  rw [hcast]
  dsimp [swingSlopeTerm] at hterm ⊢
  convert hterm using 1
  ring

/-! Combining the deterministic lower endpoint above with an upper-endpoint
bound gives feasibility of the prefix slope itself.  The upper bound is left
as an explicit hypothesis: proving it uniformly is the finite-prefix envelope
part of the later localization argument. -/
omit [MeasurableSpace Ω] in
theorem prefixCrossingSlope_feasible_prefix
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (ω : Ω)
    (hJ : 1 ≤ J)
    (hupper : ∀ i ∈ Finset.Icc 1 (J-1),
      prefixCrossingSlope X r J ω ≤
        (nativeCarriedSamples X (fun _ => E-r) i ω + E) / (i : ℝ)) :
    feasibleSlope (Finset.Icc 1 (J-1)) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω)
      0 0 E (prefixCrossingSlope X r J ω) := by
  have ht : ∀ i ∈ Finset.Icc 1 (J-1), (0 : ℝ) < (i : ℝ) := by
    intro i hi
    exact_mod_cast (Finset.mem_Icc.mp hi).1
  rw [feasibleSlope_iff_bounds _ _ _ 0 0 E _ ht]
  intro i hi
  refine ⟨?_, ?_⟩
  · simpa [slopeLower] using
      (prefixCrossingSlope_lower_cone E r J ω hJ i hi)
  · simpa [slopeUpper] using hupper i hi

/-! A deterministic finite-prefix envelope discharges the upper-cone premise
above.  This is the form used on a localization event: `K` bounds the incoming
margin, `Q` bounds the finitely many prefix partial sums, and the displayed
budget inequality is the only large-`E` requirement. -/

omit [MeasurableSpace Ω] in
theorem prefixCrossingSlope_feasible_prefix_of_prefix_bound
    {X : ℕ → Ω → ℝ} (E r K Q M : ℝ) (J : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) (hr : |r| ≤ K) (_hK : 0 ≤ K) (_hQ : 0 ≤ Q)
    (hM : 0 ≤ M) (hA : prefixCrossingSlope X r J ω ≤ M)
    (hW : ∀ i ∈ Finset.Icc 1 (J-1),
      |cumulativeSamples X (i-1) ω| ≤ Q)
    (hbudget : M * (J : ℝ) ≤ 2*E - K - Q) :
    feasibleSlope (Finset.Icc 1 (J-1)) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω)
      0 0 E (prefixCrossingSlope X r J ω) := by
  apply prefixCrossingSlope_feasible_prefix E r J ω hJ
  intro i hi
  have hiI := Finset.mem_Icc.mp hi
  have hiJ : (i : ℝ) ≤ (J : ℝ) := by
    have : i ≤ J-1 := hiI.2
    exact_mod_cast (show i ≤ J by omega)
  have hipos : (0 : ℝ) < (i : ℝ) := by
    exact_mod_cast hiI.1
  have hcar : nativeCarriedSamples X (fun _ => E-r) i ω =
      E-r + cumulativeSamples X (i-1) ω := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    simp [nativeCarriedSamples_succ]
  have hri : r ≤ K := by
    have := (abs_le.mp hr).2
    linarith
  have hwi : -Q ≤ cumulativeSamples X (i-1) ω := by
    have := neg_le_of_abs_le (hW i hi)
    linarith
  rw [hcar]
  apply (le_div_iff₀ hipos).2
  have hslM : prefixCrossingSlope X r J ω * (i : ℝ) ≤ M * (i : ℝ) :=
    mul_le_mul_of_nonneg_right hA hipos.le
  have hMi : M * (i : ℝ) ≤ M * (J : ℝ) :=
    mul_le_mul_of_nonneg_left hiJ hM
  linarith [hbudget, hslM, hMi]

omit [MeasurableSpace Ω] in
theorem prefixCrossingLevel_eq_paper {X : ℕ → Ω → ℝ} {E r : ℝ} {J : ℕ}
    (_hJ : 1 ≤ J) (ω : Ω) :
    prefixCrossingLevel X E r J ω =
      2*E-r-prefixCrossingSlope X r J ω*(J : ℝ) + cumulativeSamples X (J-1) ω := by
  rfl

/-!
For a fixed finite prefix the crossing level is affine in the budget with
strictly positive coefficient.  This elementary fact is the deterministic
part of the ``level tends to infinity'' assertion used before applying the
uniform overshoot limit; no Gaussian or slope hypothesis is needed here.
-/
omit [MeasurableSpace Ω] in
theorem prefixCrossingLevel_tendsto_atTop
    (X : ℕ → Ω → ℝ) (r : ℝ) (J : ℕ) (ω : Ω) :
    Tendsto (fun E : ℝ => prefixCrossingLevel X E r J ω) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro z
  filter_upwards [eventually_ge_atTop
    ((z + r + prefixCrossingSlope X r J ω * (J : ℝ) -
      cumulativeSamples X (J-1) ω) / 2)] with E hE
  dsimp [prefixCrossingLevel]
  linarith

omit [MeasurableSpace Ω] in
theorem prefixCrossingLevel_eventually_pos
    (X : ℕ → Ω → ℝ) (r : ℝ) (J : ℕ) (ω : Ω) :
    ∀ᶠ E : ℝ in atTop, 0 < prefixCrossingLevel X E r J ω := by
  exact (prefixCrossingLevel_tendsto_atTop X r J ω).eventually_gt_atTop 0

/-! ## Measurability -/

theorem prefixCrossingSlope_measurable {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n))
    (r : ℝ) (J : ℕ) : Measurable (prefixCrossingSlope X r J) := by
  unfold prefixCrossingSlope
  split
  · exact swingEarlySlope_measurable (Ω := Ω) (X := X) hX r (J-1)
  · exact measurable_const

theorem prefixCrossingLevel_measurable {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n))
    (E r : ℝ) (J : ℕ) : Measurable (prefixCrossingLevel X E r J) := by
  unfold prefixCrossingLevel
  convert (((measurable_const (a := (2*E-r : ℝ))).sub
    (measurable_const (a := (0 : ℝ)))).sub
    ((prefixCrossingSlope_measurable (Ω := Ω) (X := X) hX r J).mul_const (J : ℝ))).add
      (cumulativeSamples_measurable (Ω := Ω) (X := X) hX (J-1)) using 1
  ext ω
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-! A version of passage/overshoot measurability with random drift and level.
The random parameters are exactly the prefix slope and crossing level. -/
theorem gaussianWalkPassage_random_measurable
    {Y : ℕ → Ω → ℝ} {a b : Ω → ℝ}
    (hY : ∀ n, Measurable (Y n)) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => gaussianWalkPassage Y (a ω) (b ω) ω) := by
  have hW : ∀ m, Measurable (fun ω => gaussianDriftWalk Y 0 (a ω) m ω) := by
    intro m
    convert (cumulativeSamples_measurable (Ω := Ω) hY m).add
      (ha.mul_const (m : ℝ)) using 1
    funext ω
    simp [gaussianDriftWalk]
  have hE : ∀ m, MeasurableSet
      {ω | b ω < gaussianDriftWalk Y 0 (a ω) m ω} := fun m =>
    measurableSet_lt hb (hW m)
  have hEc : ∀ m, MeasurableSet
      {ω | ¬ b ω < gaussianDriftWalk Y 0 (a ω) m ω} := fun m =>
    (hE m).compl
  refine measurable_to_countable' fun n => ?_
  match n with
  | 0 =>
    have hset : (fun ω => gaussianWalkPassage Y (a ω) (b ω) ω) ⁻¹' {0} =
        {ω | b ω < gaussianDriftWalk Y 0 (a ω) 0 ω} ∪
          ⋂ m : ℕ, {ω | ¬ b ω < gaussianDriftWalk Y 0 (a ω) m ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_iInter,
        Set.mem_ofPred_eq]
      constructor
      · intro hω
        by_cases hex : ∃ m : ℕ, b ω < gaussianDriftWalk Y 0 (a ω) m ω
        · left
          have hfind : Nat.find hex = 0 := by
            rw [gaussianWalkPassage, dif_pos hex] at hω
            exact hω
          have hspec := Nat.find_spec hex
          rwa [hfind] at hspec
        · right
          intro m hm
          exact hex ⟨m, hm⟩
      · intro hω
        rcases hω with hω | hω
        · have hex : ∃ m : ℕ, b ω < gaussianDriftWalk Y 0 (a ω) m ω := ⟨0, hω⟩
          rw [gaussianWalkPassage, dif_pos hex]
          exact Nat.find_eq_zero hex |>.mpr hω
        · have hex : ¬ ∃ m : ℕ, b ω < gaussianDriftWalk Y 0 (a ω) m ω := by
            rintro ⟨m, hm⟩
            exact hω m hm
          rw [gaussianWalkPassage, dif_neg hex]
    rw [hset]
    exact (hE 0).union (MeasurableSet.iInter fun m => hEc m)
  | (n+1) =>
    have hset : (fun ω => gaussianWalkPassage Y (a ω) (b ω) ω) ⁻¹' {n+1} =
        {ω | b ω < gaussianDriftWalk Y 0 (a ω) (n+1) ω} ∩
          ⋂ j : ℕ, ⋂ _ : j < n+1,
            {ω | ¬ b ω < gaussianDriftWalk Y 0 (a ω) j ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_ofPred_eq]
      constructor
      · intro hω
        by_cases hex : ∃ m : ℕ, b ω < gaussianDriftWalk Y 0 (a ω) m ω
        · rw [gaussianWalkPassage, dif_pos hex] at hω
          have hfind := (Nat.find_eq_iff hex).mp hω
          exact ⟨hfind.1, fun j hj => hfind.2 j hj⟩
        · rw [gaussianWalkPassage, dif_neg hex] at hω
          exact absurd hω (by omega)
      · rintro ⟨h1, h2⟩
        have hex : ∃ m : ℕ, b ω < gaussianDriftWalk Y 0 (a ω) m ω := ⟨n+1, h1⟩
        rw [gaussianWalkPassage, dif_pos hex]
        exact (Nat.find_eq_iff hex).mpr ⟨h1, fun j hj => h2 j hj⟩
    rw [hset]
    exact (hE (n+1)).inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => hEc j)

theorem gaussianWalkOvershoot_random_measurable
    {Y : ℕ → Ω → ℝ} {a b : Ω → ℝ}
    (hY : ∀ n, Measurable (Y n)) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => gaussianWalkOvershoot Y (a ω) (b ω) ω) := by
  have hτ := gaussianWalkPassage_random_measurable hY ha hb
  have hU : ∀ m, Measurable (fun ω => gaussianDriftWalk Y 0 (a ω) m ω) := by
    intro m
    convert (cumulativeSamples_measurable (Ω := Ω) hY m).add
      (ha.mul_const (m : ℝ)) using 1
    funext ω
    simp [gaussianDriftWalk]
  convert (measurable_apply_nat hτ hU).sub hb using 1
  funext ω
  rfl

theorem prefixCrossingOvershoot_measurable {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n))
    (E r : ℝ) (J : ℕ) : Measurable (prefixCrossingOvershoot X E r J) := by
  unfold prefixCrossingOvershoot
  apply gaussianWalkOvershoot_random_measurable
  · intro n
    exact (hX (J-1+n)).neg
  · exact prefixCrossingSlope_measurable (Ω := Ω) (X := X) hX r J
  · exact prefixCrossingLevel_measurable (Ω := Ω) (X := X) hX E r J

theorem prefixCrossingSubstitute_measurable {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n))
    (E r : ℝ) (J : ℕ) : Measurable (prefixCrossingSubstitute X E r J) := by
  unfold prefixCrossingSubstitute
  apply Measurable.ite
  · exact (measurableSet_lt (measurable_const (a := (0 : ℝ)))
      (prefixCrossingSlope_measurable (Ω := Ω) (X := X) hX r J)).inter
      (measurableSet_lt (measurable_const (a := (0 : ℝ)))
        (prefixCrossingLevel_measurable (Ω := Ω) (X := X) hX E r J))
  · exact (prefixCrossingSlope_measurable (Ω := Ω) (X := X) hX r J).sub
      (prefixCrossingOvershoot_measurable (Ω := Ω) (X := X) hX E r J)
  · exact measurable_const

/-! ## The crossing algebra -/

omit [MeasurableSpace Ω] in
theorem cumulativeSamples_shifted_succ
    (X : ℕ → Ω → ℝ) (J k : ℕ) (_hJ : 1 ≤ J) (ω : Ω) :
    cumulativeSamples X (J-1+k) ω =
      cumulativeSamples X (J-1) ω +
        cumulativeSamples (fun j => X (J-1+j)) k ω := by
  exact cumulativeSamples_add_shift X (J-1) k ω

omit [MeasurableSpace Ω] in
theorem prefixCrossingOvershoot_eq_formula
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J k : ℕ) (ω : Ω)
    (_hJ : 1 ≤ J)
    (hk : gaussianWalkPassage
      (negIncrements (fun j => X (J-1+j)))
      (prefixCrossingSlope X r J ω)
      (prefixCrossingLevel X E r J ω) ω = k) :
    prefixCrossingOvershoot X E r J ω =
      prefixCrossingSlope X r J ω * (k : ℝ) -
        cumulativeSamples (fun j => X (J-1+j)) k ω -
          prefixCrossingLevel X E r J ω := by
  unfold prefixCrossingOvershoot gaussianWalkOvershoot
  rw [hk]
  simp only [gaussianDriftWalk, cumulativeSamples, negIncrements]
  rw [Finset.sum_neg_distrib]
  ring

/-! The exact reflection algebra used after the (separate) first-crossing
identification.  Keeping this lemma independent of the passage index makes
the remaining localization obligation explicit rather than hiding it in an
unproved rewrite. -/
omit [MeasurableSpace Ω] in
theorem finiteMarginMap_neg_affine (E a o : ℝ)
    (ho : 0 ≤ o) (haE : a ≤ E) :
    E - |-E + a - o| = a - o := by
  have hnonpos : -E + a - o ≤ 0 := by linarith
  rw [abs_of_nonpos hnonpos]
  linarith

omit [MeasurableSpace Ω] in
theorem finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_of_bridge
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J : ℕ) (ω : Ω)
    (ha : 0 < prefixCrossingSlope X r J ω)
    (hb : 0 < prefixCrossingLevel X E r J ω)
    (ho : 0 ≤ prefixCrossingOvershoot X E r J ω)
    (haE : prefixCrossingSlope X r J ω ≤ E)
    (hnext : nativeRestartNext X E (E-r) ω =
      -E + prefixCrossingSlope X r J ω -
        prefixCrossingOvershoot X E r J ω) :
    finiteMarginMap E (nativeRestartNext X E (E-r) ω) =
      prefixCrossingSubstitute X E r J ω := by
  rw [finiteMarginMap, hnext]
  have hnonpos : -E + prefixCrossingSlope X r J ω -
      prefixCrossingOvershoot X E r J ω ≤ 0 := by linarith
  rw [abs_of_nonpos hnonpos]
  unfold prefixCrossingSubstitute
  rw [if_pos ⟨ha, hb⟩]
  linarith

/-!
If the first rejected point is known to be the lower (negative-residual)
rejection, the bridge hypotheses above can be discharged directly from the
native prefix specification.  This is the exact finite-path reduction used in
the paper; the remaining asymptotic work is to prove that this lower branch,
the prefix slope, and the distant crossing index occur on one high-probability
localization event.
-/
omit [MeasurableSpace Ω] in
theorem finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_of_lower_rejection
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J k : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) (hE : 0 ≤ E)
    (hfinite : nativeRestartLength X E (E-r) ω ≠ ⊤)
    (hlen : nativeRestartLengthNat X E (E-r) ω = J-1+k)
    (hslope : nativeRestartSlope X E (E-r) ω =
      prefixCrossingSlope X r J ω)
    (ha : 0 < prefixCrossingSlope X r J ω)
    (hlevel : 0 < prefixCrossingLevel X E r J ω)
    (haE : prefixCrossingSlope X r J ω ≤ E)
    (hfail : nativeRestartNext X E (E-r) ω -
      prefixCrossingSlope X r J ω < -E) :
    finiteMarginMap E (nativeRestartNext X E (E-r) ω) =
      prefixCrossingSubstitute X E r J ω := by
  let a : ℝ := prefixCrossingSlope X r J ω
  let b : ℝ := prefixCrossingLevel X E r J ω
  have hfeas := nativeRestartSlope_feasible X hE (E-r) ω hfinite
  have hprefix : ∀ j : ℕ, j < k →
      gaussianDriftWalk (negIncrements (fun q => X (J-1+q))) 0 a j ω ≤ b := by
    intro j hj
    have hiJ : 1 ≤ J+j := by omega
    have hiN : J+j ≤ J-1+k := by omega
    have hiN' : J+j ≤ nativeRestartLengthNat X E (E-r) ω := by
      rw [hlen]
      exact hiN
    have hf := hfeas (J+j) (Finset.mem_Icc.mpr ⟨hiJ, hiN'⟩)
    rw [hslope] at hf
    have hlow : -E ≤
        nativeCarriedSamples X (fun _ => E-r) (J+j) ω -
          a*((J+j : ℕ) : ℝ) := by
      simpa [a] using (abs_le.mp hf).1
    have hcar : nativeCarriedSamples X (fun _ => E-r) (J+j) ω =
        E-r + cumulativeSamples X (J-1+j) ω := by
      rw [show J+j = (J-1+j)+1 by omega, nativeCarriedSamples_succ]
    rw [hcar] at hlow
    have hshift : cumulativeSamples X (J-1+j) ω =
        cumulativeSamples X (J-1) ω +
          cumulativeSamples (fun q => X (J-1+q)) j ω :=
      cumulativeSamples_shifted_succ X J j hJ ω
    have hwalk : gaussianDriftWalk
        (negIncrements (fun q => X (J-1+q))) 0 a j ω =
        a*(j : ℝ) - cumulativeSamples (fun q => X (J-1+q)) j ω := by
      simp [gaussianDriftWalk, cumulativeSamples_neg]
      ring
    rw [hshift] at hlow
    rw [hwalk]
    change a*(j : ℝ) - cumulativeSamples (fun q => X (J-1+q)) j ω ≤
      2*E-r-a*(J : ℝ) + cumulativeSamples X (J-1) ω
    push_cast at hlow ⊢
    linarith
  have hcrossk :
      b < gaussianDriftWalk (negIncrements (fun q => X (J-1+q))) 0 a k ω := by
    have hnext_expand : nativeRestartNext X E (E-r) ω =
        E-r + cumulativeSamples X (J-1+k) ω - a*((J-1+k : ℕ) : ℝ) := by
      rw [nativeRestartNext, hlen, hslope]
    have hshift : cumulativeSamples X (J-1+k) ω =
        cumulativeSamples X (J-1) ω +
          cumulativeSamples (fun q => X (J-1+q)) k ω :=
      cumulativeSamples_shifted_succ X J k hJ ω
    have hfail' : nativeRestartNext X E (E-r) ω - a < -E := by
      simpa [a] using hfail
    rw [hnext_expand, hshift] at hfail'
    have hwalk : gaussianDriftWalk
        (negIncrements (fun q => X (J-1+q))) 0 a k ω =
        a*(k : ℝ) - cumulativeSamples (fun q => X (J-1+q)) k ω := by
      simp [gaussianDriftWalk, cumulativeSamples_neg]
      ring
    rw [hwalk]
    change 2*E-r-a*(J : ℝ) + cumulativeSamples X (J-1) ω <
      a*(k : ℝ) - cumulativeSamples (fun q => X (J-1+q)) k ω
    have hcast : ((J-1+k : ℕ) : ℝ) = (J : ℝ) - 1 + (k : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub hJ]
      ring
    rw [hcast] at hfail'
    ring_nf at hfail' ⊢
    linarith
  have hcross : ∃ m : ℕ,
      b < gaussianDriftWalk (negIncrements (fun q => X (J-1+q))) 0 a m ω := by
    exact ⟨k, hcrossk⟩
  have hpass : gaussianWalkPassage
      (negIncrements (fun q => X (J-1+q))) a b ω = k := by
    rw [gaussianWalkPassage, dif_pos hcross]
    apply (Nat.find_eq_iff hcross).mpr
    refine ⟨?_, ?_⟩
    · exact hcrossk
    · intro j hj
      exact not_lt_of_ge (hprefix j hj)
  have ho := prefixCrossingOvershoot_eq_formula X E r J k ω hJ hpass
  have ho' : prefixCrossingOvershoot X E r J ω =
      a * (k : ℝ) - cumulativeSamples (fun q => X (J-1+q)) k ω - b := by
    simpa [a, b] using ho
  have hshift : cumulativeSamples X (J-1+k) ω =
      cumulativeSamples X (J-1) ω +
        cumulativeSamples (fun q => X (J-1+q)) k ω :=
    cumulativeSamples_shifted_succ X J k hJ ω
  have hnext0 : nativeRestartNext X E (E-r) ω =
      -E + prefixCrossingSlope X r J ω - prefixCrossingOvershoot X E r J ω := by
    calc
      nativeRestartNext X E (E-r) ω =
          E-r + cumulativeSamples X (J-1+k) ω -
            a * ((J-1+k : ℕ) : ℝ) := by
        rw [nativeRestartNext, hlen, hslope]
      _ = E-r + cumulativeSamples X (J-1) ω +
            cumulativeSamples (fun q => X (J-1+q)) k ω -
            a * ((J : ℝ) - 1 + (k : ℝ)) := by
        rw [hshift]
        have hcast : ((J-1+k : ℕ) : ℝ) = (J : ℝ) - 1 + (k : ℝ) := by
          rw [Nat.cast_add, Nat.cast_sub hJ]
          ring
        rw [hcast]
        ring
      _ = -E + prefixCrossingSlope X r J ω -
            prefixCrossingOvershoot X E r J ω := by
        rw [ho']
        dsimp [a, b, prefixCrossingLevel]
        ring
  have hnext : nativeRestartNext X E (E-r) ω =
      -E + a - prefixCrossingOvershoot X E r J ω := by
    simpa [a] using hnext0
  have ho_nonneg : 0 ≤ prefixCrossingOvershoot X E r J ω := by
    unfold prefixCrossingOvershoot gaussianWalkOvershoot
    rw [hpass]
    dsimp [gaussianDriftWalk]
    simp only [cumulativeSamples_neg]
    have hgt := hcrossk
    linarith
  exact finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_of_bridge
    X E r J ω ha hlevel ho_nonneg haE hnext

/-! A named event packaging the finite-path hypotheses.  This is useful when
the strong-law/least-squares argument is supplied separately: no pathwise
condition is silently promoted to an asymptotic theorem. -/
omit [MeasurableSpace Ω] in
def prefixCrossingLowerBridgeEvent
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J k : ℕ) : Set Ω :=
  {ω | nativeRestartLength X E (E-r) ω ≠ ⊤} ∩
    ({ω | nativeRestartLengthNat X E (E-r) ω = J-1+k} ∩
      ({ω | nativeRestartSlope X E (E-r) ω = prefixCrossingSlope X r J ω} ∩
        ({ω | 0 < prefixCrossingSlope X r J ω} ∩
          ({ω | 0 < prefixCrossingLevel X E r J ω} ∩
            ({ω | prefixCrossingSlope X r J ω ≤ E} ∩
              {ω | nativeRestartNext X E (E-r) ω -
                prefixCrossingSlope X r J ω < -E})))))

omit [MeasurableSpace Ω] in
theorem finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_on_event
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J k : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) (hE : 0 ≤ E)
    (hω : ω ∈ prefixCrossingLowerBridgeEvent X E r J k) :
    finiteMarginMap E (nativeRestartNext X E (E-r) ω) =
      prefixCrossingSubstitute X E r J ω := by
  rcases hω with ⟨hfinite, hlen, hslope, ha, hlevel, haE, hfail⟩
  exact finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_of_lower_rejection
    X E r J k ω hJ hE hfinite hlen hslope ha hlevel haE hfail

theorem finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_ae
    {μ : Measure Ω} [SFinite μ]
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J k : ℕ)
    (hJ : 1 ≤ J) (hE : 0 ≤ E)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ prefixCrossingLowerBridgeEvent X E r J k) :
    (fun ω => finiteMarginMap E (nativeRestartNext X E (E-r) ω)) =ᵐ[μ]
      prefixCrossingSubstitute X E r J := by
  filter_upwards [hgood] with ω hω
  exact finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_on_event
    X E r J k ω hJ hE hω

end SwingRepair
