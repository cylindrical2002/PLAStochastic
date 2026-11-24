import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.Substitute
import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.LeastSquares
import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.PassageWindows

/-!
# Deterministic distant-crossing bridge

This file packages the finite, pathwise part of the distant-crossing argument.
It does not assert the strong-law localization event.  Instead it exposes the
exact hypotheses needed to turn a feasible prefix and a first upper crossing
into the native restart length, selected slope, and reflected margin update.
The hypotheses are deliberately pointwise, so the probabilistic localization
lemmas can be supplied independently.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Generic maximal-prefix identification -/

omit [MeasurableSpace Ω] in
theorem nativeRestartLengthNat_eq_of_feasible_and_rejected
    (X : ℕ → Ω → ℝ) (E x : ℝ) (N : ℕ) (ω : Ω)
    (hfit : nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) E 0 N 0)
    (hrej : ¬ nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) E 0 (N + 1) 0) :
    nativeRestartLength X E x ω ≠ ⊤ ∧
      nativeRestartLengthNat X E x ω = N := by
  have hlow : (N : WithTop ℕ) ≤ nativeRestartLength X E x ω := by
    exact (le_nativePrefixLength_iff
      (nativeCarriedSamples X (fun _ => x)) (fun _ => 0) E ω N).mpr hfit
  have hupp : nativeRestartLength X E x ω ≤ (N : WithTop ℕ) := by
    apply (nativePrefixLength_le_iff
      (nativeCarriedSamples X (fun _ => x)) (fun _ => 0) E ω N).mpr
    exact ⟨N, le_rfl, hrej⟩
  have heq : nativeRestartLength X E x ω = (N : WithTop ℕ) := le_antisymm hupp hlow
  constructor
  · rw [heq]
    exact WithTop.coe_ne_top
  · change (nativeRestartLength X E x ω).untopD 0 = N
    simp [heq]

/-! ## A selector equality once the lower endpoint is known -/

omit [MeasurableSpace Ω] in
theorem nativeRestartSlope_eq_of_lower_endpoint_and_least_squares
    (X : ℕ → Ω → ℝ) (E x : ℝ) (N : ℕ) (ω : Ω)
    (hN : 1 ≤ N)
    (_hfinite : nativeRestartLength X E x ω ≠ ⊤)
    {A : ℝ}
    (hlower : nativeConeLower (Finset.Icc 1 N)
      (Finset.nonempty_Icc.mpr hN) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E = A)
    (hls : nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 ≤ A)
    (hlen : nativeRestartLengthNat X E x ω = N) :
    nativeRestartSlope X E x ω = A := by
  rw [nativeRestartSlope, hlen, nativeRestartSlopeAt, dif_pos (by omega : 0 < N)]
  exact nativeSelectedSlope_eq_of_lower_endpoint
    (Finset.nonempty_Icc.mpr hN) hlower hls

/-! ## A finite bridge with explicit cone hypotheses -/

omit [MeasurableSpace Ω] in
theorem nativeRestartLength_and_slope_eq_of_prefix_cone
    (X : ℕ → Ω → ℝ) (E x : ℝ) (N : ℕ) (ω : Ω)
    (hN : 1 ≤ N)
    {A : ℝ}
    (hfit : nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) E 0 N 0)
    (hrej : ¬ nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) E 0 (N + 1) 0)
    (hlower : nativeConeLower (Finset.Icc 1 N)
      (Finset.nonempty_Icc.mpr hN) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E = A)
    (hls : nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 ≤ A) :
    nativeRestartLength X E x ω ≠ ⊤ ∧
      nativeRestartLengthNat X E x ω = N ∧
      nativeRestartSlope X E x ω = A := by
  obtain ⟨hfinite, hlen⟩ := nativeRestartLengthNat_eq_of_feasible_and_rejected
    X E x N ω hfit hrej
  refine ⟨hfinite, hlen, ?_⟩
  exact nativeRestartSlope_eq_of_lower_endpoint_and_least_squares
    X E x N ω hN hfinite hlower hls hlen

/-! ## Translating the reflected crossing inequalities -/

omit [MeasurableSpace Ω] in
theorem nativeCarried_upper_bound_of_shifted_drift_le
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J k : ℕ) (ω : Ω)
    {a : ℝ} (hJ : 1 ≤ J) (ha : a = prefixCrossingSlope X r J ω)
    (j : ℕ) (_hjlt : j < k)
    (hwalk : gaussianDriftWalk
      (negIncrements (fun q => X (J - 1 + q))) 0 a j ω ≤
      prefixCrossingLevel X E r J ω) :
    a ≤ (nativeCarriedSamples X (fun _ => E-r) (J+j) ω + E) /
      ((J+j : ℕ) : ℝ) := by
  have hJpos : (0 : ℝ) < ((J + j : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < J + j by omega)
  have hshift : cumulativeSamples X (J - 1 + j) ω =
      cumulativeSamples X (J - 1) ω +
        cumulativeSamples (fun q => X (J - 1 + q)) j ω := by
    exact cumulativeSamples_shifted_succ X J j hJ ω
  have hcar : nativeCarriedSamples X (fun _ => E-r) (J+j) ω =
      E-r + cumulativeSamples X (J - 1 + j) ω := by
    rw [show J + j = (J - 1 + j) + 1 by omega,
      nativeCarriedSamples_succ]
  have hwalk' : gaussianDriftWalk
      (negIncrements (fun q => X (J - 1 + q))) 0 a j ω =
      a * (j : ℝ) - cumulativeSamples (fun q => X (J - 1 + q)) j ω := by
    simp [gaussianDriftWalk, cumulativeSamples_neg]
    ring
  rw [hwalk'] at hwalk
  dsimp [prefixCrossingLevel] at hwalk
  rw [← ha] at hwalk
  rw [hcar, hshift]
  apply (le_div_iff₀ hJpos).2
  have hcast : ((J + j : ℕ) : ℝ) = (J : ℝ) + (j : ℝ) := by
    push_cast
    ring
  rw [hcast]
  linarith

/-!
The previous helper is intentionally pointwise.  This wrapper turns a
no-crossing prefix of the reflected walk into all future upper-cone bounds.
-/

omit [MeasurableSpace Ω] in
theorem nativeCarried_future_upper_bounds_of_no_crossing
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J k : ℕ) (ω : Ω)
    {a : ℝ} (hJ : 1 ≤ J) (ha : a = prefixCrossingSlope X r J ω)
    (hbefore : ∀ j < k,
      gaussianDriftWalk (negIncrements (fun q => X (J - 1 + q))) 0 a j ω ≤
        prefixCrossingLevel X E r J ω) :
    ∀ i ∈ Finset.Icc J (J - 1 + k),
      a ≤ (nativeCarriedSamples X (fun _ => E-r) i ω + E) / (i : ℝ) := by
  intro i hi
  have hiJ : J ≤ i := (Finset.mem_Icc.mp hi).1
  have hiN : i ≤ J - 1 + k := (Finset.mem_Icc.mp hi).2
  let j : ℕ := i - J
  have hj_eq : J + j = i := by
    dsimp [j]
    omega
  have hjlt : j < k := by
    dsimp [j]
    omega
  have h := nativeCarried_upper_bound_of_shifted_drift_le X E r J k ω hJ
    ha j hjlt (hbefore j hjlt)
  simpa only [hj_eq] using h

/-! ## Feasibility and rejection from the cone bounds -/

omit [MeasurableSpace Ω] in
theorem nativeCarriedPrefix_feasible_of_prefix_future_bounds
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J k : ℕ) (ω : Ω)
    {a : ℝ} (hJ : 1 ≤ J) (ha : a = prefixCrossingSlope X r J ω)
    (_hN : 1 ≤ J - 1 + k)
    (hprefix : feasibleSlope (Finset.Icc 1 (J-1)) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 E a)
    (hlower_future : ∀ i ∈ Finset.Icc J (J - 1 + k),
      slopeLower (i : ℝ) (nativeCarriedSamples X (fun _ => E-r) i ω)
        0 0 E ≤ a)
    (hbefore : ∀ j < k,
      gaussianDriftWalk (negIncrements (fun q => X (J - 1 + q))) 0 a j ω ≤
        prefixCrossingLevel X E r J ω) :
    nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) E 0
      (J - 1 + k) 0 := by
  simp only [nativePrefixFeasible, Nat.zero_add, Nat.cast_zero]
  refine ⟨a, ?_⟩
  have ht : ∀ i ∈ Finset.Icc 1 (J - 1 + k), (0 : ℝ) < (i : ℝ) := by
    intro i hi
    exact_mod_cast (Finset.mem_Icc.mp hi).1
  rw [feasibleSlope_iff_bounds _ _ _ 0 0 E a ht]
  intro i hi
  by_cases hip : i ≤ J - 1
  · have hpi : i ∈ Finset.Icc 1 (J-1) := Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hi).1, hip⟩
    exact (feasibleSlope_iff_bounds _ _ _ 0 0 E a
      (fun j hj => by exact_mod_cast (Finset.mem_Icc.mp hj).1)).mp hprefix i hpi
  · have hiJ : J ≤ i := by omega
    have hfi : i ∈ Finset.Icc J (J - 1 + k) := Finset.mem_Icc.mpr
      ⟨hiJ, (Finset.mem_Icc.mp hi).2⟩
    have hlow := hlower_future i hfi
    have hupper := nativeCarried_future_upper_bounds_of_no_crossing
      X E r J k ω hJ ha hbefore i hfi
    have hupper' : a ≤ slopeUpper (i : ℝ)
        (nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 E := by
      simpa only [slopeUpper, sub_zero, add_zero] using hupper
    exact ⟨hlow, hupper'⟩

omit [MeasurableSpace Ω] in
theorem nativeCarriedPrefix_rejected_of_strict_upper_crossing
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J k : ℕ) (ω : Ω)
    {a : ℝ} (hJ : 1 ≤ J) (ha : a = prefixCrossingSlope X r J ω)
    (hi₀ : ∃ i₀ ∈ Finset.Icc 1 J,
      slopeLower (i₀ : ℝ) (nativeCarriedSamples X (fun _ => E-r) i₀ ω)
        0 0 E = a)
    (hcross : prefixCrossingLevel X E r J ω <
      a * (k : ℝ) - cumulativeSamples (fun q => X (J - 1 + q)) k ω) :
    ¬ nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) E 0
      (J - 1 + k + 1) 0 := by
  intro hbad
  obtain ⟨m, hm⟩ := hbad
  obtain ⟨i₀, hi₀, hloweq⟩ := hi₀
  have htime : ∀ i ∈ Finset.Icc 1 (J - 1 + k + 1), (0 : ℝ) < (i : ℝ) := by
    intro i hi
    exact_mod_cast (Finset.mem_Icc.mp hi).1
  have hm' : feasibleSlope (Finset.Icc 1 (J - 1 + k + 1))
      (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 E m := by
    simpa only [Nat.zero_add, Nat.cast_zero] using hm
  have hbounds := (feasibleSlope_iff_bounds _ _ _ 0 0 E m htime).mp hm'
  have hm_ge : a ≤ m := by
    have hi₀lo : 1 ≤ i₀ := (Finset.mem_Icc.mp hi₀).1
    have hi₀hi : i₀ ≤ J := (Finset.mem_Icc.mp hi₀).2
    have hone := hbounds i₀ (by
      exact Finset.mem_Icc.mpr ⟨hi₀lo, by omega⟩)
    rw [hloweq] at hone
    exact hone.1
  have hnew := hbounds (J + k) (by
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hupper : m ≤
      (nativeCarriedSamples X (fun _ => E-r) (J+k) ω + E) / ((J+k : ℕ) : ℝ) := by
    simpa only [slopeUpper, sub_zero, add_zero] using hnew.2
  have hcar : nativeCarriedSamples X (fun _ => E-r) (J+k) ω =
      E-r + cumulativeSamples X (J - 1 + k) ω := by
    rw [show J + k = (J - 1 + k) + 1 by omega, nativeCarriedSamples_succ]
  have hshift : cumulativeSamples X (J - 1 + k) ω =
      cumulativeSamples X (J - 1) ω +
        cumulativeSamples (fun q => X (J - 1 + q)) k ω := by
    exact cumulativeSamples_shifted_succ X J k hJ ω
  rw [hcar, hshift] at hupper
  have hcast : ((J + k : ℕ) : ℝ) = (J : ℝ) + (k : ℝ) := by
    push_cast
    ring
  rw [hcast] at hupper
  dsimp [prefixCrossingLevel] at hcross
  rw [← ha] at hcross
  have hstrict :
      (E-r + (cumulativeSamples X (J - 1) ω +
        cumulativeSamples (fun q => X (J - 1 + q)) k ω) + E) /
          ((J : ℝ) + (k : ℝ)) < a := by
    have hden : (0 : ℝ) < (J : ℝ) + (k : ℝ) := by
      exact_mod_cast (show 0 < J + k by omega)
    apply (div_lt_iff₀ hden).2
    linarith
  exact (not_lt_of_ge hm_ge) (hupper.trans_lt hstrict)

/-! A small interface lemma for feeding `gaussianWalkPassage = k` into the
first-crossing bridge.  The existence premise is intentionally explicit: the
definition uses the value `0` as its fallback when no crossing ever occurs. -/

omit [MeasurableSpace Ω] in
theorem gaussianWalkPassage_eq_index_spec
    {Y : ℕ → Ω → ℝ} {a b : ℝ} {ω : Ω} (k : ℕ)
    (hcross : ∃ m : ℕ, b < gaussianDriftWalk Y 0 a m ω)
    (hpass : gaussianWalkPassage Y a b ω = k) :
    b < gaussianDriftWalk Y 0 a k ω ∧
      ∀ j < k, gaussianDriftWalk Y 0 a j ω ≤ b := by
  rw [gaussianWalkPassage, dif_pos hcross] at hpass
  have hfind : Nat.find hcross = k := hpass
  constructor
  · rw [← hfind]
    exact Nat.find_spec hcross
  · intro j hj
    exact le_of_not_gt (by
      intro hbad
      have hmin := Nat.find_min hcross
        (show j < Nat.find hcross by simpa [hfind] using hj)
      exact hmin hbad)

omit [MeasurableSpace Ω] in
theorem prefixCrossingLevel_lt_of_reflected_crossing
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J k : ℕ) (ω : Ω)
    {a : ℝ}
    (hcross : prefixCrossingLevel X E r J ω <
      gaussianDriftWalk (negIncrements (fun q => X (J - 1 + q))) 0 a k ω) :
    prefixCrossingLevel X E r J ω <
      a * (k : ℝ) - cumulativeSamples (fun q => X (J - 1 + q)) k ω := by
  have hwalk : gaussianDriftWalk
      (negIncrements (fun q => X (J - 1 + q))) 0 a k ω =
      a * (k : ℝ) - cumulativeSamples (fun q => X (J - 1 + q)) k ω := by
    simp [gaussianDriftWalk, cumulativeSamples_neg]
    ring
  rw [hwalk] at hcross
  exact hcross

/-!
The following theorem is the advertised finite bridge.  The two hypotheses
`hbefore` and `hcross` are precisely the pathwise specification of a first
strict crossing at `k` for the reflected future walk.  All remaining
conditions are finite cone/localization checks: a feasible prefix, lower-cone
bounds on the future accepted points, one prefix point attaining the lower
endpoint, and the least-squares coefficient bound.
-/

omit [MeasurableSpace Ω] in
theorem finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_of_first_crossing_bounds
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J k : ℕ) (ω : Ω)
    {a : ℝ} (hJ : 1 ≤ J) (hE : 0 ≤ E)
    (ha : a = prefixCrossingSlope X r J ω)
    (hN : 1 ≤ J - 1 + k)
    (hprefix : feasibleSlope (Finset.Icc 1 (J-1)) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 E a)
    (hlower_future : ∀ i ∈ Finset.Icc J (J - 1 + k),
      slopeLower (i : ℝ) (nativeCarriedSamples X (fun _ => E-r) i ω)
        0 0 E ≤ a)
    (hi₀ : ∃ i₀ ∈ Finset.Icc 1 J,
      slopeLower (i₀ : ℝ) (nativeCarriedSamples X (fun _ => E-r) i₀ ω)
        0 0 E = a)
    (hbefore : ∀ j < k,
      gaussianDriftWalk (negIncrements (fun q => X (J - 1 + q))) 0 a j ω ≤
        prefixCrossingLevel X E r J ω)
    (hcross : prefixCrossingLevel X E r J ω <
      a * (k : ℝ) - cumulativeSamples (fun q => X (J - 1 + q)) k ω)
    (hls : nativeLeastSquares (Finset.Icc 1 (J - 1 + k)) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 ≤ a)
    (ha_pos : 0 < a) (hb : 0 < prefixCrossingLevel X E r J ω)
    (haE : a ≤ E) :
    nativeRestartLength X E (E-r) ω ≠ ⊤ ∧
      nativeRestartLengthNat X E (E-r) ω = J - 1 + k ∧
      nativeRestartSlope X E (E-r) ω = a ∧
      finiteMarginMap E (nativeRestartNext X E (E-r) ω) =
        prefixCrossingSubstitute X E r J ω := by
  have hfit := nativeCarriedPrefix_feasible_of_prefix_future_bounds
    X E r J k ω hJ ha hN hprefix hlower_future hbefore
  have hrej := nativeCarriedPrefix_rejected_of_strict_upper_crossing
    X E r J k ω hJ ha hi₀ hcross
  have hkpos : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    subst k
    have hzero : cumulativeSamples (fun q => X (J - 1 + q)) 0 ω = 0 := by simp
    rw [hzero] at hcross
    have : prefixCrossingLevel X E r J ω < 0 := by simpa using hcross
    linarith
  have htime_prefix : ∀ i ∈ Finset.Icc 1 (J - 1), (0 : ℝ) < (i : ℝ) := by
    intro i hi
    exact_mod_cast (Finset.mem_Icc.mp hi).1
  have hprefix_bounds := (feasibleSlope_iff_bounds _ _ _ 0 0 E a htime_prefix).mp hprefix
  have hlower_all : ∀ i ∈ Finset.Icc 1 (J - 1 + k),
      slopeLower (i : ℝ) (nativeCarriedSamples X (fun _ => E-r) i ω)
        0 0 E ≤ a := by
    intro i hi
    by_cases hip : i ≤ J - 1
    · exact (hprefix_bounds i (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hi).1, hip⟩)).1
    · exact hlower_future i (Finset.mem_Icc.mpr
        ⟨by omega, (Finset.mem_Icc.mp hi).2⟩)
  have hcone_le : nativeConeLower (Finset.Icc 1 (J - 1 + k))
      (Finset.nonempty_Icc.mpr hN) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 E ≤ a := by
    unfold nativeConeLower
    exact Finset.sup'_le _ _ (fun i hi => hlower_all i hi)
  obtain ⟨i₀, hi₀', hloweq⟩ := hi₀
  have hcone_ge : a ≤ nativeConeLower (Finset.Icc 1 (J - 1 + k))
      (Finset.nonempty_Icc.mpr hN) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 E := by
    rw [← hloweq]
    have hi₀lo : 1 ≤ i₀ := (Finset.mem_Icc.mp hi₀').1
    have hi₀hi : i₀ ≤ J := (Finset.mem_Icc.mp hi₀').2
    simpa only [nativeConeLower] using
      (Finset.le_sup'
        (fun j : ℕ => slopeLower ((j : ℝ))
          (nativeCarriedSamples X (fun _ => E-r) j ω) 0 0 E)
        (Finset.mem_Icc.mpr ⟨hi₀lo, by omega⟩))
  have hcone : nativeConeLower (Finset.Icc 1 (J - 1 + k))
      (Finset.nonempty_Icc.mpr hN) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 E = a :=
    le_antisymm hcone_le hcone_ge
  obtain ⟨hfinite, hlen, hslope⟩ := nativeRestartLength_and_slope_eq_of_prefix_cone
    X E (E-r) (J - 1 + k) ω hN hfit hrej hcone hls
  have hfail : nativeRestartNext X E (E-r) ω - a < -E := by
    rw [nativeRestartNext, hlen, hslope]
    have hshift : cumulativeSamples X (J - 1 + k) ω =
        cumulativeSamples X (J - 1) ω +
          cumulativeSamples (fun q => X (J - 1 + q)) k ω := by
      exact cumulativeSamples_shifted_succ X J k hJ ω
    rw [hshift]
    dsimp [prefixCrossingLevel] at hcross
    rw [← ha] at hcross
    have hcast : ((J - 1 + k : ℕ) : ℝ) = (J : ℝ) - 1 + (k : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub hJ]
      ring
    rw [hcast]
    linarith
  have hfail' : nativeRestartNext X E (E-r) ω -
      prefixCrossingSlope X r J ω < -E := by
    rw [← ha]
    exact hfail
  have hbridge := finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_of_lower_rejection
    X E r J k ω hJ hE hfinite hlen (hslope.trans ha)
      (by rw [← ha]; exact ha_pos) hb
      (by rw [← ha]; exact haE) hfail'
  exact ⟨hfinite, hlen, hslope, hbridge⟩

/-! ## Quantitative exceptional-event transfer -/

theorem integral_sub_le_of_eqOn_event_of_bounded
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {F G : Ω → ℝ} {A : Set Ω} {B δ : ℝ}
    (hA : MeasurableSet A)
    (hF : Integrable F μ) (hG : Integrable G μ)
    (hFB : ∀ᵐ ω ∂μ, |F ω| ≤ B)
    (hGB : ∀ᵐ ω ∂μ, |G ω| ≤ B)
    (hEq : EqOn F G A)
    (hbad : μ.real Aᶜ ≤ δ) (hB : 0 ≤ B) (_hδ : 0 ≤ δ) :
    |(∫ ω, F ω ∂μ) - ∫ ω, G ω ∂μ| ≤ 2 * B * δ := by
  have hH : Integrable (fun ω => F ω - G ω) μ := hF.sub hG
  have hHB : ∀ᵐ ω ∂μ, ‖F ω - G ω‖ ≤ 2 * B := by
    filter_upwards [hFB, hGB] with ω hFω hGω
    rw [Real.norm_eq_abs, abs_sub_comm]
    calc
      |G ω - F ω| ≤ ‖G ω - F ω‖ := by rfl
      _ ≤ ‖G ω‖ + ‖F ω‖ := norm_sub_le _ _
      _ = |G ω| + |F ω| := by simp only [Real.norm_eq_abs]
      _ ≤ B + B := add_le_add hGω hFω
      _ = 2 * B := by ring
  have hgood : (∫ ω in A, (F ω - G ω) ∂μ) = 0 := by
    have heq : (∫ ω in A, (F ω - G ω) ∂μ) =
        ∫ ω in A, (fun _ => (0 : ℝ)) ω ∂μ := by
      apply setIntegral_congr_fun hA
      intro ω hω
      change F ω - G ω = 0
      rw [hEq hω]
      ring
    simpa using heq
  have htotal : (∫ ω, F ω ∂μ) - ∫ ω, G ω ∂μ =
      ∫ ω in Aᶜ, (F ω - G ω) ∂μ := by
    calc
      (∫ ω, F ω ∂μ) - ∫ ω, G ω ∂μ = ∫ ω, (F ω - G ω) ∂μ := by
        rw [integral_sub hF hG]
      _ = (∫ ω in A, (F ω - G ω) ∂μ) +
          ∫ ω in Aᶜ, (F ω - G ω) ∂μ :=
        (integral_add_compl hA hH).symm
      _ = ∫ ω in Aᶜ, (F ω - G ω) ∂μ := by rw [hgood, zero_add]
  rw [htotal]
  have hnorm :
      ‖∫ ω in Aᶜ, (F ω - G ω) ∂μ‖ ≤
        (2 * B) * μ.real Aᶜ := by
    have hHB' : ∀ᵐ ω ∂μ, ω ∈ Aᶜ → ‖F ω - G ω‖ ≤ 2 * B :=
      hHB.mono (fun ω hω _ => hω)
    exact norm_setIntegral_le_of_norm_le_const_ae'
      (lt_top_iff_ne_top.mpr (measure_ne_top μ Aᶜ)) hHB'
  have hmul : (2 * B) * μ.real Aᶜ ≤ (2 * B) * δ := by
    exact mul_le_mul_of_nonneg_left hbad (by positivity)
  simpa only [Real.norm_eq_abs] using hnorm.trans hmul


/-! ## Crossing-index bridge

The next theorem is the reusable core for the paper's lower-rejection branch.
It takes the prefix cone and selector conclusions as hypotheses and derives the
native restart output from the reflected first-passage identity.  The remaining
localization theorem only has to prove these finite hypotheses on a good event.
-/

omit [MeasurableSpace Ω] in
theorem finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_of_cone_crossing
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J k : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) (hE : 0 ≤ E)
    (hN : 1 ≤ J - 1 + k)
    (hfit : nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) E 0 (J - 1 + k) 0)
    (hrej : ¬ nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) E 0 (J - 1 + k + 1) 0)
    (hls : nativeLeastSquares (Finset.Icc 1 (J - 1 + k)) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 ≤
        prefixCrossingSlope X r J ω)
    (hcone : nativeConeLower (Finset.Icc 1 (J - 1 + k))
      (Finset.nonempty_Icc.mpr hN) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 E =
        prefixCrossingSlope X r J ω)
    (ha : 0 < prefixCrossingSlope X r J ω)
    (hb : 0 < prefixCrossingLevel X E r J ω)
    (haE : prefixCrossingSlope X r J ω ≤ E)
    (hfail : nativeRestartNext X E (E-r) ω -
      prefixCrossingSlope X r J ω < -E) :
    nativeRestartLength X E (E-r) ω ≠ ⊤ ∧
      nativeRestartLengthNat X E (E-r) ω = J - 1 + k ∧
      nativeRestartSlope X E (E-r) ω = prefixCrossingSlope X r J ω ∧
      finiteMarginMap E (nativeRestartNext X E (E-r) ω) =
        prefixCrossingSubstitute X E r J ω := by
  let N : ℕ := J - 1 + k
  have hN' : N = J - 1 + k := rfl
  obtain ⟨hfinite, hlen, hslope⟩ := nativeRestartLength_and_slope_eq_of_prefix_cone
    X E (E-r) N ω hN hfit hrej hcone hls
  have hbridge := finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_of_lower_rejection
    X E r J k ω hJ hE hfinite (by simpa [N] using hlen) hslope ha hb haE hfail
  exact ⟨hfinite, by simpa [N] using hlen, hslope, hbridge⟩

/-! The lower-bridge event is measurable once the increment coordinates are
measurable.  This is a small interface lemma for applying the bounded-integral
estimate to that event; the pathwise bridge itself does not use regularity. -/

end SwingRepair
