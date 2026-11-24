import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.DistantBridge
import PLAStochastic.Swing.StationaryLimit.MarginKernel.WeakFeller
import PLAStochastic.ForMathlib.Probability.Kernel.Invariant.WeakLimit
import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.LeastSquares

/-!
# The finite-to-substitute local error bridge

This file records the measure-theoretic part of the distant-crossing argument.
The pathwise bridge in `DeterministicDistantBridge` identifies the native
finite-margin output with the prefix substitute on a good event.  Here we
turn that identification into an integral estimate, uniformly in the incoming
margin once the event and the substitute-law estimate are supplied.

No asymptotic probability statement is hidden in these lemmas: the only
probabilistic input is explicitly the mass of the bad event.  This is useful
because it separates the remaining strong-law/selector work from the already
formalized kernel algebra.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## A finite-prefix least-squares estimate with a bounded head -/

theorem nativeLeastSquares_Icc_const_add_bound_with_constant
    {N : ℕ} (hN : 1 ≤ N) {c η Q : ℝ} (_hη : 0 ≤ η) (_hQ : 0 ≤ Q)
    {W : ℕ → ℝ}
    (hW : ∀ i ∈ Finset.Icc 1 N,
      |W (i - 1)| ≤ Q + η * (i : ℝ)) :
    nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ))
        (fun i => c + W (i - 1)) 0 0 ≤
      3 * (c + Q) / (2 * (N : ℝ) + 1) + η := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hdenpos : 0 <
      (N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6 := by
    positivity
  have hsumW :
      |∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1)| ≤
        Q * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
          η * ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) := by
    calc
      |∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1)| ≤
          ∑ i ∈ Finset.Icc 1 N, |(i : ℝ) * W (i - 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Icc 1 N,
          (i : ℝ) * (Q + η * (i : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg i)]
        exact mul_le_mul_of_nonneg_left (hW i hi) (Nat.cast_nonneg i)
      _ = Q * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
          η * ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) := by
        have hsplit :
            (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (Q + η * (i : ℝ))) =
              (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * Q) +
                ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (η * (i : ℝ)) := by
          calc
            (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (Q + η * (i : ℝ))) =
                ∑ i ∈ Finset.Icc 1 N,
                  ((i : ℝ) * Q + (i : ℝ) * (η * (i : ℝ))) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * Q) +
                  ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (η * (i : ℝ)) := by
              rw [Finset.sum_add_distrib]
        have hQ :
            (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * Q) =
              Q * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) := by
          calc
            (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * Q) =
                ∑ i ∈ Finset.Icc 1 N, Q * (i : ℝ) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = Q * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) := by
              rw [Finset.mul_sum]
        have hη :
            (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (η * (i : ℝ))) =
              η * ∑ i ∈ Finset.Icc 1 N, (i : ℝ)^2 := by
          calc
            (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (η * (i : ℝ))) =
                ∑ i ∈ Finset.Icc 1 N, η * ((i : ℝ)^2) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = η * ∑ i ∈ Finset.Icc 1 N, (i : ℝ)^2 := by
              rw [Finset.mul_sum]
        rw [hsplit, hQ, hη, sum_Icc_one_cast_prefix,
          sum_Icc_one_sq_cast_prefix]
  rw [nativeLeastSquares_Icc_formula_closed]
  have hsumid :
      (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (c + W (i - 1))) =
        c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
          ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1) := by
    calc
      (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (c + W (i - 1))) =
          ∑ i ∈ Finset.Icc 1 N,
            ((i : ℝ) * c + (i : ℝ) * W (i - 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * c) +
          ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1) := by
        rw [Finset.sum_add_distrib]
      _ = c * (∑ i ∈ Finset.Icc 1 N, (i : ℝ)) +
          ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1) := by
        have hc :
            (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * c) =
              c * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) := by
          calc
            (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * c) =
                ∑ i ∈ Finset.Icc 1 N, c * (i : ℝ) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = c * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) := by
              rw [Finset.mul_sum]
        rw [hc]
      _ = _ := by rw [sum_Icc_one_cast_prefix]
  rw [hsumid]
  have hupper :
      ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1) ≤
        Q * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
          η * ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) :=
    (le_abs_self _).trans hsumW
  have hratio :
      (c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
        Q * ((N : ℝ) * ((N : ℝ) + 1) / 2)) /
          ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) =
        3 * (c + Q) / (2 * (N : ℝ) + 1) := by
    field_simp
    ring
  have hsplit :
      (c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
        ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1)) /
          ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) ≤
        (c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
          Q * ((N : ℝ) * ((N : ℝ) + 1) / 2)) /
            ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) + η := by
    have hnum :
        c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
            ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1) ≤
          c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
            Q * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
              η * ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) := by
      linarith [hupper]
    calc
      _ ≤
          (c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
            Q * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
              η * ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6)) /
            ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) :=
        div_le_div_of_nonneg_right hnum hdenpos.le
      _ =
          (c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
            Q * ((N : ℝ) * ((N : ℝ) + 1) / 2)) /
              ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) + η := by
        field_simp
  calc
    (c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
        ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1)) /
          ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) ≤
        (c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
          Q * ((N : ℝ) * ((N : ℝ) + 1) / 2)) /
            ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) + η := hsplit
    _ = 3 * (c + Q) / (2 * (N : ℝ) + 1) + η := by rw [hratio]

/-! The preceding estimate is stated for an explicit additive path
`c + W (i-1)`.  Native restart proofs naturally carry the same path through
`nativeCarriedSamples`; the following wrapper performs that identification
once and for all.  In particular, a lower-bridge certificate no longer needs
to carry the least-squares inequality as an independent hypothesis: it is a
deterministic consequence of its cumulative-sum envelope. -/

omit [MeasurableSpace Ω] in
theorem nativeLeastSquares_nativeCarried_Icc_const_add_bound
    {X : ℕ → Ω → ℝ} {N : ℕ} (hN : 1 ≤ N)
    {c η Q : ℝ} (hη : 0 ≤ η) (hQ : 0 ≤ Q) (ω : Ω)
    (hW : ∀ i ∈ Finset.Icc 1 N,
      |cumulativeSamples X (i - 1) ω| ≤ Q + η * (i : ℝ)) :
    nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ))
        (fun i => nativeCarriedSamples X (fun _ => c) i ω) 0 0 ≤
      3 * (c + Q) / (2 * (N : ℝ) + 1) + η := by
  have hls0 := nativeLeastSquares_Icc_const_add_bound_with_constant
    (N := N) (c := c) hN hη hQ (W := fun n => cumulativeSamples X n ω) hW
  have hls_eq :
      nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ))
          (fun i => nativeCarriedSamples X (fun _ => c) i ω) 0 0 =
        nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ))
          (fun i => c + cumulativeSamples X (i - 1) ω) 0 0 := by
    rw [nativeLeastSquares_Icc_formula_closed,
      nativeLeastSquares_Icc_formula_closed]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    simp [nativeCarriedSamples_succ]
  rw [hls_eq]
  exact hls0

/-! A small arithmetic bridge turns a lower bound on the accepted index into
the least-squares threshold used by the selector.  This is intentionally
deterministic: the lower-index inequality is left visible as an input, so a
later passage/localization theorem can discharge it without smuggling in a
probability claim. -/

theorem leastSquares_threshold_of_lower_index
    {a η c Q : ℝ} {L N : ℕ}
    (hηa : η ≤ a)
    (hineq : 3 * (c + Q) ≤ (a - η) * (2 * (L : ℝ) + 1))
    (hLN : L ≤ N) :
    3 * (c + Q) / (2 * (N : ℝ) + 1) + η ≤ a := by
  have hcoef : 0 ≤ a - η := sub_nonneg.mpr hηa
  have hcast : (2 * (L : ℝ) + 1) ≤ 2 * (N : ℝ) + 1 := by
    have hcast' : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLN
    linarith
  have hnum : 3 * (c + Q) ≤ (a - η) * (2 * (N : ℝ) + 1) := by
    exact hineq.trans (mul_le_mul_of_nonneg_left hcast hcoef)
  have hden : 0 < 2 * (N : ℝ) + 1 := by positivity
  have hfrac : 3 * (c + Q) / (2 * (N : ℝ) + 1) ≤ a - η := by
    exact (div_le_iff₀ hden).2 hnum
  linarith

omit [MeasurableSpace Ω] in
theorem prefixCrossingSlope_attained_lower_cone
    {X : ℕ → Ω → ℝ} {E r : ℝ} {J : ℕ} (hJ : 1 ≤ J) (ω : Ω) :
    ∃ i₀ ∈ Finset.Icc 1 J,
      slopeLower (i₀ : ℝ)
          (nativeCarriedSamples X (fun _ => E-r) i₀ ω) 0 0 E =
        prefixCrossingSlope X r J ω := by
  obtain ⟨n, hn, hval⟩ := swingEarlySlope_mem X r ω (J-1)
  let i₀ : ℕ := n + 1
  have hi₀ : i₀ ∈ Finset.Icc 1 J := by
    apply Finset.mem_Icc.mpr
    constructor <;> dsimp [i₀] <;> omega
  refine ⟨i₀, hi₀, ?_⟩
  rw [prefixCrossingSlope_eq_early (X := X) (r := r) (J := J) hJ]
  have hcar : nativeCarriedSamples X (fun _ => E-r) i₀ ω =
      E-r + cumulativeSamples X n ω := by
    dsimp [i₀]
    rw [nativeCarriedSamples_succ]
  rw [hcar]
  dsimp [slopeLower, swingSlopeTerm] at *
  rw [hval]
  dsimp [i₀]
  push_cast
  ring

omit [MeasurableSpace Ω] in
theorem slopeLower_nativeCarried_eq_swingSlopeTerm
    {X : ℕ → Ω → ℝ} {E r : ℝ} {i : ℕ} (hi : 1 ≤ i) (ω : Ω) :
    slopeLower (i : ℝ)
        (nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 E =
      swingSlopeTerm X r (i-1) ω := by
  have hcar : nativeCarriedSamples X (fun _ => E-r) i ω =
      E-r + cumulativeSamples X (i-1) ω := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    simp [nativeCarriedSamples_succ]
  rw [hcar]
  dsimp [slopeLower, swingSlopeTerm]
  have hcast : (i : ℝ) = ((i-1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ i)]
    norm_num
  rw [hcast]
  ring

/-! ## Random first-passage index

The fixed-index event in `PrefixCrossingSubstitute` is convenient for finite
algebra, but its probability is not the right asymptotic object: the crossing
index itself is random.  The following event uses the measurable random
passage index and therefore is the exact event to which a strong-law estimate
can be applied.
-/

def prefixCrossingPassageIndex (X : ℕ → Ω → ℝ) (E r : ℝ) (J : ℕ) : Ω → ℕ :=
  fun ω => gaussianWalkPassage
    (negIncrements (fun q => X (J-1+q)))
    (prefixCrossingSlope X r J ω)
    (prefixCrossingLevel X E r J ω) ω

def prefixCrossingLowerBridgeEventRandom
    (X : ℕ → Ω → ℝ) (E r : ℝ) (J : ℕ) : Set Ω :=
  {ω | nativeRestartLength X E (E-r) ω ≠ ⊤} ∩
    ({ω | nativeRestartLengthNat X E (E-r) ω =
        J-1+prefixCrossingPassageIndex X E r J ω} ∩
      ({ω | nativeRestartSlope X E (E-r) ω = prefixCrossingSlope X r J ω} ∩
        ({ω | 0 < prefixCrossingSlope X r J ω} ∩
          ({ω | 0 < prefixCrossingLevel X E r J ω} ∩
            ({ω | prefixCrossingSlope X r J ω ≤ E} ∩
              {ω | nativeRestartNext X E (E-r) ω -
                prefixCrossingSlope X r J ω < -E})))))

theorem prefixCrossingPassageIndex_measurable
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (E r : ℝ) (J : ℕ) :
    Measurable (prefixCrossingPassageIndex X E r J) := by
  unfold prefixCrossingPassageIndex
  apply gaussianWalkPassage_random_measurable
  · intro n
    exact (hX (J-1+n)).neg
  · exact prefixCrossingSlope_measurable hX r J
  · exact prefixCrossingLevel_measurable hX E r J

/-! The four restart-state coordinates are used by both the random-index and
fixed-index bridge events.  Build their pullback measurability once, sharing
the parameter/environment map, so the event proofs do not duplicate the
large native-restart selector terms. -/

theorem nativeRestartComponents_measurable
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (E x : ℝ) :
    Measurable (fun ω : Ω => nativeRestartLength X E x ω) ∧
    Measurable (fun ω : Ω => nativeRestartLengthNat X E x ω) ∧
    Measurable (fun ω : Ω => nativeRestartSlope X E x ω) ∧
    Measurable (fun ω : Ω => nativeRestartNext X E x ω) := by
  let hp : Measurable (fun ω : Ω => (x, ω)) :=
    (measurable_const (a := x)).prodMk measurable_id
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h0 := (nativeRestartLength_measurable X hX E).comp hp
    convert h0 using 1
    rfl
  · have h0 := (nativeRestartLengthNat_measurable X hX E).comp hp
    convert h0 using 1
    rfl
  · have h0 := (nativeRestartSlope_measurable X hX E).comp hp
    convert h0 using 1
    rfl
  · have h0 := (nativeRestartNext_measurable X hX E).comp hp
    convert h0 using 1
    rfl

set_option maxHeartbeats 10000000 in
theorem prefixCrossingLowerBridgeEventRandom_measurableSet
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (E r : ℝ) (J : ℕ) :
    MeasurableSet (prefixCrossingLowerBridgeEventRandom X E r J) := by
  let hk : Measurable (prefixCrossingPassageIndex X E r J) :=
    prefixCrossingPassageIndex_measurable hX E r J
  let hsum : Measurable (fun ω : Ω =>
      J-1 + prefixCrossingPassageIndex X E r J ω) :=
    (measurable_of_countable (f := fun n : ℕ => J-1+n)).comp hk
  have hcomponents := nativeRestartComponents_measurable (X := X) hX E (E-r)
  have hlen := hcomponents.1
  have hnat := hcomponents.2.1
  have hslopeN := hcomponents.2.2.1
  have hnext := hcomponents.2.2.2
  let hsl : Measurable (prefixCrossingSlope X r J) :=
    prefixCrossingSlope_measurable hX r J
  let hlev : Measurable (prefixCrossingLevel X E r J) :=
    prefixCrossingLevel_measurable hX E r J
  have h1 : MeasurableSet {ω : Ω |
      nativeRestartLength X E (E-r) ω ≠ (⊤ : WithTop ℕ)} := by
    exact (measurableSet_eq_fun hlen measurable_const).compl
  have h2 : MeasurableSet {ω : Ω |
      nativeRestartLengthNat X E (E-r) ω =
        J-1+prefixCrossingPassageIndex X E r J ω} :=
    measurableSet_eq_fun hnat hsum
  have h3 : MeasurableSet {ω : Ω |
      nativeRestartSlope X E (E-r) ω = prefixCrossingSlope X r J ω} :=
    measurableSet_eq_fun hslopeN hsl
  have h4 : MeasurableSet {ω : Ω |
      0 < prefixCrossingSlope X r J ω} :=
    measurableSet_lt measurable_const hsl
  have h5 : MeasurableSet {ω : Ω |
      0 < prefixCrossingLevel X E r J ω} :=
    measurableSet_lt measurable_const hlev
  have h6 : MeasurableSet {ω : Ω |
      prefixCrossingSlope X r J ω ≤ E} :=
    measurableSet_le hsl measurable_const
  have h7 : MeasurableSet {ω : Ω |
      nativeRestartNext X E (E-r) ω - prefixCrossingSlope X r J ω < -E} :=
    measurableSet_lt (hnext.sub hsl) measurable_const
  exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter h7)))))

omit [MeasurableSpace Ω] in
theorem finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_on_random_event
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) (hE : 0 ≤ E)
    (hω : ω ∈ prefixCrossingLowerBridgeEventRandom X E r J) :
    finiteMarginMap E (nativeRestartNext X E (E-r) ω) =
      prefixCrossingSubstitute X E r J ω := by
  rcases hω with ⟨hfinite, hlen, hslope, ha, hlevel, haE, hfail⟩
  exact finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_of_lower_rejection
    X E r J (prefixCrossingPassageIndex X E r J ω) ω hJ hE hfinite hlen hslope
    ha hlevel haE hfail

/-! The preceding event is the exact random-index version of the finite
bridge.  This wrapper is useful when the localization argument is phrased in
terms of a first-passage specification: all cone and least-squares hypotheses
are pointwise, while the passage index is allowed to remain random. -/

omit [MeasurableSpace Ω] in
theorem prefixCrossingLowerBridgeEventRandom_of_first_crossing_bounds
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J k : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) (hE : 0 ≤ E) (hN : 1 ≤ J - 1 + k)
    (hprefix : feasibleSlope (Finset.Icc 1 (J-1)) (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 E
      (prefixCrossingSlope X r J ω))
    (hlower_future : ∀ i ∈ Finset.Icc J (J - 1 + k),
      slopeLower (i : ℝ) (nativeCarriedSamples X (fun _ => E-r) i ω)
        0 0 E ≤ prefixCrossingSlope X r J ω)
    (hi₀ : ∃ i₀ ∈ Finset.Icc 1 J,
      slopeLower (i₀ : ℝ) (nativeCarriedSamples X (fun _ => E-r) i₀ ω)
        0 0 E = prefixCrossingSlope X r J ω)
    (hls : nativeLeastSquares (Finset.Icc 1 (J - 1 + k))
      (fun i => (i : ℝ))
      (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 ≤
      prefixCrossingSlope X r J ω)
    (ha : 0 < prefixCrossingSlope X r J ω)
    (hb : 0 < prefixCrossingLevel X E r J ω)
    (haE : prefixCrossingSlope X r J ω ≤ E)
    (hcross : ∃ m : ℕ,
      prefixCrossingLevel X E r J ω <
        gaussianDriftWalk
          (negIncrements (fun q => X (J - 1 + q))) 0
          (prefixCrossingSlope X r J ω) m ω)
    (hpass : gaussianWalkPassage
        (negIncrements (fun q => X (J - 1 + q)))
        (prefixCrossingSlope X r J ω)
        (prefixCrossingLevel X E r J ω) ω = k) :
    ω ∈ prefixCrossingLowerBridgeEventRandom X E r J := by
  have hspec := gaussianWalkPassage_eq_index_spec
    (Y := negIncrements (fun q => X (J - 1 + q)))
    (a := prefixCrossingSlope X r J ω)
    (b := prefixCrossingLevel X E r J ω) (ω := ω) k hcross hpass
  have hbefore : ∀ j < k,
      gaussianDriftWalk (negIncrements (fun q => X (J - 1 + q))) 0
        (prefixCrossingSlope X r J ω) j ω ≤
        prefixCrossingLevel X E r J ω := hspec.2
  have hcross' := prefixCrossingLevel_lt_of_reflected_crossing
    X E r J k ω hspec.1
  have hpath :=
    finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_of_first_crossing_bounds
      X E r J k ω hJ hE rfl hN hprefix hlower_future hi₀ hbefore hcross'
      hls ha hb haE
  rcases hpath with ⟨hfinite, hlen, hslope, _hmap⟩
  have hfail : nativeRestartNext X E (E-r) ω -
      prefixCrossingSlope X r J ω < -E := by
    rw [nativeRestartNext, hlen, hslope]
    have hshift : cumulativeSamples X (J - 1 + k) ω =
        cumulativeSamples X (J - 1) ω +
          cumulativeSamples (fun q => X (J - 1 + q)) k ω := by
      exact cumulativeSamples_shifted_succ X J k hJ ω
    rw [hshift]
    dsimp [prefixCrossingLevel] at hcross'
    have hcast : ((J - 1 + k : ℕ) : ℝ) =
        (J : ℝ) - 1 + (k : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub hJ]
      ring
    rw [hcast]
    linarith
  refine ⟨hfinite, ?_, hslope, ha, hb, haE, hfail⟩
  change nativeRestartLengthNat X E (E-r) ω =
    J - 1 + gaussianWalkPassage
      (negIncrements (fun q => X (J - 1 + q)))
      (prefixCrossingSlope X r J ω)
      (prefixCrossingLevel X E r J ω) ω
  rw [hpass]
  exact hlen

/-! The lower-cone inequalities after the frozen prefix are already a
deterministic consequence of the early-slope localization event.  Isolating
this step removes one of the directional conditions from the probabilistic
bridge input: only the first-passage and least-squares checks remain. -/

omit [MeasurableSpace Ω] in
theorem prefixCrossing_lower_future_of_earlySlopeGood
    {X : ℕ → Ω → ℝ} {E r K δ M : ℝ} {J N : ℕ} (ω : Ω)
    (hJ : 1 ≤ J) (_hN : J ≤ N) (hδ : 0 < δ)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J-1))
    (hr : |r| ≤ K) :
    ∀ i ∈ Finset.Icc J N,
      slopeLower (i : ℝ) (nativeCarriedSamples X (fun _ => E-r) i ω)
        0 0 E ≤ prefixCrossingSlope X r J ω := by
  have hloc := swingEarlySlope_localization (X := X) (K₀ := K)
    (δ := δ) (M := M) (J := J-1) hδ hgood hr
  have hδA : δ ≤ prefixCrossingSlope X r J ω := by
    rw [prefixCrossingSlope_eq_early (X := X) (r := r) (J := J) hJ]
    rw [← hloc.1]
    linarith [hloc.2.1]
  intro i hi
  have hiJ : J ≤ i := (Finset.mem_Icc.mp hi).1
  have hiN : i ≤ N := (Finset.mem_Icc.mp hi).2
  have hi1 : 1 ≤ i := hJ.trans hiJ
  have hterm := slopeLower_nativeCarried_eq_swingSlopeTerm
    (X := X) (E := E) (r := r) hi1 ω
  rw [hterm]
  rw [prefixCrossingSlope_eq_early (X := X) (r := r) (J := J) hJ]
  by_cases heq : i = J
  · subst i
    exact swingSlopeTerm_le_swingEarlySlope X r ω (by omega)
  · by_cases hni : i - 1 ≤ J - 1
    · exact swingSlopeTerm_le_swingEarlySlope X r ω hni
    · have htail := (swingSlopeTerm_le_tail X hr (i-1) ω)
      have hgoodtail : swingSlopeTail X K (i-1) ω < δ :=
        hgood.2.2 (i-1) (by omega)
      linarith

/-! A more operational version packages the two finite localization checks
usually produced by the strong-law event.  The prefix budget inequality gives
the upper cone on the first `J-1` observations, while the linear envelope gives
the constrained least-squares bound.  The future lower-cone and first-passage
conditions are kept explicit: these are exactly the directional/selector
conditions that must be supplied by the renewal localization argument. -/

omit [MeasurableSpace Ω] in
theorem prefixCrossingLowerBridgeEventRandom_of_envelopes
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J k : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) (hE : 0 ≤ E) (hN : 1 ≤ J - 1 + k)
    {K Q M η : ℝ}
    (hr : |r| ≤ K) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hA : prefixCrossingSlope X r J ω ≤ M)
    (hWprefix : ∀ i ∈ Finset.Icc 1 (J-1),
      |cumulativeSamples X (i-1) ω| ≤ Q)
    (hbudget : M * (J : ℝ) ≤ 2*E - K - Q)
    (hWglobal : ∀ i ∈ Finset.Icc 1 (J - 1 + k),
      |cumulativeSamples X (i-1) ω| ≤ Q + η * (i : ℝ))
    (hlsbound : 3 * (E-r+Q) /
        (2 * ((J - 1 + k : ℕ) : ℝ) + 1) + η ≤
      prefixCrossingSlope X r J ω)
    (hlower_future : ∀ i ∈ Finset.Icc J (J - 1 + k),
      slopeLower (i : ℝ) (nativeCarriedSamples X (fun _ => E-r) i ω)
        0 0 E ≤ prefixCrossingSlope X r J ω)
    (hi₀ : ∃ i₀ ∈ Finset.Icc 1 J,
      slopeLower (i₀ : ℝ) (nativeCarriedSamples X (fun _ => E-r) i₀ ω)
        0 0 E = prefixCrossingSlope X r J ω)
    (ha : 0 < prefixCrossingSlope X r J ω)
    (hb : 0 < prefixCrossingLevel X E r J ω)
    (haE : prefixCrossingSlope X r J ω ≤ E)
    (hcross : ∃ m : ℕ,
      prefixCrossingLevel X E r J ω <
        gaussianDriftWalk
          (negIncrements (fun q => X (J - 1 + q))) 0
          (prefixCrossingSlope X r J ω) m ω)
    (hpass : gaussianWalkPassage
        (negIncrements (fun q => X (J - 1 + q)))
        (prefixCrossingSlope X r J ω)
        (prefixCrossingLevel X E r J ω) ω = k) :
    ω ∈ prefixCrossingLowerBridgeEventRandom X E r J := by
  have hprefix := prefixCrossingSlope_feasible_prefix_of_prefix_bound
    (X := X) E r K Q M J ω hJ hr hK hQ hM hA hWprefix hbudget
  have hls0 := nativeLeastSquares_Icc_const_add_bound_with_constant
    (N := J - 1 + k) (c := E-r) hN hη hQ
    (W := fun n => cumulativeSamples X n ω) hWglobal
  have hls_eq :
      nativeLeastSquares (Finset.Icc 1 (J - 1 + k))
          (fun i => (i : ℝ))
          (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 =
        nativeLeastSquares (Finset.Icc 1 (J - 1 + k))
          (fun i => (i : ℝ))
          (fun i => (E-r) + cumulativeSamples X (i-1) ω) 0 0 := by
    rw [nativeLeastSquares_Icc_formula_closed,
      nativeLeastSquares_Icc_formula_closed]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    simp [nativeCarriedSamples_succ]
  have hls :
      nativeLeastSquares (Finset.Icc 1 (J - 1 + k))
          (fun i => (i : ℝ))
          (fun i => nativeCarriedSamples X (fun _ => E-r) i ω) 0 0 ≤
        prefixCrossingSlope X r J ω := by
    rw [hls_eq]
    exact hls0.trans hlsbound
  exact prefixCrossingLowerBridgeEventRandom_of_first_crossing_bounds
    (X := X) E r J k ω hJ hE hN hprefix hlower_future hi₀ hls ha hb haE hcross hpass

/-! The path-integral identity is placed before the random-event estimate so
that the latter can use it without a forward declaration. -/

theorem nativeFiniteMarginKernel_integral_eq_pre
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (E r : ℝ)
    {f : ℝ → ℝ} (hf : Measurable f)
    (_hint : Integrable f (nativeFiniteMarginKernel X μ E r)) :
    (∫ y, f y ∂(nativeFiniteMarginKernel X μ E r)) =
      ∫ ω, f (finiteMarginMap E
        (nativeRestartNext X E (finiteMarginSection E r) ω)) ∂μ := by
  rw [nativeFiniteMarginKernel_apply hX E r]
  have hnext : Measurable (fun ω =>
      finiteMarginMap E (nativeRestartNext X E (finiteMarginSection E r) ω)) :=
    (measurable_finiteMarginMap E).comp
      ((nativeRestartNext_measurable X hX E).comp
        ((measurable_const (a := finiteMarginSection E r)).prodMk measurable_id))
  have hnext0 : Measurable (fun ω =>
      nativeRestartNext X E (finiteMarginSection E r) ω) :=
    (nativeRestartNext_measurable X hX E).comp
      ((measurable_const (a := finiteMarginSection E r)).prodMk measurable_id)
  have hrestart : nativeRestartKernel X μ E (finiteMarginSection E r) =
      Measure.map (fun ω => nativeRestartNext X E (finiteMarginSection E r) ω) μ := by
    apply Measure.ext
    intro A hA
    rw [nativeRestartKernel_apply hX E (finiteMarginSection E r) hA,
      Measure.map_apply hnext0 hA]
    rfl
  rw [hrestart, Measure.map_map (measurable_finiteMarginMap E) hnext0]
  exact MeasureTheory.integral_map hnext.aemeasurable hf.aestronglyMeasurable

theorem nativeFiniteMarginKernel_integral_sub_prefixCrossingSubstitute_of_randomBridge
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ] [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (E r : ℝ) (J : ℕ)
    (hJ : 1 ≤ J) (hE : 0 ≤ E)
    {f : ℝ → ℝ} {B δ : ℝ} (hf : Measurable f) (hB : 0 ≤ B)
    (hfB : ∀ y, |f y| ≤ B) (hδ : 0 ≤ δ)
    (hbad : μ.real (prefixCrossingLowerBridgeEventRandom X E r J)ᶜ ≤ δ) :
    |(∫ y, f y ∂(nativeFiniteMarginKernel X μ E r)) -
        ∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ| ≤
      2 * B * δ := by
  have hK : IsMarkovKernel (nativeFiniteMarginKernel X μ E) :=
    nativeFiniteMarginKernel_isMarkov hX E
  haveI : IsMarkovKernel (nativeFiniteMarginKernel X μ E) := hK
  have hKint : Integrable f (nativeFiniteMarginKernel X μ E r) :=
    integrable_of_bounded hf hfB
  have hF : Measurable (fun ω =>
      f (finiteMarginMap E (nativeRestartNext X E (E-r) ω))) :=
    hf.comp ((measurable_finiteMarginMap E).comp
      ((nativeRestartNext_measurable X hX E).comp
        ((measurable_const (a := E-r)).prodMk measurable_id)))
  have hG : Measurable (fun ω =>
      f (prefixCrossingSubstitute X E r J ω)) :=
    hf.comp (prefixCrossingSubstitute_measurable hX E r J)
  have hFI : Integrable (fun ω =>
      f (finiteMarginMap E (nativeRestartNext X E (E-r) ω))) μ :=
    (integrable_const B).mono' hF.aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs]
        exact hfB _))
  have hGI : Integrable (fun ω =>
      f (prefixCrossingSubstitute X E r J ω)) μ :=
    (integrable_const B).mono' hG.aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs]
        exact hfB _))
  have hFA : ∀ᵐ ω ∂μ, |f (finiteMarginMap E
      (nativeRestartNext X E (E-r) ω))| ≤ B :=
    Eventually.of_forall (fun ω => hfB _)
  have hGA : ∀ᵐ ω ∂μ, |f (prefixCrossingSubstitute X E r J ω)| ≤ B :=
    Eventually.of_forall (fun ω => hfB _)
  have hEq :
      EqOn
        (fun ω => f (finiteMarginMap E (nativeRestartNext X E (E-r) ω)))
        (fun ω => f (prefixCrossingSubstitute X E r J ω))
        (prefixCrossingLowerBridgeEventRandom X E r J) := by
    intro ω hω
    change f (finiteMarginMap E (nativeRestartNext X E (E-r) ω)) =
      f (prefixCrossingSubstitute X E r J ω)
    exact congrArg f
      (finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_on_random_event
        (X := X) E r J ω hJ hE hω)
  have hbound := integral_sub_le_of_eqOn_event_of_bounded
    (μ := μ) (A := prefixCrossingLowerBridgeEventRandom X E r J)
    (prefixCrossingLowerBridgeEventRandom_measurableSet hX E r J)
    hFI hGI hFA hGA hEq hbad hB hδ
  rw [nativeFiniteMarginKernel_integral_eq_pre hX E r hf hKint]
  exact hbound

/-! ## A bounded integral estimate on a good event -/

theorem abs_integral_sub_le_of_eq_on_event
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u v : Ω → ℝ} {B : ℝ}
    (hu : Measurable u) (hv : Measurable v) (_hB : 0 ≤ B)
    (huB : ∀ ω, |u ω| ≤ B) (hvB : ∀ ω, |v ω| ≤ B)
    {G : Set Ω} (hG : MeasurableSet G)
    (heq : ∀ᵐ ω ∂μ, ω ∈ G → u ω = v ω) :
    |(∫ ω, u ω ∂μ) - ∫ ω, v ω ∂μ| ≤ 2 * B * (μ.real Gᶜ) := by
  have huI : Integrable u μ := by
    exact (integrable_const B).mono' hu.aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs]
        exact huB ω))
  have hvI : Integrable v μ := by
    exact (integrable_const B).mono' hv.aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs]
        exact hvB ω))
  have hdiffI : Integrable (fun ω => u ω - v ω) μ := huI.sub hvI
  have hbadI : Integrable (Gᶜ.indicator (fun _ : Ω => (2 * B : ℝ))) μ := by
    exact (integrable_const (2 * B)).indicator hG.compl
  have hpoint : ∀ᵐ ω ∂μ,
      |u ω - v ω| ≤ Gᶜ.indicator (fun _ : Ω => (2 * B : ℝ)) ω := by
    filter_upwards [heq] with ω hω
    by_cases hmem : ω ∈ G
    · have he := hω hmem
      rw [Set.indicator_of_notMem (show ω ∉ Gᶜ by
        intro hbad
        exact hbad hmem)]
      rw [he]
      simp
    · rw [Set.indicator_of_mem (show ω ∈ Gᶜ by exact hmem)]
      have htri : |u ω - v ω| ≤ |u ω| + |v ω| := abs_sub _ _
      linarith [huB ω, hvB ω]
  have hbadval : (∫ ω, Gᶜ.indicator (fun _ : Ω => (2 * B : ℝ)) ω ∂μ) =
      2 * B * (μ.real Gᶜ) := by
    rw [integral_indicator hG.compl]
    · rw [integral_const, Measure.real]
      rw [Measure.restrict_apply_univ]
      simp only [smul_eq_mul, Measure.real]
      ring
  calc
    |(∫ ω, u ω ∂μ) - ∫ ω, v ω ∂μ| =
        |∫ ω, (u ω - v ω) ∂μ| := by rw [integral_sub huI hvI]
    _ ≤ ∫ ω, |u ω - v ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, Gᶜ.indicator (fun _ : Ω => (2 * B : ℝ)) ω ∂μ :=
      integral_mono_ae hdiffI.norm hbadI hpoint
    _ = 2 * B * (μ.real Gᶜ) := hbadval

/-! ## Native finite-kernel integrals as path integrals -/

theorem nativeFiniteMarginKernel_integral_eq
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (E r : ℝ)
    {f : ℝ → ℝ} (hf : Measurable f)
    (_hint : Integrable f (nativeFiniteMarginKernel X μ E r)) :
    (∫ y, f y ∂(nativeFiniteMarginKernel X μ E r)) =
      ∫ ω, f (finiteMarginMap E
        (nativeRestartNext X E (finiteMarginSection E r) ω)) ∂μ := by
  rw [nativeFiniteMarginKernel_apply hX E r]
  have hnext : Measurable (fun ω =>
      finiteMarginMap E (nativeRestartNext X E (finiteMarginSection E r) ω)) :=
    (measurable_finiteMarginMap E).comp
      ((nativeRestartNext_measurable X hX E).comp
        ((measurable_const (a := finiteMarginSection E r)).prodMk measurable_id))
  have hnext0 : Measurable (fun ω =>
      nativeRestartNext X E (finiteMarginSection E r) ω) :=
    (nativeRestartNext_measurable X hX E).comp
      ((measurable_const (a := finiteMarginSection E r)).prodMk measurable_id)
  have hrestart : nativeRestartKernel X μ E (finiteMarginSection E r) =
      Measure.map (fun ω => nativeRestartNext X E (finiteMarginSection E r) ω) μ := by
    apply Measure.ext
    intro A hA
    rw [nativeRestartKernel_apply hX E (finiteMarginSection E r) hA,
      Measure.map_apply hnext0 hA]
    rfl
  rw [hrestart, Measure.map_map (measurable_finiteMarginMap E) hnext0]
  exact MeasureTheory.integral_map hnext.aemeasurable hf.aestronglyMeasurable

/-! The finite bridge event is measurable.  We spell out the seven scalar
conditions instead of asking simplification to unfold the whole predicate;
this keeps elaboration predictable for the large restart-state expressions. -/

set_option maxHeartbeats 10000000 in
theorem prefixCrossingLowerBridgeEvent_measurableSet
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (E r : ℝ) (J k : ℕ) :
    MeasurableSet (prefixCrossingLowerBridgeEvent X E r J k) := by
  have hcomponents := nativeRestartComponents_measurable (X := X) hX E (E-r)
  have hlen := hcomponents.1
  have hnat := hcomponents.2.1
  have hslopeN := hcomponents.2.2.1
  have hnext := hcomponents.2.2.2
  let hsl : Measurable (prefixCrossingSlope X r J) :=
    prefixCrossingSlope_measurable hX r J
  let hlev : Measurable (prefixCrossingLevel X E r J) :=
    prefixCrossingLevel_measurable hX E r J
  have h1 : MeasurableSet {ω : Ω |
      nativeRestartLength X E (E-r) ω ≠ (⊤ : WithTop ℕ)} := by
    exact (measurableSet_eq_fun hlen measurable_const).compl
  have h2 : MeasurableSet {ω : Ω |
      nativeRestartLengthNat X E (E-r) ω = J-1+k} :=
    measurableSet_eq_fun hnat measurable_const
  have h3 : MeasurableSet {ω : Ω |
      nativeRestartSlope X E (E-r) ω = prefixCrossingSlope X r J ω} :=
    measurableSet_eq_fun hslopeN hsl
  have h4 : MeasurableSet {ω : Ω |
      0 < prefixCrossingSlope X r J ω} :=
    measurableSet_lt measurable_const hsl
  have h5 : MeasurableSet {ω : Ω |
      0 < prefixCrossingLevel X E r J ω} :=
    measurableSet_lt measurable_const hlev
  have h6 : MeasurableSet {ω : Ω |
      prefixCrossingSlope X r J ω ≤ E} :=
    measurableSet_le hsl measurable_const
  have h7 : MeasurableSet {ω : Ω |
      nativeRestartNext X E (E-r) ω - prefixCrossingSlope X r J ω < -E} :=
    measurableSet_lt (hnext.sub hsl) measurable_const
  exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter h7)))))

/-! ## The pathwise bridge gives a finite-kernel error bound -/

theorem nativeFiniteMarginKernel_integral_sub_prefixCrossingSubstitute_le
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ] [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (E r : ℝ) (J _k : ℕ)
    (_hJ : 1 ≤ J) (_hE : 0 ≤ E)
    {f : ℝ → ℝ} {B : ℝ} (hf : Measurable f) (hB : 0 ≤ B)
    (hfB : ∀ y, |f y| ≤ B)
    {G : Set Ω} (hG : MeasurableSet G)
    (hbridge : ∀ᵐ ω ∂μ, ω ∈ G →
      finiteMarginMap E (nativeRestartNext X E (E-r) ω) =
        prefixCrossingSubstitute X E r J ω)
    (hsection : finiteMarginSection E r = E-r) :
    |(∫ y, f y ∂(nativeFiniteMarginKernel X μ E r)) -
        ∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ| ≤
      2 * B * (μ.real Gᶜ) := by
  have hK : IsMarkovKernel (nativeFiniteMarginKernel X μ E) :=
    nativeFiniteMarginKernel_isMarkov hX E
  haveI : IsMarkovKernel (nativeFiniteMarginKernel X μ E) := hK
  have hKint : Integrable f (nativeFiniteMarginKernel X μ E r) :=
    integrable_of_bounded hf hfB
  have hnative : Measurable (fun ω =>
      f (finiteMarginMap E (nativeRestartNext X E (finiteMarginSection E r) ω))) :=
    hf.comp ((measurable_finiteMarginMap E).comp
      ((nativeRestartNext_measurable X hX E).comp
        ((measurable_const (a := finiteMarginSection E r)).prodMk measurable_id)))
  have hsub : Measurable (fun ω => f (prefixCrossingSubstitute X E r J ω)) :=
    hf.comp (prefixCrossingSubstitute_measurable hX E r J)
  have hsec : (fun ω => f (finiteMarginMap E
      (nativeRestartNext X E (finiteMarginSection E r) ω))) =ᵐ[μ]
      (fun ω => f (finiteMarginMap E
        (nativeRestartNext X E (E-r) ω))) := by
    rw [hsection]
  have hnativeB : ∀ ω, |f (finiteMarginMap E
      (nativeRestartNext X E (finiteMarginSection E r) ω))| ≤ B :=
    fun ω => hfB _
  have hsubB : ∀ ω, |f (prefixCrossingSubstitute X E r J ω)| ≤ B :=
    fun ω => hfB _
  have hbridge' : ∀ᵐ ω ∂μ, ω ∈ G →
      f (finiteMarginMap E (nativeRestartNext X E (finiteMarginSection E r) ω)) =
        f (prefixCrossingSubstitute X E r J ω) := by
    filter_upwards [hbridge, hsec] with ω hω hωsec hmem
    rw [hωsec, hω hmem]
  rw [nativeFiniteMarginKernel_integral_eq hX E r hf hKint]
  exact abs_integral_sub_le_of_eq_on_event hnative hsub hB hnativeB hsubB hG hbridge'

/-! A ready-to-use specialization: the good set is exactly the lower-bridge
event, so the only remaining input is its bad-mass estimate. -/

theorem nativeFiniteMarginKernel_integral_sub_prefixCrossingSubstitute_of_lowerBridge
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ] [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (E r : ℝ) (J k : ℕ)
    (hJ : 1 ≤ J) (hE : 0 ≤ E)
    {f : ℝ → ℝ} {B δ : ℝ} (hf : Measurable f) (hB : 0 ≤ B)
    (hfB : ∀ y, |f y| ≤ B) (hδ : 0 ≤ δ)
    (hbad : μ.real (prefixCrossingLowerBridgeEvent X E r J k)ᶜ ≤ δ) :
    |(∫ y, f y ∂(nativeFiniteMarginKernel X μ E r)) -
        ∫ ω, f (prefixCrossingSubstitute X E r J ω) ∂μ| ≤
      2 * B * δ := by
  have hK : IsMarkovKernel (nativeFiniteMarginKernel X μ E) :=
    nativeFiniteMarginKernel_isMarkov hX E
  haveI : IsMarkovKernel (nativeFiniteMarginKernel X μ E) := hK
  have hKint : Integrable f (nativeFiniteMarginKernel X μ E r) :=
    integrable_of_bounded hf hfB
  have hF : Measurable (fun ω =>
      f (finiteMarginMap E (nativeRestartNext X E (E-r) ω))) :=
    hf.comp ((measurable_finiteMarginMap E).comp
      ((nativeRestartNext_measurable X hX E).comp
        ((measurable_const (a := E-r)).prodMk measurable_id)))
  have hG : Measurable (fun ω =>
      f (prefixCrossingSubstitute X E r J ω)) :=
    hf.comp (prefixCrossingSubstitute_measurable hX E r J)
  have hFI : Integrable (fun ω =>
      f (finiteMarginMap E (nativeRestartNext X E (E-r) ω))) μ :=
    (integrable_const B).mono' hF.aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs]
        exact hfB _))
  have hGI : Integrable (fun ω =>
      f (prefixCrossingSubstitute X E r J ω)) μ :=
    (integrable_const B).mono' hG.aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs]
        exact hfB _))
  have hFA : ∀ᵐ ω ∂μ, |f (finiteMarginMap E
      (nativeRestartNext X E (E-r) ω))| ≤ B :=
    Eventually.of_forall (fun ω => hfB _)
  have hGA : ∀ᵐ ω ∂μ, |f (prefixCrossingSubstitute X E r J ω)| ≤ B :=
    Eventually.of_forall (fun ω => hfB _)
  have hEq : EqOn
      (fun ω => f (finiteMarginMap E (nativeRestartNext X E (E-r) ω)))
      (fun ω => f (prefixCrossingSubstitute X E r J ω))
      (prefixCrossingLowerBridgeEvent X E r J k) := by
    intro ω hω
    have hpath := finiteMarginMap_nativeRestartNext_eq_prefixCrossingSubstitute_on_event
      X E r J k ω hJ hE hω
    change f (finiteMarginMap E (nativeRestartNext X E (E-r) ω)) =
      f (prefixCrossingSubstitute X E r J ω)
    rw [hpath]
  have hbound := integral_sub_le_of_eqOn_event_of_bounded
    (μ := μ) (A := prefixCrossingLowerBridgeEvent X E r J k)
    (prefixCrossingLowerBridgeEvent_measurableSet hX E r J k)
    hFI hGI hFA hGA hEq hbad hB hδ
  rw [nativeFiniteMarginKernel_integral_eq hX E r hf hKint]
  exact hbound

/-! ## Final reduction to the two genuinely probabilistic estimates

This theorem is the exact interface needed by Theorem 4.3.  Its hypothesis is
not the kernel convergence conclusion in disguise: it asks separately for a
uniform bad-mass estimate for the random lower-bridge event and for a uniform
renewal/substitute estimate.  The proof then consists only of the pathwise
bridge and a two-term triangle inequality.
-/

theorem nativeFiniteMarginKernel_compact_uniform_of_randomBridge
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    {ι : Type*} {l : Filter ι} [l.NeBot] {budget : ι → ℝ}
    (hinputs : ∀ (f : ℝ → ℝ) (L B : ℝ), KernelLimit.IsBddLip f L B →
      ∀ (C ε : ℝ), 0 < ε →
      ∃ J : ℕ, ∃ δ : ℝ,
        1 ≤ J ∧ 0 ≤ δ ∧ 2 * B * δ ≤ ε / 2 ∧
        ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
          0 ≤ budget i ∧
          μ.real (prefixCrossingLowerBridgeEventRandom X (budget i) r J)ᶜ ≤ δ ∧
          |(∫ ω, f (prefixCrossingSubstitute X (budget i) r J ω) ∂μ) -
            ∫ y, f y ∂(swingMarginKernel X μ r)| ≤ ε / 2) :
    ∀ (f : ℝ → ℝ) (L B : ℝ), KernelLimit.IsBddLip f L B →
      ∀ (C ε : ℝ), 0 < ε →
        ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
          |(∫ y, f y ∂(nativeFiniteMarginKernel X μ (budget i) r)) -
            (∫ y, f y ∂(swingMarginKernel X μ r))| ≤ ε := by
  haveI : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  intro f L B hf C ε hε
  obtain ⟨J, δ, hJ, hδ, hsplit, hevent⟩ := hinputs f L B hf C ε hε
  filter_upwards [hevent] with i hi_event
  intro r hr
  obtain ⟨hE, hbad, hsub⟩ := hi_event r hr
  have hB : 0 ≤ B := le_trans (abs_nonneg (f 0)) (hf.bdd 0)
  have hbridge := nativeFiniteMarginKernel_integral_sub_prefixCrossingSubstitute_of_randomBridge
    (X := X) (μ := μ) hX (budget i) r J hJ hE hf.meas hB hf.bdd hδ hbad
  let A : ℝ := ∫ y, f y ∂(nativeFiniteMarginKernel X μ (budget i) r)
  let S : ℝ := ∫ ω, f (prefixCrossingSubstitute X (budget i) r J ω) ∂μ
  let K : ℝ := ∫ y, f y ∂(swingMarginKernel X μ r)
  have hid : A - K = (A - S) + (S - K) := by ring
  rw [show |A - K| = |(A - S) + (S - K)| by rw [hid]]
  calc
    |(A - S) + (S - K)| ≤ |A - S| + |S - K| := abs_add_le _ _
    _ ≤ ε := by
      have h₁₀ : |A - S| ≤ 2 * B * δ := by
        simpa [A, S] using hbridge
      have h₁ : |A - S| ≤ ε / 2 := h₁₀.trans hsplit
      have h₂ : |S - K| ≤ ε / 2 := by simpa [S, K] using hsub
      linarith

end SwingRepair
