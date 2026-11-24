import PLAStochastic.Swing.Ladder.Renewal.StationaryIdentity

/-!
# Feasibility gate for the uniform Blackwell argument

Before implementing the long Blackwell proof, this file settles the four
points where the informal plan could be wrong.

1. **Direction.**  The renewal relation for the window mass
   `W(u) = U((u-x, u])` is proved literally from `U = ∑ ν^{*n}`; it comes out
   *backward*, `W(u) = 1_{0 ∈ (u-x,u]} + ∫ W(u-h) dν(h)`.  No reflection is
   used anywhere.

2. **Boundary-safe iteration.**  The `m`-fold version is *not* the naive
   `W(b) = ∫ W(b-y) dν^{*m}(y)`: the renewal atom at `0` contributes.  The
   exact global identity with its explicit correction term is
   `ladderRenewalMeasure_Ioc_split`, which is proved by splitting the renewal
   series at index `m` rather than by iterating the renewal equation, so no
   intermediate-position side condition is needed at all.  The correction is
   `∑_{j<m} ν^{*j}((b-x,b])`, which is `0` for no `b` but tends to `0` as
   `b → ∞` at fixed `m`; a uniform bound for it is `renewalWindowCorrection_le`.

3. **No attained maximum.**  The supremum `L(β) = sSup (W '' Ici β)` is only
   approached: `exists_near_window_sSup` gives `b* ≥ β` with
   `L(β) - ε ≤ W(b*)`.  Every later statement is phrased with this
   `ε`-approximation.

4. **Finite-`m` test theorem.**  `window_deficit_integral_eq` is the real-valued
   deficit identity at a fixed `m`, with the boundary correction carried
   explicitly.  It compiles before any Irwin--Hall or pigeonhole work.

The `m = 0` boundary of `LadderPostPassage` is a different issue (the
"never crosses" event cannot use prefix independence) and is untouched here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-! ## Convolution acting on a window -/

theorem measure_conv_Ioc (ρ ν : Measure ℝ) [SFinite ρ] [SFinite ν] (c d : ℝ) :
    (ρ ∗ ν) (Ioc c d) = ∫⁻ y, ρ (Ioc (c - y) (d - y)) ∂ν := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ∈ Ioc c d} :=
    measurableSet_Ioc.preimage (measurable_fst.add measurable_snd)
  have hmap : (ρ ∗ ν) (Ioc c d) = (ρ.prod ν) {p : ℝ × ℝ | p.1 + p.2 ∈ Ioc c d} := by
    rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Ioc]
    rfl
  rw [hmap, Measure.prod_apply_symm hS]
  refine lintegral_congr fun y => ?_
  congr 1
  ext s
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

theorem measurable_measure_Ioc_shift (ρ : Measure ℝ) [SFinite ρ] (c d : ℝ) :
    Measurable (fun y : ℝ => ρ (Ioc (c - y) (d - y))) := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ∈ Ioc c d} :=
    measurableSet_Ioc.preimage (measurable_fst.add measurable_snd)
  have hbase := measurable_measure_prodMk_left (ν := ρ) hS
  have hEq : (fun y : ℝ => ρ (Ioc (c - y) (d - y))) =
      fun y : ℝ => ρ (Prod.mk y ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ∈ Ioc c d}) := by
    funext y
    congr 1
    ext s
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  rw [hEq]
  exact hbase

/-! ## Splitting the convolution powers -/

theorem measureConvPow_add (ν : Measure ℝ) [SFinite ν] (m k : ℕ) :
    measureConvPow ν (m + k) = measureConvPow ν k ∗ measureConvPow ν m := by
  induction k with
  | zero =>
    rw [Nat.add_zero, measureConvPow_zero]
    exact (Measure.dirac_zero_conv _).symm
  | succ k ih =>
    have hstep : m + (k + 1) = (m + k) + 1 := by omega
    calc measureConvPow ν (m + (k + 1))
        = measureConvPow ν (m + k) ∗ ν := by rw [hstep, measureConvPow_succ]
      _ = (measureConvPow ν k ∗ measureConvPow ν m) ∗ ν := by rw [ih]
      _ = measureConvPow ν k ∗ (measureConvPow ν m ∗ ν) := Measure.conv_assoc _ _ _
      _ = measureConvPow ν k ∗ (ν ∗ measureConvPow ν m) := by
          rw [Measure.conv_comm (measureConvPow ν m) ν]
      _ = (measureConvPow ν k ∗ ν) ∗ measureConvPow ν m :=
          (Measure.conv_assoc _ _ _).symm
      _ = measureConvPow ν (k + 1) ∗ measureConvPow ν m := by rw [measureConvPow_succ]

/-! ## The exact `m`-fold identity with its boundary correction -/

/-- A pure `ℝ≥0∞` reindexing: split a series at index `m`.  Kept separate so
that the renewal terms never enter the `Summable` unification. -/
theorem tsum_nat_split (f : ℕ → ℝ≥0∞) (m : ℕ) :
    (∑' n : ℕ, f n) = (∑ j ∈ Finset.range m, f j) + ∑' k : ℕ, f (m + k) := by
  have hpt : ∀ n : ℕ,
      f n = (if n < m then f n else 0) + (if m ≤ n then f n else 0) := by
    intro n
    by_cases h : n < m
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  have hlow : (∑' n : ℕ, (if n < m then f n else 0)) =
      ∑ j ∈ Finset.range m, f j := by
    rw [tsum_eq_sum (s := Finset.range m) (fun b hb => by
      rw [if_neg (by simpa using hb)])]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [if_pos (Finset.mem_range.mp hj)]
  have hhigh : (∑' n : ℕ, (if m ≤ n then f n else 0)) =
      ∑' k : ℕ, f (m + k) := by
    have h := tsum_ite_shift m (fun k => f (m + k))
    rw [← h]
    refine tsum_congr fun n => ?_
    by_cases hn : m ≤ n
    · rw [if_pos hn, if_pos hn]
      congr 1
      omega
    · rw [if_neg hn, if_neg hn]
  calc (∑' n : ℕ, f n)
      = ∑' n : ℕ, ((if n < m then f n else 0) + (if m ≤ n then f n else 0)) :=
        tsum_congr hpt
    _ = (∑' n : ℕ, (if n < m then f n else 0)) +
        ∑' n : ℕ, (if m ≤ n then f n else 0) := ENNReal.tsum_add
    _ = (∑ j ∈ Finset.range m, f j) + ∑' k : ℕ, f (m + k) := by rw [hlow, hhigh]

theorem ladderRenewalMeasure_Ioc_tsum_tail (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m : ℕ) (c d : ℝ) :
    ladderRenewalMeasure ν (Ioc c d) =
      (∑ j ∈ Finset.range m, measureConvPow ν j (Ioc c d)) +
        ∑' k : ℕ, measureConvPow ν (m + k) (Ioc c d) := by
  rw [ladderRenewalMeasure_apply ν measurableSet_Ioc]
  exact tsum_nat_split (fun n => measureConvPow ν n (Ioc c d)) m

theorem tsum_measureConvPow_shift_eq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m : ℕ) (c d : ℝ) :
    (∑' k : ℕ, measureConvPow ν (m + k) (Ioc c d)) =
      ∫⁻ y, ladderRenewalMeasure ν (Ioc (c - y) (d - y))
        ∂(measureConvPow ν m) := by
  have hterm : ∀ k : ℕ, measureConvPow ν (m + k) (Ioc c d) =
      ∫⁻ y, measureConvPow ν k (Ioc (c - y) (d - y)) ∂(measureConvPow ν m) := by
    intro k
    rw [measureConvPow_add ν m k, measure_conv_Ioc]
  have h1 : (∑' k : ℕ, measureConvPow ν (m + k) (Ioc c d)) =
      ∑' k : ℕ, ∫⁻ y, measureConvPow ν k (Ioc (c - y) (d - y))
        ∂(measureConvPow ν m) := tsum_congr hterm
  have h2 : (∑' k : ℕ, ∫⁻ y, measureConvPow ν k (Ioc (c - y) (d - y))
        ∂(measureConvPow ν m)) =
      ∫⁻ y, (∑' k : ℕ, measureConvPow ν k (Ioc (c - y) (d - y)))
        ∂(measureConvPow ν m) :=
    (lintegral_tsum (fun k =>
      (measurable_measure_Ioc_shift (measureConvPow ν k) c d).aemeasurable)).symm
  rw [h1, h2]
  refine lintegral_congr fun y => ?_
  exact (ladderRenewalMeasure_apply ν measurableSet_Ioc).symm

/--
**The boundary-safe `m`-fold renewal identity.**  Splitting the renewal series
at index `m` gives, for every `m`, every window and with no side condition,

`U(Ioc c d) = ∑_{j<m} ν^{*j}(Ioc c d) + ∫ U(Ioc (c-y) (d-y)) dν^{*m}(y)`.

The finite sum is exactly the boundary correction that a naive iteration of the
renewal equation would drop.
-/
theorem ladderRenewalMeasure_Ioc_split (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m : ℕ) (c d : ℝ) :
    ladderRenewalMeasure ν (Ioc c d) =
      (∑ j ∈ Finset.range m, measureConvPow ν j (Ioc c d)) +
        ∫⁻ y, ladderRenewalMeasure ν (Ioc (c - y) (d - y))
          ∂(measureConvPow ν m) := by
  rw [ladderRenewalMeasure_Ioc_tsum_tail ν m c d,
    tsum_measureConvPow_shift_eq ν m c d]

/-- The `m = 1` case, recorded separately because it fixes the *direction* of
the renewal relation: the window mass at `u` is an average of window masses at
*smaller* arguments, plus the renewal atom. -/
theorem ladderRenewalMeasure_Ioc_renewal (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (c d : ℝ) :
    ladderRenewalMeasure ν (Ioc c d) =
      (if (0 : ℝ) ∈ Ioc c d then 1 else 0) +
        ∫⁻ y, ladderRenewalMeasure ν (Ioc (c - y) (d - y)) ∂ν := by
  have hone : measureConvPow ν 1 = ν := by
    rw [measureConvPow_succ, measureConvPow_zero, Measure.dirac_zero_conv]
  have h := ladderRenewalMeasure_Ioc_split ν 1 c d
  rw [Finset.sum_range_one, measureConvPow_zero, hone] at h
  rw [h]
  congr 1
  rw [Measure.dirac_apply' _ measurableSet_Ioc]
  by_cases h0 : (0 : ℝ) ∈ Ioc c d
  · rw [Set.indicator_of_mem h0, if_pos h0]
    rfl
  · rw [Set.indicator_of_notMem h0, if_neg h0]

/-- The boundary correction vanishes as the window recedes: each term is the
mass of a fixed finite measure on a far window. -/
theorem renewalWindowCorrection_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m : ℕ) {c d : ℝ} :
    (∑ j ∈ Finset.range m, measureConvPow ν j (Ioc c d)) ≤
      ∑ j ∈ Finset.range m, measureConvPow ν j (Ioi c) := by
  refine Finset.sum_le_sum fun j _ => measure_mono ?_
  exact Ioc_subset_Ioi_self


/-! ## Gate 3: the supremum is only approached -/

/-- `L(β) = sSup (f '' Ici β)` need not be attained; this is the only form in
which it is used below. -/
theorem exists_near_window_sSup {f : ℝ → ℝ} {P : ℝ} (hbd : ∀ u : ℝ, f u ≤ P)
    (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ, β ≤ u ∧ sSup (f '' Ici β) - ε ≤ f u := by
  have hne : (f '' Ici β).Nonempty := ⟨f β, β, le_refl β, rfl⟩
  have hbdd : BddAbove (f '' Ici β) := by
    refine ⟨P, ?_⟩
    rintro z ⟨u, -, rfl⟩
    exact hbd u
  have hlt : sSup (f '' Ici β) - ε < sSup (f '' Ici β) := by linarith
  obtain ⟨z, ⟨u, hu, rfl⟩, hz⟩ := exists_lt_of_lt_csSup hne hlt
  exact ⟨u, hu, hz.le⟩

/-- The dual statement for the infimum. -/
theorem exists_near_window_sInf {f : ℝ → ℝ} {P : ℝ} (hbd : ∀ u : ℝ, -P ≤ f u)
    (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ, β ≤ u ∧ f u ≤ sInf (f '' Ici β) + ε := by
  have hne : (f '' Ici β).Nonempty := ⟨f β, β, le_refl β, rfl⟩
  have hbdd : BddBelow (f '' Ici β) := by
    refine ⟨-P, ?_⟩
    rintro z ⟨u, -, rfl⟩
    exact hbd u
  have hlt : sInf (f '' Ici β) < sInf (f '' Ici β) + ε := by linarith
  obtain ⟨z, ⟨u, hu, rfl⟩, hz⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨u, hu, hz.le⟩

/-! ## Gate 4: the finite-`m` deficit identity -/

/-- The real-valued renewal window mass. -/
def renewalWindow (ν : Measure ℝ) (x u : ℝ) : ℝ :=
  (ladderRenewalMeasure ν (Ioc (u - x) u)).toReal

theorem renewalWindow_nonneg (ν : Measure ℝ) (x u : ℝ) :
    0 ≤ renewalWindow ν x u := ENNReal.toReal_nonneg

theorem renewalWindow_le (ν : Measure ℝ) {x P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ u : ℝ, ladderRenewalMeasure ν (Ioc (u - x) u) ≤ ENNReal.ofReal P)
    (u : ℝ) : renewalWindow ν x u ≤ P := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hP u)
  rwa [ENNReal.toReal_ofReal hP0] at h

theorem measurable_renewalWindow_shift (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (x b : ℝ) :
    Measurable (fun y : ℝ => renewalWindow ν x (b - y)) := by
  have hEq : (fun y : ℝ => renewalWindow ν x (b - y)) =
      fun y : ℝ => (ladderRenewalMeasure ν (Ioc (b - x - y) (b - y))).toReal := by
    funext y
    rw [renewalWindow, show b - y - x = b - x - y by ring]
  rw [hEq]
  exact (measurable_measure_Ioc_shift (ladderRenewalMeasure ν) (b - x) b).ennreal_toReal

/--
**The finite-`m` deficit identity.**  For every `m`, every level `b` and every
constant `L`, the `ν^{*m}`-average of the deficit `L - W` equals the deficit at
`b` plus the explicit boundary correction of the `m`-fold split.  No
`b ≥ x` side condition, no attained supremum, no asymptotics.
-/
theorem window_deficit_integral_eq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {x P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ u : ℝ, ladderRenewalMeasure ν (Ioc (u - x) u) ≤ ENNReal.ofReal P)
    (m : ℕ) (b L : ℝ) :
    (∫ y, (L - renewalWindow ν x (b - y)) ∂(measureConvPow ν m)) =
      L - renewalWindow ν x b +
        ∑ j ∈ Finset.range m, (measureConvPow ν j (Ioc (b - x) b)).toReal := by
  set U := ladderRenewalMeasure ν with hUdef
  have hshift : ∀ y : ℝ, renewalWindow ν x (b - y) =
      (U (Ioc (b - x - y) (b - y))).toReal := by
    intro y
    rw [renewalWindow, show b - y - x = b - x - y by ring]
  have hmeas : Measurable (fun y : ℝ => renewalWindow ν x (b - y)) :=
    measurable_renewalWindow_shift ν x b
  have hbdd : ∀ y : ℝ, renewalWindow ν x (b - y) ≤ P :=
    fun y => renewalWindow_le ν hP0 hP _
  have hint : Integrable (fun y : ℝ => renewalWindow ν x (b - y))
      (measureConvPow ν m) := by
    refine (integrable_const P).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (renewalWindow_nonneg ν x _)]
    exact hbdd y
  -- the ENNReal split and its finiteness
  have hsplit := ladderRenewalMeasure_Ioc_split ν m (b - x) b
  have hIfin : (∫⁻ y, U (Ioc (b - x - y) (b - y)) ∂(measureConvPow ν m)) ≠ ⊤ := by
    have hstep : ∀ y : ℝ, U (Ioc (b - x - y) (b - y)) ≤ ENNReal.ofReal P := by
      intro y
      have hy := hP (b - y)
      rwa [show b - y - x = b - x - y by ring] at hy
    have hle : (∫⁻ y, U (Ioc (b - x - y) (b - y)) ∂(measureConvPow ν m)) ≤
        ENNReal.ofReal P := by
      calc (∫⁻ y, U (Ioc (b - x - y) (b - y)) ∂(measureConvPow ν m))
          ≤ ∫⁻ _y : ℝ, ENNReal.ofReal P ∂(measureConvPow ν m) :=
            lintegral_mono hstep
        _ = ENNReal.ofReal P := by rw [lintegral_const, measure_univ, mul_one]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hSfin : ∀ j : ℕ, measureConvPow ν j (Ioc (b - x) b) ≠ ⊤ :=
    fun j => measure_ne_top _ _
  have hsumfin : (∑ j ∈ Finset.range m, measureConvPow ν j (Ioc (b - x) b)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => hSfin j)
  -- take `toReal` of the split
  have hreal : renewalWindow ν x b =
      (∑ j ∈ Finset.range m, (measureConvPow ν j (Ioc (b - x) b)).toReal) +
        (∫⁻ y, U (Ioc (b - x - y) (b - y)) ∂(measureConvPow ν m)).toReal := by
    rw [renewalWindow, hsplit, ENNReal.toReal_add hsumfin hIfin,
      ENNReal.toReal_sum (fun j _ => hSfin j)]
  -- the Bochner integral of the window
  have hBochner : (∫ y, renewalWindow ν x (b - y) ∂(measureConvPow ν m)) =
      (∫⁻ y, U (Ioc (b - x - y) (b - y)) ∂(measureConvPow ν m)).toReal := by
    have hcongr : (fun y : ℝ => renewalWindow ν x (b - y)) =
        fun y : ℝ => (U (Ioc (b - x - y) (b - y))).toReal := funext hshift
    rw [hcongr]
    refine integral_toReal
      (measurable_measure_Ioc_shift (ladderRenewalMeasure ν) (b - x) b).aemeasurable ?_
    filter_upwards with y
    have hy := hP (b - y)
    rw [show b - y - x = b - x - y by ring] at hy
    exact lt_of_le_of_lt hy ENNReal.ofReal_lt_top
  rw [integral_sub (integrable_const L) hint, integral_const]
  have hQuniv : (measureConvPow ν m).real univ = 1 := by
    rw [Measure.real, measure_univ, ENNReal.toReal_one]
  rw [hQuniv, one_smul, hBochner, hreal]
  ring

end SwingRepair
