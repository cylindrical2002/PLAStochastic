import PLAStochastic.Index.KRE.LatticeWindow
import PLAStochastic.Index.KRE.CurvedLayer
import PLAStochastic.Index.Model.ExpConcentration

/-!
# The good event for the Model K reference walk

Let `E` be an iid sequence of standard exponential variables.  The reference walk is
`refWalk E ω t = E 0 + ⋯ + E t` (`t + 1` terms), whose gaps after the first key are
`refGap E s = E (s + 1)` (`refWalk_eq`), again iid standard exponential
(`gapLaw_refGap`).

The bad event `kreBad E n eps t j` is the union of

* the failure of the uniform partial-sum concentration `(expGood E n)ᶜ`;
* the null event that some `E i ≤ 0`;
* the lattice-count bad events `reBad` of the gaps `refGap E` at the tolerances
  `eps / 2` and `2 eps` (with `G₀ = θ²`);
* the long-window event `vBad (2 eps) (refGap E) j n`.

`measureReal_kreBad_le` bounds its probability by
`18 / n² + 2 (2n + 1)² pairFail t + (2n + 1)² (71/72)^j`.

Off the bad event, for `z = refWalk E ω`: `z` is strictly increasing, `z t / z n ∈ [0, 1]`
for `t < n`, the span and tube bounds hold with constant `80`, `n / 2 ≤ z n` (for
`n ≥ 160000`), every lattice count `finSegCount θ (z (· d)) K` with `θ ∈ {eps/2, 2 eps}`
lies in the `reBad` bracket, and no lattice window of `j kreL (2 eps) d + 1` keys is
`2 eps`-feasible.  `curvedLattice_refWalk` packages these into a `CurvedLattice`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

/-! ## The reference walk and the bad event -/

section Pathwise

variable {Ω : Type*} {E : ℕ → Ω → ℝ}

/-- The reference walk `refWalk E ω t = E 0 ω + ⋯ + E t ω`. -/
def refWalk (E : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) : ℝ := ∑ i ∈ range (t + 1), E i ω

/-- The gaps of the reference walk after its first key: `refGap E s = E (s + 1)`. -/
def refGap (E : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun s ω => E (s + 1) ω

theorem refWalk_eq (E : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) :
    refWalk E ω t = E 0 ω + ∑ i ∈ range t, refGap E i ω := by
  unfold refWalk refGap
  rw [sum_range_succ', add_comm]

theorem refWalk_sub (E : ℕ → Ω → ℝ) (ω : Ω) {a b : ℕ} (hab : a ≤ b) :
    refWalk E ω b - refWalk E ω a = expSum E (a + 1) (b + 1) ω := by
  unfold refWalk expSum
  rw [sum_Ico_eq_sub _ (by omega)]

/-- The bad event of the Model K layer analysis. -/
def kreBad (E : ℕ → Ω → ℝ) (n : ℕ) (eps : ℝ) (t j : ℕ) : Set Ω :=
  (expGood E n)ᶜ ∪ {ω | ∃ i, E i ω ≤ 0} ∪ reBad (eps / 2) (refGap E) ((eps / 2) ^ 2) t n ∪
    reBad (2 * eps) (refGap E) ((2 * eps) ^ 2) t n ∪ vBad (2 * eps) (refGap E) j n

variable {n : ℕ} {eps : ℝ} {t j : ℕ} {ω : Ω}

/-- The components of the complement of the bad event. -/
theorem notMem_kreBad (hω : ω ∉ kreBad E n eps t j) :
    ω ∈ expGood E n ∧ (∀ i, 0 < E i ω) ∧
      ω ∉ reBad (eps / 2) (refGap E) ((eps / 2) ^ 2) t n ∧
      ω ∉ reBad (2 * eps) (refGap E) ((2 * eps) ^ 2) t n ∧
      ω ∉ vBad (2 * eps) (refGap E) j n := by
  simp only [kreBad, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_not,
    not_exists, not_le] at hω
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hω
  exact ⟨h1, h2, h3, h4, h5⟩

/-- The reference walk is positive off the bad event. -/
theorem refWalk_pos (hω : ω ∉ kreBad E n eps t j) (s : ℕ) : 0 < refWalk E ω s :=
  sum_pos (fun i _ => (notMem_kreBad hω).2.1 i) ⟨0, mem_range.2 (Nat.succ_pos _)⟩

/-- **(a)** The reference walk is strictly increasing off the bad event. -/
theorem refWalk_strictMono (hω : ω ∉ kreBad E n eps t j) : StrictMono (refWalk E ω) :=
  strictMono_sum_range_succ (e := fun i => E i ω) (notMem_kreBad hω).2.1

/-- **(b)** Normalised by `z n`, the keys `z s`, `s < n`, lie in `[0, 1]`. -/
theorem refWalk_div_mem_Icc (hω : ω ∉ kreBad E n eps t j) :
    ∀ s < n, refWalk E ω s / refWalk E ω n ∈ Set.Icc (0 : ℝ) 1 := by
  intro s hs
  have hpos := refWalk_pos hω s
  have hposn := refWalk_pos hω n
  have hle := (refWalk_strictMono hω).monotone hs.le
  exact ⟨div_nonneg hpos.le hposn.le, (div_le_one hposn).2 hle⟩

theorem cast_succ_sub_succ {a b : ℕ} (hab : a ≤ b) :
    (((b + 1 - (a + 1) : ℕ)) : ℝ) = (b : ℝ) - a := by
  rw [show b + 1 - (a + 1) = b - a by omega, Nat.cast_sub hab]

/-- **(c)** The span bound with constant `80`. -/
theorem refWalk_span (hω : ω ∉ kreBad E n eps t j) :
    ∀ a b : ℕ, a ≤ b → b < n →
      refWalk E ω b - refWalk E ω a ≤ 80 * ((b - a : ℝ) + Real.log n) := by
  intro a b hab hbn
  have hn : 1 ≤ n := by omega
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [refWalk_sub E ω hab]
  have h := expSum_le_of_mem_expGood (notMem_kreBad hω).1 hn (a := a + 1) (b := b + 1)
    (by omega) (by omega)
  rw [cast_succ_sub_succ hab] at h
  have hba : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.2 (by exact_mod_cast hab)
  linarith

/-- **(d)** The tube bound with constant `80`. -/
theorem refWalk_tube (hω : ω ∉ kreBad E n eps t j) :
    ∀ a b : ℕ, a ≤ b → b < n →
      |refWalk E ω b - refWalk E ω a - (b - a)| ≤
        80 * (Real.sqrt ((b - a) * Real.log n) + Real.log n) := by
  intro a b hab hbn
  have hn : 1 ≤ n := by omega
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hs : 0 ≤ Real.sqrt (((b : ℝ) - a) * Real.log n) := Real.sqrt_nonneg _
  rw [refWalk_sub E ω hab]
  rcases hab.eq_or_lt with rfl | hlt
  · rw [expSum, Ico_self, sum_empty, sub_self, sub_self, abs_zero]
    positivity
  · have h := (notMem_kreBad hω).1 (a + 1) (b + 1) (by omega) (by omega)
    rw [cast_succ_sub_succ hab] at h
    linarith

/-- **(e)** `n / 2 ≤ z n` for `n ≥ 160000`. -/
theorem half_le_refWalk (hω : ω ∉ kreBad E n eps t j) (hn : 160000 ≤ n) :
    (n : ℝ) / 2 ≤ refWalk E ω n := by
  have h := half_le_expSum_zero_of_mem_expGood_of_ge (notMem_kreBad hω).1 hn
  have he : refWalk E ω n = expSum E 0 n ω + E n ω := by
    rw [refWalk, sum_range_succ, expSum, range_eq_Ico]
  have hpos := (notMem_kreBad hω).2.1 n
  rw [he]
  linarith

/-- The lattice count of the reference walk is the block count of its gaps. -/
theorem finSegCount_refWalk_eq (E : ℕ → Ω → ℝ) (ω : Ω) (θ : ℝ) (d K : ℕ) :
    finSegCount θ (fun k => refWalk E ω (k * d)) K = blockCount θ (refGap E) d K ω := by
  unfold blockCount
  have hfun : (fun k => refWalk E ω (k * d)) =
      fun k => gapKeys (seq (blockGap (refGap E) d) ω) k + E 0 ω := by
    funext k
    rw [gapKeys_blockGap, refWalk_eq]
    simp only [gapKeys, seq]
    ring
  rw [hfun, finSegCount_add_const]

/-- Off `reBad θ (refGap E) θ² t n`, every lattice count of the reference walk with
`1 ≤ d, K ≤ 2n` is in the bracket. -/
theorem bracket_of_not_reBad_refGap {θ : ℝ} (hω : ω ∉ reBad θ (refGap E) (θ ^ 2) t n)
    {d K : ℕ} (hd : 1 ≤ d) (hK : 1 ≤ K) (hd2 : d ≤ 2 * n) (hK2 : K ≤ 2 * n) :
    aLow * K / (d * θ ^ 2) - t ≤ (finSegCount θ (fun k => refWalk E ω (k * d)) K : ℝ) ∧
      (finSegCount θ (fun k => refWalk E ω (k * d)) K : ℝ) ≤ 128 * K / (d * θ ^ 2) + t + 1 := by
  have hnot : ω ∉ pairBad θ (refGap E) (θ ^ 2) t d K := fun h =>
    hω (Set.mem_biUnion (mem_range.2 (by omega)) (Set.mem_biUnion (mem_range.2 (by omega)) h))
  unfold pairBad at hnot
  rw [if_pos ⟨hd, hK⟩] at hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot
  rw [finSegCount_refWalk_eq]
  exact ⟨hnot.2, hnot.1⟩

/-- **(f)** The lattice-count bracket at the tolerances `eps / 2` and `2 eps`. -/
theorem refWalk_bracket (hω : ω ∉ kreBad E n eps t j) {θ : ℝ}
    (hθ : θ = eps / 2 ∨ θ = 2 * eps) :
    ∀ d K : ℕ, 1 ≤ d → 1 ≤ K → d ≤ 2 * n → K ≤ 2 * n →
      aLow * K / (d * θ ^ 2) - t ≤ (finSegCount θ (fun k => refWalk E ω (k * d)) K : ℝ) ∧
        (finSegCount θ (fun k => refWalk E ω (k * d)) K : ℝ) ≤
          128 * K / (d * θ ^ 2) + t + 1 := by
  intro d K hd hK hd2 hK2
  rcases hθ with rfl | rfl
  · exact bracket_of_not_reBad_refGap (notMem_kreBad hω).2.2.1 hd hK hd2 hK2
  · exact bracket_of_not_reBad_refGap (notMem_kreBad hω).2.2.2.1 hd hK hd2 hK2

/-- **(g)** No lattice window of `j kreL (2 eps) d + 1` reference keys is
`2 eps`-feasible. -/
theorem refWalk_not_windowFeasible (hω : ω ∉ kreBad E n eps t j) :
    ∀ d a : ℕ, 1 ≤ d → d ≤ 2 * n → a ≤ 2 * n →
      ¬ windowFeasible (2 * eps) (fun k => refWalk E ω (k * d)) a
        (a + (j * kreL (2 * eps) d + 1)) :=
  fun _ _ hd hd2 ha =>
    not_windowFeasible_lattice_of_not_vBad (notMem_kreBad hω).2.2.2.2 (refWalk_eq E ω) hd hd2 ha

/-- Off the bad event (and for `n ≥ 160000`), the reference walk with normaliser `z n`
and constant `Kst = 80` is a `CurvedLattice` for any admissible change of keys and any
lattice of spacing `Δ ≥ 1` and size `K` with `(K - 1) Δ < n`. -/
theorem curvedLattice_refWalk (hω : ω ∉ kreBad E n eps t j) (hn : 160000 ≤ n)
    {φ φ' : ℝ → ℝ} {L δ : ℝ}
    (hderiv : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' x) (Set.Icc 0 1) x)
    (hlip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |φ' x - φ' y| ≤ L * |x - y|)
    (hδ : 0 < δ) (hle : ∀ x ∈ Set.Icc (0 : ℝ) 1, δ ≤ φ' x)
    {Δ K : ℕ} (hΔ : 1 ≤ Δ) (hsize : (K - 1) * Δ < n) :
    CurvedLattice φ φ' (refWalk E ω) (refWalk E ω n) L δ 80 n Δ K where
  strictMono := refWalk_strictMono hω
  deriv := hderiv
  lip := hlip
  delta_pos := hδ
  le_deriv := hle
  mem_Icc := refWalk_div_mem_Icc hω
  one_le_spacing := hΔ
  size := hsize
  Kst_nonneg := by norm_num
  span := refWalk_span hω
  half_le := half_le_refWalk hω hn

end Pathwise

/-! ## Measurability and probability of the bad event -/

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℕ → Ω → ℝ}

theorem measurable_refGap (hE : ∀ i, Measurable (E i)) (s : ℕ) : Measurable (refGap E s) :=
  hE (s + 1)

theorem measurableSet_expGood (hE : ∀ i, Measurable (E i)) (N : ℕ) :
    MeasurableSet (expGood E N) := by
  have hS : ∀ a b, Measurable (expSum E a b) := fun a b => by
    show Measurable fun ω => ∑ i ∈ Ico a b, E i ω
    exact Finset.measurable_sum _ fun i _ => hE i
  simp only [expGood, Set.ofPred_forall]
  refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le (continuous_abs.measurable.comp ((hS a b).sub_const _))
    measurable_const

theorem measurableSet_exists_nonpos (hE : ∀ i, Measurable (E i)) :
    MeasurableSet {ω | ∃ i, E i ω ≤ 0} := by
  rw [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun i => measurableSet_le (hE i) measurable_const

theorem measurableSet_kreBad (hE : ∀ i, Measurable (E i)) (n : ℕ) (eps : ℝ) (t j : ℕ) :
    MeasurableSet (kreBad E n eps t j) :=
  ((((measurableSet_expGood hE n).compl.union (measurableSet_exists_nonpos hE)).union
    (measurableSet_reBad (measurable_refGap hE) _ _ t n)).union
    (measurableSet_reBad (measurable_refGap hE) _ _ t n)).union
    (measurableSet_vBad (measurable_refGap hE) _ j n)

/-- The gaps `E (s + 1)` are again iid standard exponential. -/
theorem gapLaw_refGap (hE : IIDSeq P E) (hlaw : HasLaw (E 0) (expMeasure 1) P) :
    GapLaw P (refGap E) 1 1 16 := by
  have h := (gapLaw_exp hE hlaw).shift 1
  have hfun : (fun t => E (1 + t)) = refGap E := by
    funext s ω
    simp only [refGap, add_comm]
  rwa [hfun] at h

/-- Standard exponential variables are almost surely positive. -/
theorem measureReal_exists_nonpos (hE : IIDSeq P E) (hlaw : HasLaw (E 0) (expMeasure 1) P) :
    P.real {ω | ∃ i, E i ω ≤ 0} = 0 := by
  have h : ∀ i, P {ω | E i ω ≤ 0} = 0 := fun i => by
    have := hE.ae_pos_of_expMeasure_one hlaw i
    rw [ae_iff] at this
    simpa only [not_lt] using this
  rw [Set.ofPred_exists, measureReal_def, measure_iUnion_null h, ENNReal.toReal_zero]

/-- **Probability of the bad event.** -/
theorem measureReal_kreBad_le [IsProbabilityMeasure P] (hE : IIDSeq P E)
    (hlaw : HasLaw (E 0) (expMeasure 1) P) {n : ℕ} (hn : 1 ≤ n) {eps : ℝ}
    (heps : epsZero 1 18 ≤ eps / 2) (t j : ℕ) :
    P.real (kreBad E n eps t j) ≤
      18 / (n : ℝ) ^ 2 + 2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail t) +
        ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (71 / 72 : ℝ) ^ j := by
  have hg := gapLaw_refGap hE hlaw
  have hZ : epsZero ((1 : ℝ) ^ 2 / 1 ^ 2) (2 + 16 / 1 ^ 3) = epsZero 1 18 := by norm_num
  have h1 := one_le_epsZero 1 18
  have heps2 : epsZero 1 18 ≤ 2 * eps := by linarith
  have hC := measureReal_reBad_le hg (eps := eps / 2) (hZ.trans_le heps) t n
  have hD := measureReal_reBad_le hg (eps := 2 * eps) (hZ.trans_le heps2) t n
  simp only [one_pow, one_mul, div_one] at hC hD
  have hF := measureReal_vBad_le hg (eps := 2 * eps) (by linarith) j n
  have hA := measureReal_compl_expGood_le hE hlaw hn
  have hB := measureReal_exists_nonpos hE hlaw
  set A := (expGood E n)ᶜ
  set B := {ω | ∃ i, E i ω ≤ 0}
  set C := reBad (eps / 2) (refGap E) ((eps / 2) ^ 2) t n
  set D := reBad (2 * eps) (refGap E) ((2 * eps) ^ 2) t n
  set F := vBad (2 * eps) (refGap E) j n
  have u1 : P.real (A ∪ B ∪ C ∪ D ∪ F) ≤ P.real (A ∪ B ∪ C ∪ D) + P.real F :=
    measureReal_union_le _ _
  have u2 : P.real (A ∪ B ∪ C ∪ D) ≤ P.real (A ∪ B ∪ C) + P.real D := measureReal_union_le _ _
  have u3 : P.real (A ∪ B ∪ C) ≤ P.real (A ∪ B) + P.real C := measureReal_union_le _ _
  have u4 : P.real (A ∪ B) ≤ P.real A + P.real B := measureReal_union_le _ _
  show P.real (A ∪ B ∪ C ∪ D ∪ F) ≤ _
  linarith

end Probability

end

end PGM
