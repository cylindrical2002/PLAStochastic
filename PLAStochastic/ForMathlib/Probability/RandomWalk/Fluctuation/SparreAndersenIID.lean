import PLAStochastic.ForMathlib.Probability.RandomWalk.Fluctuation.SparreAndersenCombinatorial
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Sparre Andersen for i.i.d. sequences (roadmap 1.2, target B)

For an i.i.d. real sequence `Y` the vector `(Y_{p₁}, …, Y_{pₙ})` has the same law for every
list `p` of `n` distinct indices, namely the product law.  Averaging the combinatorial
identity `card_posCount_eq_card_isFirstArgmax` over all permutations of `[0, n)` gives

  `μ {N_n = k} = μ {T_n = k}`,

where `N_n = #{1 ≤ j ≤ n : S_j > 0}` and `T_n` is the first argmax of `S_0, …, S_n`,
`S_j = Y_0 + ⋯ + Y_{j-1}`.
-/
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal List
namespace SwingRepair
namespace Fluctuation

/-! ### Predicates as functions of the value list -/

theorem psum_map (x : ι → ℝ) (p : List ι) (j : ℕ) : psum id (p.map x) j = psum x p j := by
  simp [psum, List.map_take]

theorem isFirstArgmax_map_iff (x : ι → ℝ) (p : List ι) (k : ℕ) :
    IsFirstArgmax id (p.map x) k ↔ IsFirstArgmax x p k := by
  simp only [IsFirstArgmax, psum_map, List.length_map]

theorem posCount_map (x : ι → ℝ) (p : List ι) : posCount id (p.map x) = posCount x p := by
  simp only [posCount, psum_map, List.length_map]

theorem allPos_map_iff (x : ι → ℝ) (p : List ι) : AllPos id (p.map x) ↔ AllPos x p := by
  simp only [AllPos, psum_map, List.length_map]

/-! ### Measurability on `Fin m → ℝ` -/

theorem measurable_psum_ofFn :
    ∀ (m j : ℕ), Measurable fun v : Fin m → ℝ => psum id (List.ofFn v) j := by
  intro m
  induction m with
  | zero => intro j; simp [psum]
  | succ m ih =>
    intro j
    cases j with
    | zero => simp [psum]
    | succ j =>
      have : (fun v : Fin (m + 1) → ℝ => psum id (List.ofFn v) (j + 1)) =
          fun v => v 0 + psum id (List.ofFn fun i : Fin m => v i.succ) j := by
        funext v
        simp [psum, List.ofFn_succ]
      rw [this]
      exact (measurable_pi_apply 0).add
        ((ih j).comp (measurable_pi_lambda _ fun i => measurable_pi_apply i.succ))

theorem measurableSet_isFirstArgmax_ofFn (m k : ℕ) :
    MeasurableSet {v : Fin m → ℝ | IsFirstArgmax id (List.ofFn v) k} := by
  have : {v : Fin m → ℝ | IsFirstArgmax id (List.ofFn v) k} =
      {v | k ≤ m} ∩ ((⋂ i, ⋂ (_ : i < k), {v | psum id (List.ofFn v) i < psum id (List.ofFn v) k}) ∩
        ⋂ i, {v | psum id (List.ofFn v) i ≤ psum id (List.ofFn v) k}) := by
    ext v
    simp [IsFirstArgmax]
  rw [this]
  refine MeasurableSet.inter (by by_cases h : k ≤ m <;> simp [h]) (MeasurableSet.inter ?_ ?_)
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_psum_ofFn m i) (measurable_psum_ofFn m k)
  · exact MeasurableSet.iInter fun i =>
      measurableSet_le (measurable_psum_ofFn m i) (measurable_psum_ofFn m k)

theorem measurable_posCount_ofFn (m : ℕ) :
    Measurable fun v : Fin m → ℝ => posCount id (List.ofFn v) := by
  have : (fun v : Fin m → ℝ => posCount id (List.ofFn v)) =
      fun v => ∑ j ∈ Finset.range m, if 0 < psum id (List.ofFn v) (j + 1) then 1 else 0 := by
    funext v
    simp only [posCount, List.length_ofFn]
    rw [Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ fun j _ => Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt measurable_const (measurable_psum_ofFn m (j + 1))

theorem measurableSet_posCount_ofFn (m k : ℕ) :
    MeasurableSet {v : Fin m → ℝ | posCount id (List.ofFn v) = k} :=
  measurable_posCount_ofFn m (measurableSet_singleton k)

/-! ### The law of a vector of distinct coordinates -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : ℕ → Ω → ℝ} {ν : Measure ℝ}

theorem map_vector_eq_pi [IsProbabilityMeasure μ] (hY : ∀ i, Measurable (Y i))
    (hi : iIndepFun Y μ) (hν : ∀ i, μ.map (Y i) = ν) {m : ℕ} (f : Fin m → ℕ)
    (hf : Function.Injective f) :
    μ.map (fun ω (i : Fin m) => Y (f i) ω) = Measure.pi fun _ : Fin m => ν := by
  have h := hi.precomp hf
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hY (f i)).aemeasurable)] at h
  rw [h]
  congr 1
  funext i
  exact hν (f i)

/-- The value list along `p` is the `ofFn` of the vector `i ↦ Y (p[i])`. -/
theorem map_eq_ofFn_get (g : ℕ → ℝ) (p : List ℕ) {n : ℕ} (hlen : p.length = n) :
    p.map g = List.ofFn fun i : Fin n => g (p.get (Fin.cast hlen.symm i)) := by
  conv_lhs => rw [← List.ofFn_get p]
  rw [List.map_ofFn, List.ofFn_congr hlen]
  rfl

omit [MeasurableSpace Ω] in
/-- The event `{Q (Y ∘ p)}` is the preimage of `{v | Q (ofFn v)}` under the coordinate vector. -/
theorem setOf_list_pred_eq_preimage (Q : List ℝ → Prop) (p : List ℕ) {n : ℕ} (hlen : p.length = n) :
    {ω | Q (p.map fun i => Y i ω)} =
      (fun ω (i : Fin n) => Y (p.get (Fin.cast hlen.symm i)) ω) ⁻¹' {v | Q (List.ofFn v)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  rw [map_eq_ofFn_get (fun i => Y i ω) p hlen]

theorem measurableSet_list_pred (hY : ∀ i, Measurable (Y i)) {n : ℕ} (Q : List ℝ → Prop)
    (hQ : MeasurableSet {v : Fin n → ℝ | Q (List.ofFn v)}) (p : List ℕ) (hlen : p.length = n) :
    MeasurableSet {ω | Q (p.map fun i => Y i ω)} := by
  rw [setOf_list_pred_eq_preimage Q p hlen]
  exact hQ.preimage (measurable_pi_lambda _ fun i => hY _)

/-- `μ {Q (Y ∘ p)} = (⊗ν) {Q ∘ ofFn}` for any list `p` of `n` distinct indices. -/
theorem measure_list_pred_eq [IsProbabilityMeasure μ] (hY : ∀ i, Measurable (Y i))
    (hi : iIndepFun Y μ) (hν : ∀ i, μ.map (Y i) = ν) {n : ℕ} (Q : List ℝ → Prop)
    (hQ : MeasurableSet {v : Fin n → ℝ | Q (List.ofFn v)}) (p : List ℕ) (hlen : p.length = n)
    (hnd : p.Nodup) :
    μ {ω | Q (p.map fun i => Y i ω)} = (Measure.pi fun _ : Fin n => ν) {v | Q (List.ofFn v)} := by
  set f : Fin n → ℕ := fun i => p.get (Fin.cast hlen.symm i) with hf_def
  have hf : Function.Injective f :=
    (List.nodup_iff_injective_get.mp hnd).comp (Fin.cast_injective _)
  rw [setOf_list_pred_eq_preimage Q p hlen,
    ← Measure.map_apply (measurable_pi_lambda _ fun i => hY _) hQ]
  rw [map_vector_eq_pi hY hi hν f hf]

/-! ### The main identity -/

theorem mem_permutations_range_iff (n : ℕ) (p : List ℕ) :
    p ∈ (List.range n).permutations.toFinset ↔ p ~ List.range n := by
  simp [List.mem_permutations]

theorem length_of_perm_range {n : ℕ} {p : List ℕ} (h : p ~ List.range n) : p.length = n := by
  rw [h.length_eq, List.length_range]

theorem nodup_of_perm_range {n : ℕ} {p : List ℕ} (h : p ~ List.range n) : p.Nodup :=
  h.nodup_iff.mpr (List.nodup_range)

/-- `∑_{p ∈ P} μ {Q (Y ∘ p)} = ∫⁻ #{p ∈ P : Q (Y ∘ p)}`. -/
theorem sum_measure_list_pred (hY : ∀ i, Measurable (Y i)) {n : ℕ} (Q : List ℝ → Prop)
    (hQ : MeasurableSet {v : Fin n → ℝ | Q (List.ofFn v)}) :
    ∑ p ∈ (List.range n).permutations.toFinset, μ {ω | Q (p.map fun i => Y i ω)} =
      ∫⁻ ω, (((List.range n).permutations.toFinset.filter
        fun p => Q (p.map fun i => Y i ω)).card : ℝ≥0∞) ∂μ := by
  set P := (List.range n).permutations.toFinset
  have hmeas : ∀ p ∈ P, MeasurableSet {ω | Q (p.map fun i => Y i ω)} := fun p hp =>
    measurableSet_list_pred hY Q hQ p
      (length_of_perm_range ((mem_permutations_range_iff n p).mp hp))
  calc ∑ p ∈ P, μ {ω | Q (p.map fun i => Y i ω)}
      = ∑ p ∈ P, ∫⁻ ω, {ω | Q (p.map fun i => Y i ω)}.indicator (1 : Ω → ℝ≥0∞) ω ∂μ := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [lintegral_indicator_one (hmeas p hp)]
    _ = ∫⁻ ω, ∑ p ∈ P, {ω | Q (p.map fun i => Y i ω)}.indicator (1 : Ω → ℝ≥0∞) ω ∂μ := by
        rw [lintegral_finsetSum]
        intro p hp
        exact measurable_one.indicator (hmeas p hp)
    _ = ∫⁻ ω, ((P.filter fun p => Q (p.map fun i => Y i ω)).card : ℝ≥0∞) ∂μ := by
        congr 1
        funext ω
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Set.indicator_apply]
        simp only [Set.mem_ofPred_eq, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Pi.one_apply]

/-- **Sparre Andersen for i.i.d. sequences**: `μ {N_n = k} = μ {T_n = k}`. -/
theorem measure_posCount_eq_measure_isFirstArgmax [IsProbabilityMeasure μ]
    (hY : ∀ i, Measurable (Y i)) (hi : iIndepFun Y μ) (hν : ∀ i, μ.map (Y i) = ν) (n k : ℕ) :
    μ {ω | posCount (fun i => Y i ω) (List.range n) = k} =
      μ {ω | IsFirstArgmax (fun i => Y i ω) (List.range n) k} := by
  set P := (List.range n).permutations.toFinset with hPdef
  have hP : ∀ p, p ∈ P ↔ p ~ List.range n := mem_permutations_range_iff n
  set QN : List ℝ → Prop := fun w => posCount id w = k
  set QT : List ℝ → Prop := fun w => IsFirstArgmax id w k
  have hQN : MeasurableSet {v : Fin n → ℝ | QN (List.ofFn v)} := measurableSet_posCount_ofFn n k
  have hQT : MeasurableSet {v : Fin n → ℝ | QT (List.ofFn v)} := measurableSet_isFirstArgmax_ofFn n k
  -- each term of the sums is the product-law value
  have hN : ∀ p ∈ P, μ {ω | QN (p.map fun i => Y i ω)} =
      (Measure.pi fun _ : Fin n => ν) {v | QN (List.ofFn v)} := fun p hp =>
    measure_list_pred_eq hY hi hν QN hQN p (length_of_perm_range ((hP p).mp hp))
      (nodup_of_perm_range ((hP p).mp hp))
  have hT : ∀ p ∈ P, μ {ω | QT (p.map fun i => Y i ω)} =
      (Measure.pi fun _ : Fin n => ν) {v | QT (List.ofFn v)} := fun p hp =>
    measure_list_pred_eq hY hi hν QT hQT p (length_of_perm_range ((hP p).mp hp))
      (nodup_of_perm_range ((hP p).mp hp))
  -- the sums agree by the combinatorial theorem
  have hsum : ∑ p ∈ P, μ {ω | QN (p.map fun i => Y i ω)} =
      ∑ p ∈ P, μ {ω | QT (p.map fun i => Y i ω)} := by
    rw [sum_measure_list_pred hY QN hQN, sum_measure_list_pred hY QT hQT, ← hPdef]
    congr 1
    funext ω
    congr 1
    simp only [QN, QT, posCount_map, isFirstArgmax_map_iff]
    convert card_posCount_eq_card_isFirstArgmax (fun i => Y i ω) hP k using 2
  rw [Finset.sum_congr rfl hN, Finset.sum_congr rfl hT, Finset.sum_const, Finset.sum_const] at hsum
  have hcard : (P.card : ℝ≥0∞) ≠ 0 := by
    have : List.range n ∈ P := (hP _).mpr (List.Perm.refl _)
    exact_mod_cast (Finset.card_pos.mpr ⟨_, this⟩).ne'
  have hpi : (Measure.pi fun _ : Fin n => ν) {v | QN (List.ofFn v)} =
      (Measure.pi fun _ : Fin n => ν) {v | QT (List.ofFn v)} := by
    simp only [nsmul_eq_mul] at hsum
    exact (ENNReal.mul_right_inj hcard (ENNReal.natCast_ne_top _)).mp hsum
  -- specialise to `p = range n`
  have hrange : List.range n ∈ P := (hP _).mpr (List.Perm.refl _)
  have e1 := hN _ hrange
  have e2 := hT _ hrange
  simp only [QN, QT, posCount_map, isFirstArgmax_map_iff] at e1 e2
  rw [e1, e2]
  exact hpi

end Fluctuation
end SwingRepair
