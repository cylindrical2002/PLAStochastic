import PLAStochastic.Swing.Ladder.Renewal.LadderPointCount

/-!
# Post-passage splitting of an i.i.d. renewal sequence

The renewal measure of the ladder law is only known to the project through the
`Icc 0 b` Laplace bound, which grows with `b`.  Every uniform statement about
the overshoot needs instead a bound on the renewal mass of a *window*, with a
constant independent of the position of the window.

The classical proof of that bound uses the strong Markov property at the first
passage of the level: after the first renewal above `c`, the remaining
increments are again i.i.d. and independent of the passage index, so the
renewals inside `(c, c+w]` are at most the renewals of a fresh sequence inside
`[0, w]`.

This file formalises exactly that step, for an abstract i.i.d. sequence.  The
splitting is stated as the single measure identity it needs: the event that the
passage index equals `m` is independent of the sum of the block of increments
with indices in `[m, m+j)`, whose law is the `j`-fold convolution.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Partial sums of an abstract i.i.d. increment sequence. -/
def renewalSum (H : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, H k ω

/-- The sum of the increments with indices in the block `[m, m+j)`. -/
def renewalBlockSum (H : ℕ → Ω → ℝ) (m j : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.Ico m (m + j), H k ω

/-- The first index at which the partial sums exceed the level `c`.  The value
is `0` when no index works; on the events used below the infimum is attained. -/
def renewalPassageIndex (H : ℕ → Ω → ℝ) (c : ℝ) (ω : Ω) : ℕ :=
  sInf {n | c < renewalSum H n ω}

omit [MeasurableSpace Ω] in
@[simp] theorem renewalSum_zero (H : ℕ → Ω → ℝ) (ω : Ω) :
    renewalSum H 0 ω = 0 := by simp [renewalSum]

omit [MeasurableSpace Ω] in
@[simp] theorem renewalBlockSum_zero (H : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    renewalBlockSum H m 0 ω = 0 := by simp [renewalBlockSum]

omit [MeasurableSpace Ω] in
theorem renewalBlockSum_succ (H : ℕ → Ω → ℝ) (m j : ℕ) (ω : Ω) :
    renewalBlockSum H m (j + 1) ω =
      renewalBlockSum H m j ω + H (m + j) ω := by
  unfold renewalBlockSum
  rw [show m + (j + 1) = (m + j) + 1 by ring,
    Finset.sum_Ico_succ_top (by omega : m ≤ m + j)]

theorem renewalSum_measurable {H : ℕ → Ω → ℝ}
    (hH : ∀ n, Measurable (H n)) (n : ℕ) : Measurable (renewalSum H n) :=
  Finset.measurable_sum _ (fun k _ => hH k)

theorem renewalBlockSum_measurable {H : ℕ → Ω → ℝ}
    (hH : ∀ n, Measurable (H n)) (m j : ℕ) :
    Measurable (renewalBlockSum H m j) :=
  Finset.measurable_sum _ (fun k _ => hH k)

/-! ### The block law -/

theorem renewalBlockSum_map [IsProbabilityMeasure μ] {H : ℕ → Ω → ℝ} {ν : Measure ℝ}
    (hH : ∀ n, Measurable (H n)) (hi : iIndepFun H μ)
    (hmap : ∀ n, μ.map (H n) = ν) (m j : ℕ) :
    μ.map (renewalBlockSum H m j) = measureConvPow ν j := by
  induction j with
  | zero =>
    have hconst : renewalBlockSum H m 0 = fun _ : Ω => (0 : ℝ) := by
      funext ω; simp
    rw [hconst, Measure.map_const, measureConvPow_zero]
    simp
  | succ j ih =>
    have hfun : renewalBlockSum H m (j + 1) =
        fun ω => renewalBlockSum H m j ω + H (m + j) ω :=
      funext (fun ω => renewalBlockSum_succ H m j ω)
    have hnot : (m + j) ∉ Finset.Ico m (m + j) := by simp
    have hindep : IndepFun (renewalBlockSum H m j) (H (m + j)) μ := by
      have h := hi.indepFun_finsetSum_of_notMem hH hnot
      have heq : (∑ k ∈ Finset.Ico m (m + j), H k) = renewalBlockSum H m j := by
        funext ω
        simp [renewalBlockSum, Finset.sum_apply]
      rwa [heq] at h
    rw [hfun, map_add_of_indepFun (renewalBlockSum_measurable hH m j) (hH (m + j)) hindep,
      ih, hmap (m + j), measureConvPow_succ]

/-! ### The passage index -/

omit [MeasurableSpace Ω] in
theorem renewalPassageIndex_eq_iff {H : ℕ → Ω → ℝ} (c : ℝ) (ω : Ω) (m : ℕ) (hm : 0 < m) :
    renewalPassageIndex H c ω = m ↔
      (c < renewalSum H m ω ∧ ∀ k < m, renewalSum H k ω ≤ c) := by
  unfold renewalPassageIndex
  constructor
  · intro h
    have hne : {n | c < renewalSum H n ω}.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      rw [hempty] at h
      simp only [Nat.sInf_empty] at h
      omega
    have hmem : m ∈ {n | c < renewalSum H n ω} := by
      rw [← h]
      exact Nat.sInf_mem hne
    refine ⟨hmem, fun k hk => ?_⟩
    by_contra hcon
    have hk' : k ∈ {n | c < renewalSum H n ω} := by
      simp only [Set.mem_ofPred_eq]
      linarith [not_le.mp hcon]
    have := Nat.sInf_le hk'
    omega
  · rintro ⟨h1, h2⟩
    have hmem : m ∈ {n | c < renewalSum H n ω} := h1
    have hle := Nat.sInf_le hmem
    by_contra hcon
    have hlt : sInf {n | c < renewalSum H n ω} < m := by omega
    have := Nat.sInf_mem (⟨m, hmem⟩ : {n | c < renewalSum H n ω}.Nonempty)
    exact absurd this (by
      have := h2 _ hlt
      simp only [Set.mem_ofPred_eq]
      linarith)

omit [MeasurableSpace Ω] in
theorem renewalPassageIndex_pos {H : ℕ → Ω → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} {ω : Ω}
    (hn : c < renewalSum H n ω) : 0 < renewalPassageIndex H c ω := by
  have hne : {k | c < renewalSum H k ω}.Nonempty := ⟨n, hn⟩
  have hmem := Nat.sInf_mem hne
  rcases Nat.eq_zero_or_pos (renewalPassageIndex H c ω) with h0 | hpos
  · exfalso
    unfold renewalPassageIndex at h0
    rw [h0] at hmem
    simp only [Set.mem_ofPred_eq, renewalSum_zero] at hmem
    linarith
  · exact hpos

omit [MeasurableSpace Ω] in
theorem renewalPassageIndex_eq_zero_iff {H : ℕ → Ω → ℝ} (c : ℝ) (ω : Ω) :
    renewalPassageIndex H c ω = 0 ↔
      (c < renewalSum H 0 ω ∨ ∀ k, renewalSum H k ω ≤ c) := by
  unfold renewalPassageIndex
  constructor
  · intro h
    by_cases hne : {k | c < renewalSum H k ω}.Nonempty
    · left
      have hmem := Nat.sInf_mem hne
      rw [h] at hmem
      exact hmem
    · right
      intro k
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have hk : k ∉ {k | c < renewalSum H k ω} := by rw [hne]; simp
      simpa using hk
  · rintro (h | h)
    · exact Nat.eq_zero_of_le_zero (Nat.sInf_le h)
    · have hempty : {k | c < renewalSum H k ω} = ∅ := by
        ext k
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact h k
      rw [hempty]
      exact Nat.sInf_empty

theorem renewalPassageIndex_measurableSet {H : ℕ → Ω → ℝ}
    (hH : ∀ n, Measurable (H n)) (c : ℝ) (m : ℕ) :
    MeasurableSet {ω | renewalPassageIndex H c ω = m} := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hset : {ω | renewalPassageIndex H c ω = 0} =
        (renewalSum H 0 ⁻¹' Ioi c) ∪ ⋂ k : ℕ, (renewalSum H k ⁻¹' Iic c) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iInter, Set.mem_preimage,
        Set.mem_Ioi, Set.mem_Iic]
      exact renewalPassageIndex_eq_zero_iff c ω
    rw [hset]
    exact ((renewalSum_measurable hH 0) measurableSet_Ioi).union
      (MeasurableSet.iInter (fun k => (renewalSum_measurable hH k) measurableSet_Iic))
  · have hset : {ω | renewalPassageIndex H c ω = m} =
        (renewalSum H m ⁻¹' Ioi c) ∩
          ⋂ k ∈ Finset.range m, (renewalSum H k ⁻¹' Iic c) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
        Set.mem_Ioi, Set.mem_Iic, Finset.mem_range]
      exact renewalPassageIndex_eq_iff c ω m hm
    rw [hset]
    refine ((renewalSum_measurable hH m) measurableSet_Ioi).inter ?_
    exact MeasurableSet.biInter (Set.to_countable _)
      (fun k _ => (renewalSum_measurable hH k) measurableSet_Iic)


/-! ### The splitting identity -/

/-- **Post-passage splitting.**  For a positive passage index the event
`{passage index = m}` is determined by the first `m` increments, while the sum
of the block `[m, m+j)` is determined by disjoint increments; hence the joint
measure factorises and the block sum contributes the `j`-fold convolution. -/
theorem measure_passage_inter_blockSum_le [IsProbabilityMeasure μ]
    {H : ℕ → Ω → ℝ} {ν : Measure ℝ}
    (hH : ∀ n, Measurable (H n)) (hi : iIndepFun H μ)
    (hmap : ∀ n, μ.map (H n) = ν) (c w : ℝ) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    μ ({ω | renewalPassageIndex H c ω = m} ∩ {ω | renewalBlockSum H m j ω ≤ w}) =
      μ {ω | renewalPassageIndex H c ω = m} * measureConvPow ν j (Iic w) := by
  classical
  set Spre : Finset ℕ := Finset.range m with hSpre
  set Sblk : Finset ℕ := Finset.Ico m (m + j) with hSblk
  have hdisj : Disjoint Spre Sblk := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [hSpre, Finset.mem_range] at hi1
    simp only [hSblk, Finset.mem_Ico] at hi2
    omega
  have hind := hi.indepFun_finset Spre Sblk hdisj hH
  -- the two measurable read-off maps
  set φ : ((i : {x // x ∈ Spre}) → ℝ) → (ℕ → ℝ) :=
    fun x i => if h : i ∈ Spre then x ⟨i, h⟩ else 0 with hφdef
  set ψ : ((i : {x // x ∈ Sblk}) → ℝ) → ℝ := fun x => ∑ i, x i with hψdef
  have hφ : Measurable φ := by
    apply measurable_pi_lambda
    intro i
    by_cases h : i ∈ Spre
    · simp only [hφdef, dif_pos h]
      exact measurable_pi_apply _
    · simp only [hφdef, dif_neg h]
      exact measurable_const
  have hψ : Measurable ψ := by
    simpa only [hψdef] using
      (Finset.measurable_sum Finset.univ
        (fun i (_ : i ∈ (Finset.univ : Finset {x // x ∈ Sblk})) => measurable_pi_apply i))
  have hcomp := hind.comp hφ hψ
  -- identify the two events as preimages
  set A : Set (ℕ → ℝ) :=
    {y | c < ∑ i ∈ Finset.range m, y i} ∩
      ⋂ k ∈ Finset.range m, {y | ∑ i ∈ Finset.range k, y i ≤ c} with hAdef
  have hA : MeasurableSet A := by
    have hsum : ∀ k : ℕ, Measurable (fun y : ℕ → ℝ => ∑ i ∈ Finset.range k, y i) :=
      fun k => Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
    refine MeasurableSet.inter ?_ ?_
    · exact (hsum m) measurableSet_Ioi
    · exact MeasurableSet.biInter (Set.to_countable _)
        (fun k _ => (hsum k) measurableSet_Iic)
  have hpartial : ∀ (ω : Ω) (k : ℕ), k ≤ m →
      ∑ i ∈ Finset.range k, (φ (fun i : {x // x ∈ Spre} => H i ω)) i =
        renewalSum H k ω := by
    intro ω k hk
    unfold renewalSum
    refine Finset.sum_congr rfl (fun i hi' => ?_)
    have hi'' : i ∈ Spre := by
      simp only [hSpre, Finset.mem_range]
      simp only [Finset.mem_range] at hi'
      omega
    simp only [hφdef, dif_pos hi'']
  have hevent1 : {ω | renewalPassageIndex H c ω = m} =
      (fun ω => φ (fun i : {x // x ∈ Spre} => H i ω)) ⁻¹' A := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hAdef, Set.mem_inter_iff,
      Set.mem_iInter, Finset.mem_range]
    rw [renewalPassageIndex_eq_iff c ω m hm]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [hpartial ω m le_rfl]; exact h1, fun k hk => ?_⟩
      rw [hpartial ω k (le_of_lt hk)]
      exact h2 k hk
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [← hpartial ω m le_rfl]; exact h1, fun k hk => ?_⟩
      rw [← hpartial ω k (le_of_lt hk)]
      exact h2 k hk
  have hevent2 : {ω | renewalBlockSum H m j ω ≤ w} =
      (fun ω => ψ (fun i : {x // x ∈ Sblk} => H i ω)) ⁻¹' (Iic w) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic, hψdef]
    rw [show (∑ i : {x // x ∈ Sblk}, H (i : ℕ) ω) = renewalBlockSum H m j ω by
      rw [Finset.sum_coe_sort Sblk (fun i => H i ω)]
      rfl]
  have hfact := hcomp.measure_inter_preimage_eq_mul A (Iic w) hA measurableSet_Iic
  rw [hevent1, hevent2]
  refine hfact.trans ?_
  congr 1
  have hcompeq : (ψ ∘ fun (a : Ω) (i : {x // x ∈ Sblk}) => H (i : ℕ) a) =
      renewalBlockSum H m j := by
    funext ω
    simp only [Function.comp_apply, hψdef]
    rw [Finset.sum_coe_sort Sblk (fun i => H i ω)]
    rfl
  rw [hcompeq]
  have hmapblk : μ.map (renewalBlockSum H m j) = measureConvPow ν j :=
    renewalBlockSum_map hH hi hmap m j
  rw [← hmapblk, Measure.map_apply (renewalBlockSum_measurable hH m j) measurableSet_Iic]


/-! ### The position-uniform window bound -/

theorem tsum_ite_shift (m : ℕ) (f : ℕ → ℝ≥0∞) :
    (∑' n : ℕ, (if m ≤ n then f (n - m) else 0)) = ∑' j : ℕ, f j := by
  have hinj : Function.Injective (fun j : ℕ => m + j) := by
    intro a b h
    simp only at h
    omega
  have hsupp : Function.support (fun n : ℕ => if m ≤ n then f (n - m) else 0) ⊆
      Set.range (fun j : ℕ => m + j) := by
    intro n hn
    simp only [Function.mem_support] at hn
    by_cases h : m ≤ n
    · exact ⟨n - m, by simp only; omega⟩
    · simp [h] at hn
  rw [← hinj.tsum_eq hsupp]
  refine (tsum_congr fun j => ?_).symm
  simp

omit [MeasurableSpace Ω] in
theorem renewalBlockSum_eq_sub {H : ℕ → Ω → ℝ} {m n : ℕ} (hmn : m ≤ n) (ω : Ω) :
    renewalBlockSum H m (n - m) ω = renewalSum H n ω - renewalSum H m ω := by
  unfold renewalBlockSum renewalSum
  rw [show m + (n - m) = n by omega]
  exact Finset.sum_Ico_eq_sub _ hmn

/--
**The renewal mass of a window is bounded by the renewal mass at the origin.**
For an i.i.d. nonnegative-increment sequence the expected number of partial
sums inside `(c, c+w]` is at most the expected number inside `Iic w`, with no
dependence on the position `c ≥ 0`.  This is the strong-Markov step: after the
first passage of `c` the remaining increments are a fresh copy.
-/
theorem tsum_measure_renewalSum_Ioc_le [IsProbabilityMeasure μ]
    {H : ℕ → Ω → ℝ} {ν : Measure ℝ}
    (hH : ∀ n, Measurable (H n)) (hi : iIndepFun H μ)
    (hmap : ∀ n, μ.map (H n) = ν) {c w : ℝ} (hc : 0 ≤ c) :
    (∑' n : ℕ, μ {ω | renewalSum H n ω ∈ Ioc c (c + w)}) ≤
      ∑' j : ℕ, measureConvPow ν j (Iic w) := by
  classical
  set T : Ω → ℕ := renewalPassageIndex H c with hTdef
  set E : ℕ → Set Ω := fun n => {ω | renewalSum H n ω ∈ Ioc c (c + w)} with hEdef
  set P : ℕ → ℝ≥0∞ := fun j => measureConvPow ν j (Iic w) with hPdef
  have hEmeas : ∀ n, MeasurableSet (E n) := fun n =>
    (renewalSum_measurable hH n) measurableSet_Ioc
  have hTmeas : ∀ m, MeasurableSet {ω | T ω = m} := fun m =>
    renewalPassageIndex_measurableSet hH c m
  -- (1) decompose each event by the value of the passage index
  have hdecomp : ∀ n, μ (E n) = ∑' m : ℕ, μ ({ω | T ω = m} ∩ E n) := by
    intro n
    have hunion : E n = ⋃ m : ℕ, ({ω | T ω = m} ∩ E n) := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro h
        exact ⟨T ω, rfl, h⟩
      · rintro ⟨m, _, h⟩
        exact h
    conv_lhs => rw [hunion]
    refine measure_iUnion ?_ (fun m => (hTmeas m).inter (hEmeas n))
    intro m1 m2 hne
    refine Set.disjoint_left.mpr ?_
    intro ω h1 h2
    have e1 : T ω = m1 := h1.1
    have e2 : T ω = m2 := h2.1
    exact hne (by rw [← e1, ← e2])
  -- (2) the row bound
  have hrow : ∀ m : ℕ, (∑' n : ℕ, μ ({ω | T ω = m} ∩ E n)) ≤
      μ {ω | T ω = m} * ∑' j : ℕ, P j := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hm
    · -- the passage index is positive on every event `E n`
      have hzero : ∀ n, μ ({ω | T ω = m} ∩ E n) = 0 := by
        intro n
        have : ({ω | T ω = m} ∩ E n) = ∅ := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro hTm hEn
          have hgt : c < renewalSum H n ω := (Set.mem_Ioc.mp hEn).1
          have hpos := renewalPassageIndex_pos (H := H) hc hgt
          rw [hTdef] at hTm
          omega
        rw [this, measure_empty]
      simp only [hzero, tsum_zero]
      simp
    · have hstep : ∀ n : ℕ, μ ({ω | T ω = m} ∩ E n) ≤
          (if m ≤ n then μ {ω | T ω = m} * P (n - m) else 0) := by
        intro n
        by_cases hmn : m ≤ n
        · have hsub : ({ω | T ω = m} ∩ E n) ⊆
              ({ω | T ω = m} ∩ {ω | renewalBlockSum H m (n - m) ω ≤ w}) := by
            intro ω hω
            obtain ⟨hTm, hEn⟩ := hω
            have hTm' : renewalPassageIndex H c ω = m := hTm
            obtain ⟨hgt, _hle⟩ := (renewalPassageIndex_eq_iff (H := H) c ω m hm).mp hTm'
            obtain ⟨_, hSn⟩ := Set.mem_Ioc.mp hEn
            refine ⟨hTm, ?_⟩
            simp only [Set.mem_ofPred_eq]
            rw [renewalBlockSum_eq_sub hmn ω]
            linarith
          have hmono : μ ({ω | T ω = m} ∩ E n) ≤
              μ ({ω | T ω = m} ∩ {ω | renewalBlockSum H m (n - m) ω ≤ w}) :=
            measure_mono hsub
          have heq := measure_passage_inter_blockSum_le hH hi hmap c w hm (n - m)
          rw [heq] at hmono
          exact le_trans hmono (by rw [if_pos hmn])
        · have hempty : ({ω | T ω = m} ∩ E n) = ∅ := by
            ext ω
            simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
              iff_false, not_and]
            intro hTm hEn
            have hTm' : renewalPassageIndex H c ω = m := hTm
            obtain ⟨_, hle⟩ := (renewalPassageIndex_eq_iff (H := H) c ω m hm).mp hTm'
            have hnm : n < m := by omega
            have := hle n hnm
            have hgt : c < renewalSum H n ω := (Set.mem_Ioc.mp hEn).1
            linarith
          rw [hempty, measure_empty, if_neg hmn]
      calc (∑' n : ℕ, μ ({ω | T ω = m} ∩ E n))
          ≤ ∑' n : ℕ, (if m ≤ n then μ {ω | T ω = m} * P (n - m) else 0) :=
            ENNReal.tsum_le_tsum hstep
        _ = ∑' j : ℕ, μ {ω | T ω = m} * P j :=
            tsum_ite_shift m (fun j => μ {ω | T ω = m} * P j)
        _ = μ {ω | T ω = m} * ∑' j : ℕ, P j := ENNReal.tsum_mul_left
  -- (3) assemble
  have htotal : (∑' m : ℕ, μ {ω | T ω = m}) = 1 := by
    have hunion : (⋃ m : ℕ, {ω | T ω = m}) = Set.univ := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨T ω, rfl⟩
    have hdisj : Pairwise (Function.onFun Disjoint (fun m : ℕ => {ω | T ω = m})) := by
      intro m1 m2 hne
      refine Set.disjoint_left.mpr ?_
      intro ω h1 h2
      have e1 : T ω = m1 := h1
      have e2 : T ω = m2 := h2
      exact hne (by rw [← e1, ← e2])
    have hmu : μ (⋃ m : ℕ, {ω | T ω = m}) = ∑' m : ℕ, μ {ω | T ω = m} :=
      measure_iUnion hdisj hTmeas
    rw [hunion, measure_univ] at hmu
    exact hmu.symm
  calc (∑' n : ℕ, μ (E n))
      = ∑' n : ℕ, ∑' m : ℕ, μ ({ω | T ω = m} ∩ E n) := tsum_congr hdecomp
    _ = ∑' m : ℕ, ∑' n : ℕ, μ ({ω | T ω = m} ∩ E n) := ENNReal.tsum_comm
    _ ≤ ∑' m : ℕ, μ {ω | T ω = m} * ∑' j : ℕ, P j := ENNReal.tsum_le_tsum hrow
    _ = (∑' m : ℕ, μ {ω | T ω = m}) * ∑' j : ℕ, P j := ENNReal.tsum_mul_right
    _ = ∑' j : ℕ, P j := by rw [htotal, one_mul]

end SwingRepair
