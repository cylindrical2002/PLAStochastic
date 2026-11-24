import PLAStochastic.Swing.Entrance.Local.Crossing
import PLAStochastic.Swing.Algorithm.Measurability
import PLAStochastic.Swing.Repair.GeometricRejectionTail

/-!
# The adaptive cut is a stopping time

The cut `τ = inf {n ≥ 1 : n (b_n - a_n) ≤ d_E}` is a sample index: the width at `n` reads the
samples `y_1, …, y_n`, i.e. the increments `X_0, …, X_{n-1}`. In the zero-based increment
filtration (`incrementFiltration X hX k = σ(X_0, …, X_k)`) the stopping time is therefore the
last observed increment index `κ = τ - 1` (`entranceCutIndex`), and the first fresh increment
after the cut is `X_{κ+1} = X_τ`.

* `entranceCutIndex_isStoppingTime`: `κ` is a stopping time;
* `entranceCutIndex_ae_ne_top`: for `E ≥ 0` and iid standard Gaussian increments, `κ < ∞`
  almost surely, because the cone width is negative at the first repair rejection;
* the side, the frozen endpoint, the width and the grid area at the cut (evaluated at
  `entranceCutNat`, the cut as a natural number with `0` on `{τ = ∞}`), and the truncation
  event `entranceGood`, are measurable for the stopped σ-algebra of `κ`.
-/

namespace SwingRepair

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-! ## The cut as a first passage -/

theorem entranceCut_le_iff (y : ℕ → ℝ) (E : ℝ) (i : ℕ) :
    entranceCut y E ≤ (i : ℕ∞) ↔
      ∃ n, 1 ≤ n ∧ n ≤ i ∧ entranceWidth y E n ≤ entranceCutLevel E := by
  classical
  unfold entranceCut
  split_ifs with h
  · rw [Nat.cast_le, Nat.find_le_iff]
    constructor
    · rintro ⟨n, hn, h1, h2⟩
      exact ⟨n, h1, hn, h2⟩
    · rintro ⟨n, h1, hn, h2⟩
      exact ⟨n, hn, h1, h2⟩
  · constructor
    · intro h'
      exact absurd (top_le_iff.mp h') (ENat.natCast_ne_top i)
    · rintro ⟨n, h1, -, h2⟩
      exact absurd ⟨n, h1, h2⟩ h

theorem entranceCut_ne_zero (y : ℕ → ℝ) (E : ℝ) : entranceCut y E ≠ 0 := by
  intro h
  have h' : entranceCut y E ≤ ((0 : ℕ) : ℕ∞) := by simp [h]
  obtain ⟨n, h1, h2, -⟩ := (entranceCut_le_iff y E 0).mp h'
  omega

/-- The cut as a natural number, `0` when there is no cut. -/
def entranceCutNat (y : ℕ → ℝ) (E : ℝ) : ℕ := (entranceCut y E).toNat

theorem entranceCutNat_of_eq {y : ℕ → ℝ} {E : ℝ} {n : ℕ} (h : entranceCut y E = (n : ℕ∞)) :
    entranceCutNat y E = n := by
  simp [entranceCutNat, h]

/-- The good event pins down the cut as the natural number in its statement. -/
theorem entranceGood_iff (y : ℕ → ℝ) (E δ M : ℝ) :
    entranceGood y E δ M ↔ entranceCut y E ≠ ⊤ ∧
      δ * E ^ 2 ≤ entranceCutNat y E ∧ (entranceCutNat y E : ℝ) ≤ M * E ^ 2 ∧
      |E * entranceFrozenSlope y E (entranceCutNat y E)| ≤ M ∧
      entranceCutLevel E / 2 ≤ entranceWidth y E (entranceCutNat y E) ∧
      entranceWidth y E (entranceCutNat y E) ≤ entranceCutLevel E := by
  constructor
  · rintro ⟨n, hn, h⟩
    rw [entranceCutNat_of_eq hn]
    exact ⟨by rw [hn]; exact ENat.natCast_ne_top n, h⟩
  · rintro ⟨hne, h⟩
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
    rw [entranceCutNat_of_eq hn.symm] at h
    exact ⟨n, hn.symm, h⟩

/-! ## The stopping time `κ = τ - 1` -/

variable {Ω : Type*}

/-- The last observed increment index at the cut, `κ = τ - 1` (`⊤` if there is no cut). -/
def entranceCutIndex (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : WithTop ℕ :=
  match entranceCut (entrancePath X ω) E with
  | ⊤ => ⊤
  | (n : ℕ) => ((n - 1 : ℕ) : WithTop ℕ)

theorem entranceCutIndex_of_top {X : ℕ → Ω → ℝ} {E : ℝ} {ω : Ω}
    (h : entranceCut (entrancePath X ω) E = ⊤) : entranceCutIndex X E ω = ⊤ := by
  unfold entranceCutIndex
  rw [h]
  rfl

theorem entranceCutIndex_of_coe {X : ℕ → Ω → ℝ} {E : ℝ} {ω : Ω} {n : ℕ}
    (h : entranceCut (entrancePath X ω) E = (n : ℕ∞)) :
    entranceCutIndex X E ω = ((n - 1 : ℕ) : WithTop ℕ) := by
  unfold entranceCutIndex
  rw [h]

theorem entranceCutIndex_eq_top_iff (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) :
    entranceCutIndex X E ω = ⊤ ↔ entranceCut (entrancePath X ω) E = ⊤ := by
  by_cases htop : entranceCut (entrancePath X ω) E = ⊤
  · exact ⟨fun _ => htop, fun _ => entranceCutIndex_of_top htop⟩
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [entranceCutIndex_of_coe hn.symm]
    exact ⟨fun h => absurd h WithTop.coe_ne_top, fun h => absurd h htop⟩

theorem entranceCutIndex_eq_coe_iff (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) (k : ℕ) :
    entranceCutIndex X E ω = (k : WithTop ℕ) ↔
      entranceCut (entrancePath X ω) E = ((k + 1 : ℕ) : ℕ∞) := by
  have hne := entranceCut_ne_zero (entrancePath X ω) E
  by_cases htop : entranceCut (entrancePath X ω) E = ⊤
  · rw [entranceCutIndex_of_top htop, htop]
    exact ⟨fun h => absurd h.symm WithTop.coe_ne_top, fun h => absurd h (ENat.top_ne_natCast _)⟩
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    have hn0 : n ≠ 0 := fun h => hne (by rw [← hn, h]; rfl)
    rw [entranceCutIndex_of_coe hn.symm, ← hn]
    norm_cast
    omega

theorem entranceCutIndex_le_iff (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) (i : ℕ) :
    entranceCutIndex X E ω ≤ (i : WithTop ℕ) ↔
      entranceCut (entrancePath X ω) E ≤ ((i + 1 : ℕ) : ℕ∞) := by
  have hne := entranceCut_ne_zero (entrancePath X ω) E
  by_cases htop : entranceCut (entrancePath X ω) E = ⊤
  · rw [entranceCutIndex_of_top htop, htop]
    exact ⟨fun h => absurd (top_le_iff.mp h) WithTop.coe_ne_top,
      fun h => absurd (top_le_iff.mp h) (ENat.natCast_ne_top _)⟩
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    have hn0 : n ≠ 0 := fun h => hne (by rw [← hn, h]; rfl)
    rw [entranceCutIndex_of_coe hn.symm, ← hn]
    norm_cast
    omega

theorem entranceCutNat_of_index {X : ℕ → Ω → ℝ} {E : ℝ} {ω : Ω} {k : ℕ}
    (h : entranceCutIndex X E ω = (k : WithTop ℕ)) :
    entranceCutNat (entrancePath X ω) E = k + 1 :=
  entranceCutNat_of_eq ((entranceCutIndex_eq_coe_iff X E ω k).mp h)

theorem entranceCutNat_of_index_top {X : ℕ → Ω → ℝ} {E : ℝ} {ω : Ω}
    (h : entranceCutIndex X E ω = ⊤) : entranceCutNat (entrancePath X ω) E = 0 := by
  simp [entranceCutNat, (entranceCutIndex_eq_top_iff X E ω).mp h]

/-! ## Measurability of the quantities at a fixed index -/

variable [mΩ : MeasurableSpace Ω] {X : ℕ → Ω → ℝ}

section FixedIndex

variable (hX : ∀ k, Measurable (X k)) {n k : ℕ} (hnk : n ≤ k + 1) (E : ℝ)
include hX hnk

theorem measurable_entrancePath_at {i : ℕ} (hi : i ≤ n) :
    Measurable[incrementFiltration X hX k] fun ω => entrancePath X ω i :=
  cumulativeSamples_measurable_at hX (hi.trans hnk)

theorem measurable_entranceLower_at :
    Measurable[incrementFiltration X hX k] fun ω => entranceLower (entrancePath X ω) E n := by
  by_cases hn : (Finset.Icc 1 n).Nonempty
  · simp only [entranceLower, dif_pos hn]
    exact @measurable_nativeConeLower Ω (incrementFiltration X hX k) ℕ (Finset.Icc 1 n) hn
      (fun j => (j : ℝ)) (fun i ω => entrancePath X ω i) 0 E (fun ω => entrancePath X ω 0)
      (measurable_entrancePath_at hX hnk (Nat.zero_le n))
      (fun i hi => measurable_entrancePath_at hX hnk (Finset.mem_Icc.mp hi).2)
  · simp only [entranceLower, dif_neg hn]
    exact measurable_const

theorem measurable_entranceUpper_at :
    Measurable[incrementFiltration X hX k] fun ω => entranceUpper (entrancePath X ω) E n := by
  by_cases hn : (Finset.Icc 1 n).Nonempty
  · simp only [entranceUpper, dif_pos hn]
    exact @measurable_nativeConeUpper Ω (incrementFiltration X hX k) ℕ (Finset.Icc 1 n) hn
      (fun j => (j : ℝ)) (fun i ω => entrancePath X ω i) 0 E (fun ω => entrancePath X ω 0)
      (measurable_entrancePath_at hX hnk (Nat.zero_le n))
      (fun i hi => measurable_entrancePath_at hX hnk (Finset.mem_Icc.mp hi).2)
  · simp only [entranceUpper, dif_neg hn]
    exact measurable_const

theorem measurable_entranceWidth_at :
    Measurable[incrementFiltration X hX k] fun ω => entranceWidth (entrancePath X ω) E n :=
  ((measurable_entranceUpper_at hX hnk E).sub (measurable_entranceLower_at hX hnk E)).const_mul _

theorem measurableSet_entranceRefreshesLower_at :
    MeasurableSet[incrementFiltration X hX k]
      {ω | entranceRefreshesLower (entrancePath X ω) E n} := by
  have hs : Measurable[incrementFiltration X hX k]
      fun ω => slopeLower (n : ℝ) (entrancePath X ω n) 0 (entrancePath X ω 0) E :=
    ((((measurable_entrancePath_at hX hnk le_rfl).sub
      (measurable_entrancePath_at hX hnk (Nat.zero_le n))).sub_const E).div_const _)
  exact measurableSet_eq_fun (measurable_entranceLower_at hX hnk E) hs

theorem measurable_entranceSide_at :
    Measurable[incrementFiltration X hX k] fun ω => entranceSide (entrancePath X ω) E n := by
  unfold entranceSide
  exact Measurable.ite (measurableSet_entranceRefreshesLower_at hX hnk E) measurable_const
    measurable_const

theorem measurable_entranceFrozenSlope_at :
    Measurable[incrementFiltration X hX k]
      fun ω => entranceFrozenSlope (entrancePath X ω) E n := by
  unfold entranceFrozenSlope
  exact Measurable.ite (measurableSet_entranceRefreshesLower_at hX hnk E)
    (measurable_entranceUpper_at hX hnk E) (measurable_entranceLower_at hX hnk E)

theorem measurable_entranceGridArea_at :
    Measurable[incrementFiltration X hX k]
      fun ω => entranceGridArea (entrancePath X ω) E n := by
  refine Measurable.const_mul (Finset.measurable_sum _ fun i hi => ?_) _
  have hi' := (Finset.mem_Icc.mp hi).2
  exact Measurable.const_mul (((measurable_entranceSide_at hX hnk E).mul
      (measurable_entrancePath_at hX hnk hi')).sub
    (((measurable_entranceSide_at hX hnk E).mul
      (measurable_entranceFrozenSlope_at hX hnk E)).mul_const _)) _

end FixedIndex

theorem measurableSet_entranceWidth_le_at (hX : ∀ k, Measurable (X k)) {n k : ℕ}
    (hnk : n ≤ k + 1) (E : ℝ) :
    MeasurableSet[incrementFiltration X hX k]
      {ω | entranceWidth (entrancePath X ω) E n ≤ entranceCutLevel E} :=
  measurableSet_le (measurable_entranceWidth_at hX hnk E) measurable_const

/-- The cut index is a stopping time of the increment filtration. -/
theorem entranceCutIndex_isStoppingTime (hX : ∀ k, Measurable (X k)) (E : ℝ) :
    IsStoppingTime (incrementFiltration X hX) (entranceCutIndex X E) := by
  intro i
  have heq : {ω | entranceCutIndex X E ω ≤ (i : WithTop ℕ)} =
      ⋃ n ∈ Finset.Icc 1 (i + 1),
        {ω | entranceWidth (entrancePath X ω) E n ≤ entranceCutLevel E} := by
    ext ω
    simp only [mem_ofPred_eq, entranceCutIndex_le_iff, entranceCut_le_iff, mem_iUnion,
      Finset.mem_Icc, exists_prop]
    constructor
    · rintro ⟨n, h1, h2, h3⟩
      exact ⟨n, ⟨h1, h2⟩, h3⟩
    · rintro ⟨n, ⟨h1, h2⟩, h3⟩
      exact ⟨n, h1, h2, h3⟩
  have hU : MeasurableSet[incrementFiltration X hX i] (⋃ n ∈ Finset.Icc 1 (i + 1),
      {ω | entranceWidth (entrancePath X ω) E n ≤ entranceCutLevel E}) :=
    Finset.measurableSet_biUnion _ fun n hn =>
      measurableSet_entranceWidth_le_at hX (Finset.mem_Icc.mp hn).2 E
  convert hU using 1
  exact heq

/-! ## The cut is almost surely finite -/

omit mΩ in
/-- At a repair rejection the cone is empty, so the width is negative and the cut has
occurred. -/
theorem entranceCut_le_of_repairRejected {E : ℝ} (hE : 0 ≤ E) {n : ℕ} {ω : Ω}
    (h : repairRejected X (2 * E) n ω) :
    entranceCut (entrancePath X ω) E ≤ ((n + 1 : ℕ) : ℕ∞) := by
  rw [entranceCut_le_iff]
  refine ⟨n + 1, by omega, le_rfl, ?_⟩
  unfold repairRejected at h
  rw [prefixCone_nonempty_iff_pairwise_bounds] at h
  push Not at h
  obtain ⟨i, hi, j, hj, hlt⟩ := h
  have hne : (Finset.Icc 1 (n + 1)).Nonempty := Finset.nonempty_Icc.mpr (by omega)
  have hlow : slopeLower (i : ℝ) (entrancePath X ω i) 0 (entrancePath X ω 0) E ≤
      entranceLower (entrancePath X ω) E (n + 1) := by
    simp only [entranceLower, dif_pos hne, nativeConeLower]
    exact Finset.le_sup' (fun i : ℕ => slopeLower (i : ℝ) (entrancePath X ω i) 0
      (entrancePath X ω 0) E) (by simpa using hi)
  have hup : entranceUpper (entrancePath X ω) E (n + 1) ≤
      slopeUpper (j : ℝ) (entrancePath X ω j) 0 (entrancePath X ω 0) E := by
    simp only [entranceUpper, dif_pos hne, nativeConeUpper]
    exact Finset.inf'_le (fun i : ℕ => slopeUpper (i : ℝ) (entrancePath X ω i) 0
      (entrancePath X ω 0) E) (by simpa using hj)
  have hlt' : slopeUpper (j : ℝ) (entrancePath X ω j) 0 (entrancePath X ω 0) E <
      slopeLower (i : ℝ) (entrancePath X ω i) 0 (entrancePath X ω 0) E := by
    have h2 : 2 * E / 2 = E := by ring
    simpa only [Nat.cast_zero, h2, entrancePath] using hlt
  have hd : 0 ≤ entranceCutLevel E := Real.rpow_nonneg hE _
  unfold entranceWidth
  have : entranceUpper (entrancePath X ω) E (n + 1) -
      entranceLower (entrancePath X ω) E (n + 1) < 0 := by linarith
  have hpos : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- For iid standard Gaussian increments and `E ≥ 0` the cut is almost surely finite. -/
theorem entranceCutIndex_ae_ne_top {μ : Measure Ω}
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E) :
    ∀ᵐ ω ∂μ, entranceCutIndex X E ω ≠ ⊤ := by
  have := hi.isProbabilityMeasure
  filter_upwards [firstRepairReject_ae_finite_gaussian hX hi hG (by linarith : 0 ≤ 2 * E)]
    with ω hω
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
  obtain ⟨j, -, hj⟩ := (firstRepairReject_le_iff X (2 * E) ω n).mp (le_of_eq hn.symm)
  have hle := entranceCut_le_of_repairRejected hE hj
  rw [Ne, entranceCutIndex_eq_top_iff]
  intro htop
  rw [htop] at hle
  exact ENat.natCast_ne_top _ (top_le_iff.mp hle)

/-! ## Measurability for the stopped σ-algebra -/

section Stopped

variable {f : Filtration ℕ mΩ} {κ : Ω → WithTop ℕ}

/-- A set whose slices `{κ = k}` are `f k`-measurable and whose slice `{κ = ⊤}` agrees with an
`f 0`-measurable set belongs to the stopped σ-algebra. -/
theorem measurableSet_stopped_of_slices (hκ : IsStoppingTime f κ) {S S₀ : Set Ω}
    (hS : ∀ k : ℕ, MeasurableSet[f k] (S ∩ {ω | κ ω = k}))
    (hS₀ : MeasurableSet[f 0] S₀) (htop : S ∩ {ω | κ ω = ⊤} = S₀ ∩ {ω | κ ω = ⊤}) :
    MeasurableSet[hκ.measurableSpace] S := by
  have hsplit : S = (⋃ k : ℕ, S ∩ {ω | κ ω = k}) ∪ (S ∩ {ω | κ ω = ⊤}) := by
    ext ω
    simp only [mem_union, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h
      induction hk : κ ω using WithTop.recTopCoe with
      | top => exact Or.inr ⟨h, rfl⟩
      | coe k => exact Or.inl ⟨k, h, rfl⟩
    · rintro (⟨k, h, -⟩ | ⟨h, -⟩) <;> exact h
  rw [hsplit]
  refine MeasurableSet.union (MeasurableSet.iUnion fun k =>
    (hκ.measurableSet_inter_eq_iff S k).mpr (hS k)) ?_
  rw [htop]
  have h0 : f 0 ≤ hκ.measurableSpace := by
    have hle : (fun _ : Ω => ((0 : ℕ) : WithTop ℕ)) ≤ κ := fun ω => by
      change ((0 : ℕ) : WithTop ℕ) ≤ κ ω
      exact WithTop.coe_le_iff.mpr fun _ _ => Nat.zero_le _ |>.trans_eq' rfl
    have := (isStoppingTime_const f 0).measurableSpace_mono hκ hle
    rwa [IsStoppingTime.measurableSpace_const] at this
  have htopset : MeasurableSet[hκ.measurableSpace] {ω | κ ω = ⊤} := by
    have : {ω | κ ω = ⊤} = (⋃ i : ℕ, {ω | κ ω ≤ i})ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, not_exists]
      constructor
      · intro h i hi
        rw [h] at hi
        exact WithTop.coe_ne_top (top_le_iff.mp hi)
      · intro h
        induction hk : κ ω using WithTop.recTopCoe with
        | top => rfl
        | coe k => exact absurd (le_of_eq hk) (h k)
    rw [this]
    exact (MeasurableSet.iUnion fun i => hκ.measurableSet_le' i).compl
  exact (h0 _ hS₀).inter htopset

/-- A function that agrees on each slice `{κ = k}` with an `f k`-measurable function and on
`{κ = ⊤}` with an `f 0`-measurable function is measurable for the stopped σ-algebra. -/
theorem measurable_stopped_of_slices {β : Type*} [MeasurableSpace β]
    (hκ : IsStoppingTime f κ) {g : Ω → β} (G : ℕ → Ω → β) (hG : ∀ k, Measurable[f k] (G k))
    (hg : ∀ ω (k : ℕ), κ ω = k → g ω = G k ω) (G₀ : Ω → β) (hG₀ : Measurable[f 0] G₀)
    (hg₀ : ∀ ω, κ ω = ⊤ → g ω = G₀ ω) :
    Measurable[hκ.measurableSpace] g := by
  intro B hB
  refine measurableSet_stopped_of_slices hκ (S₀ := G₀ ⁻¹' B) (fun k => ?_) (hG₀ hB) ?_
  · have heq : g ⁻¹' B ∩ {ω | κ ω = k} = G k ⁻¹' B ∩ {ω | κ ω = k} := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      exact ⟨fun ⟨h1, h2⟩ => ⟨hg ω k h2 ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hg ω k h2).symm ▸ h1, h2⟩⟩
    rw [heq]
    exact (hG k hB).inter (hκ.measurableSet_eq k)
  · ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨hg₀ ω h2 ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(hg₀ ω h2).symm ▸ h1, h2⟩⟩

end Stopped

variable (hX : ∀ k, Measurable (X k)) (E : ℝ)

/-- A quantity read at the cut is measurable for the stopped σ-algebra as soon as its value at
index `n` is measurable for the increments `X_0, …, X_{n-1}`. -/
theorem measurable_cutSigma_at_entranceCut {β : Type*} [MeasurableSpace β] (F : ℕ → Ω → β)
    (hF : ∀ n k, n ≤ k + 1 → Measurable[incrementFiltration X hX k] (F n)) :
    Measurable[(entranceCutIndex_isStoppingTime hX E).measurableSpace]
      fun ω => F (entranceCutNat (entrancePath X ω) E) ω :=
  measurable_stopped_of_slices (entranceCutIndex_isStoppingTime hX E) (fun k => F (k + 1))
    (fun k => hF (k + 1) k le_rfl) (fun ω k hk => by rw [entranceCutNat_of_index hk])
    (F 0) (hF 0 0 (Nat.zero_le _)) (fun ω hk => by rw [entranceCutNat_of_index_top hk])

theorem measurable_entranceSide_cut :
    Measurable[(entranceCutIndex_isStoppingTime hX E).measurableSpace]
      fun ω => entranceSide (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E) :=
  measurable_cutSigma_at_entranceCut hX E (fun n ω => entranceSide (entrancePath X ω) E n)
    fun _ _ h => measurable_entranceSide_at hX h E

theorem measurable_entranceFrozenSlope_cut :
    Measurable[(entranceCutIndex_isStoppingTime hX E).measurableSpace]
      fun ω => entranceFrozenSlope (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E) :=
  measurable_cutSigma_at_entranceCut hX E (fun n ω => entranceFrozenSlope (entrancePath X ω) E n)
    fun _ _ h => measurable_entranceFrozenSlope_at hX h E

theorem measurable_entranceWidth_cut :
    Measurable[(entranceCutIndex_isStoppingTime hX E).measurableSpace]
      fun ω => entranceWidth (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E) :=
  measurable_cutSigma_at_entranceCut hX E (fun n ω => entranceWidth (entrancePath X ω) E n)
    fun _ _ h => measurable_entranceWidth_at hX h E

theorem measurable_entranceGridArea_cut :
    Measurable[(entranceCutIndex_isStoppingTime hX E).measurableSpace]
      fun ω => entranceGridArea (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E) :=
  measurable_cutSigma_at_entranceCut hX E (fun n ω => entranceGridArea (entrancePath X ω) E n)
    fun _ _ h => measurable_entranceGridArea_at hX h E

/-- The truncation event is measurable for the stopped σ-algebra (G3). -/
theorem measurableSet_cutSigma_entranceGood (δ M : ℝ) :
    MeasurableSet[(entranceCutIndex_isStoppingTime hX E).measurableSpace]
      {ω | entranceGood (entrancePath X ω) E δ M} := by
  let T : ℕ → Set Ω := fun n => {ω | δ * E ^ 2 ≤ n ∧ (n : ℝ) ≤ M * E ^ 2 ∧
      |E * entranceFrozenSlope (entrancePath X ω) E n| ≤ M ∧
      entranceCutLevel E / 2 ≤ entranceWidth (entrancePath X ω) E n ∧
      entranceWidth (entrancePath X ω) E n ≤ entranceCutLevel E}
  have hT : ∀ k : ℕ, MeasurableSet[incrementFiltration X hX k] (T (k + 1)) := by
    intro k
    have hw := measurable_entranceWidth_at hX (n := k + 1) le_rfl E
    have hb := measurable_entranceFrozenSlope_at hX (n := k + 1) le_rfl E
    simp only [T, Set.ofPred_and]
    refine (@MeasurableSet.const Ω (incrementFiltration X hX k) _).inter
      ((@MeasurableSet.const Ω (incrementFiltration X hX k) _).inter
      ((measurableSet_le (continuous_abs.measurable.comp (hb.const_mul E)) measurable_const).inter
      ((measurableSet_le measurable_const hw).inter (measurableSet_le hw measurable_const))))
  refine measurableSet_stopped_of_slices (entranceCutIndex_isStoppingTime hX E) (S₀ := ∅)
    (fun k => ?_) (@MeasurableSet.empty Ω (incrementFiltration X hX 0)) ?_
  · have heq : {ω | entranceGood (entrancePath X ω) E δ M} ∩ {ω | entranceCutIndex X E ω = k} =
        T (k + 1) ∩ {ω | entranceCutIndex X E ω = k} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hg, hk⟩
        refine ⟨?_, hk⟩
        obtain ⟨-, h⟩ := (entranceGood_iff _ E δ M).mp hg
        rw [entranceCutNat_of_index hk] at h
        exact h
      · rintro ⟨h, hk⟩
        refine ⟨(entranceGood_iff _ E δ M).mpr ⟨?_, ?_⟩, hk⟩
        · rw [(entranceCutIndex_eq_coe_iff X E ω k).mp hk]
          exact ENat.natCast_ne_top _
        · rw [entranceCutNat_of_index hk]
          exact h
    rw [heq]
    exact (hT k).inter ((entranceCutIndex_isStoppingTime hX E).measurableSet_eq k)
  · ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, false_and, iff_false, not_and]
    intro hg htop
    exact ((entranceGood_iff _ E δ M).mp hg).1 ((entranceCutIndex_eq_top_iff X E ω).mp htop)

end

end SwingRepair
