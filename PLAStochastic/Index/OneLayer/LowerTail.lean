import PLAStochastic.Index.Model.GapLaw
import PLAStochastic.ForMathlib.Probability.Moments.PaleyZygmund

/-!
# Lower bounds for the one-layer segment length

For iid gaps `X` with law parameters `GapLaw P X μ σ κ`, write
`S k = partialSum (centred X μ) k` for the centred walk and `T = layerSegLen eps X`.

* `lt_layerSegLen_of_abs_partialSum_le`: if `|S k| ≤ μ eps` for all `k ≤ m`, the fixed line
  `a = 1/μ, b = 0` certifies the first `m + 1` keys, so `m < T`.
* `layerSegLen_lowerTail` (lem:Tlower): `P(T ≤ n) ≤ n σ² / (μ eps)²`, by Kolmogorov's maximal
  inequality; `layerSegLen_gt_lowerBound` is the complementary form.
* `GapLaw.block_tube_sign`: a block of `B` centred gaps ends with either sign while staying in
  the tube `|S t| < r`, each with probability at least `1/72`.
* `layerSegLen_smallBall`: `(1/72)^k ≤ P(k B < T)`, by steering the block endpoints back
  towards `0` and factorizing over the gap filtration.
-/

namespace PGM

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {μ σ κ : ℝ}

/-! ## The tube criterion for the centred walk -/

omit mΩ in
/-- If the centred walk stays within `μ eps` up to `m`, the first segment has more than `m`
keys: the fixed line `a = 1/μ, b = 0` fits the keys `0, …, m`. -/
theorem lt_layerSegLen_of_abs_partialSum_le {eps : ℝ} (hμ : 0 < μ) {ω : Ω} {m : ℕ}
    (h : ∀ k ≤ m, |partialSum (centred X μ) k ω| ≤ μ * eps) :
    (m : ℕ∞) < layerSegLen eps X ω := by
  rw [layerSegLen, gapSegLen, lt_segLen_iff]
  refine prefixAffineFeasible_of_line (1 / μ) 0 fun i hi => ?_
  rw [gapKeys_eq_centred]
  have hk := h i (by omega)
  have heq : (i : ℝ) - (1 / μ * (i * μ + partialSum (centred X μ) i ω) + 0) =
      -(partialSum (centred X μ) i ω / μ) := by
    field_simp
    ring
  rw [heq, abs_neg, abs_div, abs_of_pos hμ, div_le_iff₀ hμ]
  linarith [mul_comm μ eps]

/-! ## Second moment of the centred walk -/

private theorem integral_partialSum_centred_sq [IsProbabilityMeasure P]
    (hX : GapLaw P X μ σ κ) (n : ℕ) :
    ∫ ω, partialSum (centred X μ) n ω ^ 2 ∂P = n * σ ^ 2 := by
  rw [partialSum_eq_weightedSum_one, integral_weightedSum_sq hX.indepIncrements
    (PredictableWeight.one _) (fun t => (hX.memLp_centred t).mono_exponent (by norm_num))
    hX.integral_centred]
  simp [hX.integral_centred_sq]

/-! ## Lower tail (lem:Tlower) -/

/-- **Lower tail of the segment length.** `P(T ≤ n) ≤ n σ² / (μ eps)²`. -/
theorem layerSegLen_lowerTail [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ) {eps : ℝ}
    (heps : 0 < eps) (n : ℕ) :
    P.real {ω | layerSegLen eps X ω ≤ (n : ℕ∞)} ≤ n * σ ^ 2 / (μ * eps) ^ 2 := by
  have hl : 0 < μ * eps := mul_pos hX.mu_pos heps
  have hsub : {ω | layerSegLen eps X ω ≤ (n : ℕ∞)} ⊆
      {ω | ∃ k ≤ n, μ * eps ≤ |partialSum (centred X μ) k ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hc
    push Not at hc
    exact (not_lt.2 hω) (lt_layerSegLen_of_abs_partialSum_le hX.mu_pos fun k hk => (hc k hk).le)
  have hk := kolmogorov_maximal hX.indepIncrements
    (fun t => (hX.memLp_centred t).mono_exponent (by norm_num)) hX.integral_centred hl n
  rw [integral_partialSum_centred_sq hX] at hk
  rw [le_div_iff₀ (by positivity)]
  calc P.real {ω | layerSegLen eps X ω ≤ (n : ℕ∞)} * (μ * eps) ^ 2
      ≤ P.real {ω | ∃ k ≤ n, μ * eps ≤ |partialSum (centred X μ) k ω|} * (μ * eps) ^ 2 :=
        mul_le_mul_of_nonneg_right (measureReal_mono hsub) (sq_nonneg _)
    _ ≤ n * σ ^ 2 := by linarith

/-- Complementary form of `layerSegLen_lowerTail`: `P(n < T) ≥ 1 - n σ² / (μ eps)²`. -/
theorem layerSegLen_gt_lowerBound [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ) {eps : ℝ}
    (heps : 0 < eps) (n : ℕ) :
    1 - n * σ ^ 2 / (μ * eps) ^ 2 ≤ P.real {ω | (n : ℕ∞) < layerSegLen eps X ω} := by
  have hm : MeasurableSet {ω | (n : ℕ∞) < layerSegLen eps X ω} :=
    (gapFiltration X hX.iid.measurable).le n _
      (gapSegLen_lt_measurable hX.iid.measurable eps n)
  have hc : {ω | (n : ℕ∞) < layerSegLen eps X ω}ᶜ = {ω | layerSegLen eps X ω ≤ (n : ℕ∞)} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
  have h1 := measureReal_add_measureReal_compl (μ := P) hm
  rw [hc, probReal_univ] at h1
  have := layerSegLen_lowerTail hX heps n
  linarith

/-! ## One block: sign anti-concentration inside a tube -/

/-- **One block.** For `1 ≤ B`, `72 B σ² ≤ r²` and `κ² ≤ σ⁶ B`, the centred walk ends the block
`0, …, B` with a prescribed sign while staying in the tube `|S t| < r`, each sign with
probability at least `1/72`. -/
theorem GapLaw.block_tube_sign [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ) {r : ℝ}
    (hr : 0 < r) {B : ℕ} (hB : 1 ≤ B) (hvar : 72 * (B * σ ^ 2) ≤ r ^ 2)
    (hκ : κ ^ 2 ≤ σ ^ 6 * B) :
    1 / 72 ≤ P.real {ω | partialSum (centred X μ) B ω < 0 ∧
        ∀ t ≤ B, |partialSum (centred X μ) t ω| < r} ∧
      1 / 72 ≤ P.real {ω | 0 < partialSum (centred X μ) B ω ∧
        ∀ t ≤ B, |partialSum (centred X μ) t ω| < r} := by
  set S := partialSum (centred X μ) with hSdef
  have hI := hX.indepIncrements
  have hY2 : ∀ t, MemLp (centred X μ t) 2 P :=
    fun t => (hX.memLp_centred t).mono_exponent (by norm_num)
  have hσ := hX.sigma_pos
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hsqB := Real.sqrt_pos.2 hBpos
  have hsqB2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hBpos.le
  set s := σ * Real.sqrt B with hs
  have hs0 : 0 < s := mul_pos hσ hsqB
  -- moments of the block sum
  have hMm : Measurable (S B) :=
    (partialSum_measurable_past hI B).mono ((gapFiltration X hX.iid.measurable).le B) le_rfl
  have hM3 : MemLp (S B) 3 P := by
    rw [hSdef, partialSum_eq_weightedSum_one]
    exact memLp_weightedSum hI (PredictableWeight.one _) hX.memLp_centred B
  have h2 : s ^ 2 ≤ ∫ ω, S B ω ^ 2 ∂P := by
    rw [hSdef, integral_partialSum_centred_sq hX, hs, mul_pow, hsqB2, mul_comm]
  have hκle : κ ≤ σ ^ 3 * Real.sqrt B := by
    have hk0 := hX.kappa_nonneg
    have hsq : (σ ^ 3 * Real.sqrt B) ^ 2 = σ ^ 6 * B := by rw [mul_pow, hsqB2]; ring
    have hpos : 0 ≤ σ ^ 3 * Real.sqrt B := by positivity
    nlinarith
  have h3 : ∫ ω, |S B ω| ^ 3 ∂P ≤ 3 * s ^ 3 := by
    have hc := integral_abs_weightedSum_cube_le_of_unit hI (PredictableWeight.one _)
      (fun _ _ => abs_one) hX.memLp_centred hX.integral_centred hσ.le
      (fun t => (hX.integral_centred_sq t).le) hX.integral_centred_abs_cube B
    rw [hSdef, partialSum_eq_weightedSum_one]
    have hs3 : s ^ 3 = σ ^ 3 * B * Real.sqrt B := by
      rw [hs, mul_pow, show Real.sqrt B ^ 3 = Real.sqrt B ^ 2 * Real.sqrt B by ring, hsqB2]
      ring
    rw [hs3]
    have : (B : ℝ) * κ ≤ B * (σ ^ 3 * Real.sqrt B) := mul_le_mul_of_nonneg_left hκle hBpos.le
    nlinarith
  have h0 : ∫ ω, S B ω ∂P = 0 := by
    simp only [hSdef, partialSum]
    rw [integral_finsetSum _ fun t _ => (hX.memLp_centred t).integrable (by norm_num)]
    simp [hX.integral_centred]
  obtain ⟨hneg, hpos⟩ := anticoncentration_sign_of_moments hs0 hMm hM3 h2 h3 h0
  -- leaving the tube is unlikely
  have hbad : P.real {ω | ∃ t ≤ B, r ≤ |S t ω|} ≤ 1 / 72 := by
    have hk := kolmogorov_maximal hI hY2 hX.integral_centred hr B
    rw [integral_partialSum_centred_sq hX] at hk
    have hr2 : 0 < r ^ 2 := by positivity
    by_contra hc
    push Not at hc
    have : r ^ 2 * (1 / 72) < r ^ 2 * P.real {ω | ∃ t ≤ B, r ≤ |S t ω|} :=
      mul_lt_mul_of_pos_left hc hr2
    linarith
  have hsplit : ∀ (p : ℝ → Prop),
      {ω | p (S B ω)} ⊆ {ω | p (S B ω) ∧ ∀ t ≤ B, |S t ω| < r} ∪
        {ω | ∃ t ≤ B, r ≤ |S t ω|} := by
    intro p ω hω
    by_cases h : ∀ t ≤ B, |S t ω| < r
    · exact Or.inl ⟨hω, h⟩
    · push Not at h
      exact Or.inr h
  have hneg' := (measureReal_mono (μ := P) (hsplit (· < 0))).trans (measureReal_union_le _ _)
  have hpos' := (measureReal_mono (μ := P) (hsplit (0 < ·))).trans (measureReal_union_le _ _)
  constructor <;> linarith

/-! ## Small-ball lower bound

The block events are events of the future gaps `(X (m + t))_t`, read on sequence space through
`blockSum`.  The good event `goodEvent X μ r B k` steers the block endpoints
`S (j B)`, `j < k`: from a nonnegative endpoint the next block must end lower, from a negative one
higher, and every block stays in the tube of radius `r` around its starting point. -/

/-- Centred partial sums of a real sequence. -/
private def blockSum (μ : ℝ) (z : ℕ → ℝ) (t : ℕ) : ℝ := ∑ s ∈ range t, (z s - μ)

private def tubeNeg (μ r : ℝ) (B : ℕ) : Set (ℕ → ℝ) :=
  {z | blockSum μ z B < 0 ∧ ∀ t ≤ B, |blockSum μ z t| < r}

private def tubePos (μ r : ℝ) (B : ℕ) : Set (ℕ → ℝ) :=
  {z | 0 < blockSum μ z B ∧ ∀ t ≤ B, |blockSum μ z t| < r}

omit mΩ in
private theorem blockSum_shift (X : ℕ → Ω → ℝ) (μ : ℝ) (m t : ℕ) (ω : Ω) :
    blockSum μ (fun s => X (m + s) ω) t =
      partialSum (centred X μ) (m + t) ω - partialSum (centred X μ) m ω := by
  simp only [blockSum, partialSum, centred, Finset.sum_range_add]
  ring

section Tube

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}

private theorem measurableSet_tube {f : ℕ → Ω' → ℝ} {B : ℕ}
    (hf : ∀ t ≤ B, Measurable (f t)) (r : ℝ) :
    MeasurableSet {ω | f B ω < 0 ∧ ∀ t ≤ B, |f t ω| < r} ∧
      MeasurableSet {ω | 0 < f B ω ∧ ∀ t ≤ B, |f t ω| < r} := by
  have htube : MeasurableSet {ω | ∀ t ≤ B, |f t ω| < r} := by
    have : {ω | ∀ t ≤ B, |f t ω| < r} = ⋂ t ∈ Finset.range (B + 1), {ω | |f t ω| < r} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, Nat.lt_succ_iff]
    rw [this]
    exact MeasurableSet.biInter (Finset.range (B + 1)).countable_toSet fun t ht =>
      measurableSet_lt (continuous_abs.measurable.comp
        (hf t (Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)))) measurable_const
  exact ⟨(measurableSet_lt (hf B le_rfl) measurable_const).inter htube,
    (measurableSet_lt measurable_const (hf B le_rfl)).inter htube⟩

end Tube

/-- The steered good event after `k` blocks of length `B`. -/
private noncomputable def goodEvent (X : ℕ → Ω → ℝ) (μ r : ℝ) (B : ℕ) : ℕ → Set Ω
  | 0 => Set.univ
  | k + 1 =>
    (goodEvent X μ r B k ∩ {ω | 0 ≤ partialSum (centred X μ) (k * B) ω} ∩
        (fun ω t => X (k * B + t) ω) ⁻¹' tubeNeg μ r B) ∪
      (goodEvent X μ r B k ∩ {ω | partialSum (centred X μ) (k * B) ω < 0} ∩
        (fun ω t => X (k * B + t) ω) ⁻¹' tubePos μ r B)

private theorem goodEvent_measurableSet (hX : GapLaw P X μ σ κ) (r : ℝ) (B : ℕ) :
    ∀ k, MeasurableSet[gapFiltration X hX.iid.measurable (k * B)] (goodEvent X μ r B k)
  | 0 => MeasurableSet.univ
  | k + 1 => by
    set F := gapFiltration X hX.iid.measurable
    have ih := goodEvent_measurableSet hX r B k
    have hkB : (k + 1) * B = k * B + B := by ring
    rw [hkB]
    have hS : ∀ j ≤ k * B + B, Measurable[F (k * B + B)] (partialSum (centred X μ) j) :=
      fun j hj => (partialSum_measurable_past hX.indepIncrements j).mono (F.mono hj) le_rfl
    have hE : MeasurableSet[F (k * B + B)] (goodEvent X μ r B k) :=
      F.mono (Nat.le_add_right _ _) _ ih
    have hf : ∀ t ≤ B, Measurable[F (k * B + B)]
        (fun ω => blockSum μ (fun s => X (k * B + s) ω) t) := by
      intro t ht
      simp only [blockSum_shift]
      exact (hS _ (by omega)).sub (hS _ (Nat.le_add_right _ _))
    obtain ⟨hN, hP⟩ := measurableSet_tube (mΩ' := F (k * B + B)) hf r
    simp only [goodEvent]
    exact ((hE.inter (measurableSet_le measurable_const (hS _ (Nat.le_add_right _ _)))).inter
      hN).union ((hE.inter (measurableSet_lt (hS _ (Nat.le_add_right _ _))
        measurable_const)).inter hP)

omit mΩ in
/-- On the good event the block endpoints stay within `2 r` and the walk within `3 r`. -/
private theorem goodEvent_bound {r : ℝ} (hr : 0 ≤ r) {B : ℕ} :
    ∀ k, ∀ ω ∈ goodEvent X μ r B k, |partialSum (centred X μ) (k * B) ω| ≤ 2 * r ∧
      ∀ t ≤ k * B, |partialSum (centred X μ) t ω| ≤ 3 * r
  | 0 => by
    intro ω _
    refine ⟨by simp only [zero_mul, partialSum, range_zero, sum_empty, abs_zero]; linarith,
      fun t ht => ?_⟩
    obtain rfl : t = 0 := by omega
    simp only [partialSum, range_zero, sum_empty, abs_zero]
    linarith
  | k + 1 => by
    intro ω hω
    have ih := goodEvent_bound (B := B) hr k
    have hkB : (k + 1) * B = k * B + B := by ring
    rw [hkB]
    set S := partialSum (centred X μ) with hSdef
    -- the block condition, in terms of the walk
    have hblock : (S (k * B + B) ω - S (k * B) ω < 0 ∨ 0 < S (k * B + B) ω - S (k * B) ω) ∧
        (0 ≤ S (k * B) ω → S (k * B + B) ω - S (k * B) ω < 0) ∧
        (S (k * B) ω < 0 → 0 < S (k * B + B) ω - S (k * B) ω) ∧
        (∀ t ≤ B, |S (k * B + t) ω - S (k * B) ω| < r) ∧ ω ∈ goodEvent X μ r B k := by
      simp only [goodEvent, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage, tubeNeg,
        tubePos, Set.mem_ofPred_eq, blockSum_shift] at hω
      rcases hω with ⟨⟨hE, h0⟩, hN, hT⟩ | ⟨⟨hE, h0⟩, hP, hT⟩
      · exact ⟨Or.inl hN, fun _ => hN, fun h => absurd h0 (not_le.2 h), hT, hE⟩
      · exact ⟨Or.inr hP, fun h => absurd h (not_le.2 h0), fun _ => hP, hT, hE⟩
    obtain ⟨-, hdn, hup, hT, hE⟩ := hblock
    obtain ⟨ha, hwalk⟩ := ih ω hE
    have ha' := abs_le.1 ha
    have hend := abs_lt.1 (hT B le_rfl)
    refine ⟨?_, fun t ht => ?_⟩
    · rcases le_or_gt 0 (S (k * B) ω) with h0 | h0
      · have := hdn h0
        exact abs_le.2 ⟨by linarith, by linarith⟩
      · have := hup h0
        exact abs_le.2 ⟨by linarith, by linarith⟩
    · by_cases htk : t ≤ k * B
      · exact hwalk t htk
      · obtain ⟨t', rfl⟩ : ∃ t', t = k * B + t' := ⟨t - k * B, by omega⟩
        have h1 := abs_lt.1 (hT t' (by omega))
        exact abs_le.2 ⟨by linarith, by linarith⟩

/-- One step of the recursion: `P(E_{k+1}) ≥ P(E_k) / 72`. -/
private theorem goodEvent_step [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ) {r : ℝ}
    (hr : 0 < r) {B : ℕ} (hB : 1 ≤ B) (hvar : 72 * (B * σ ^ 2) ≤ r ^ 2)
    (hκ : κ ^ 2 ≤ σ ^ 6 * B) (k : ℕ) :
    1 / 72 * P.real (goodEvent X μ r B k) ≤ P.real (goodEvent X μ r B (k + 1)) := by
  set F := gapFiltration X hX.iid.measurable
  set E := goodEvent X μ r B k with hEdef
  set x := partialSum (centred X μ) (k * B) with hxdef
  set fut : Ω → ℕ → ℝ := fun ω t => X (k * B + t) ω with hfut
  have hE : MeasurableSet[F (k * B)] E := goodEvent_measurableSet hX r B k
  have hx : Measurable[F (k * B)] x := partialSum_measurable_past hX.indepIncrements _
  have hx0 : MeasurableSet[F (k * B)] {ω | 0 ≤ x ω} := measurableSet_le measurable_const hx
  have hA1 : MeasurableSet[F (k * B)] (E ∩ {ω | 0 ≤ x ω}) := hE.inter hx0
  have hA2 : MeasurableSet[F (k * B)] (E ∩ {ω | x ω < 0}) :=
    hE.inter (measurableSet_lt hx measurable_const)
  have hbs : ∀ t ≤ B, Measurable (fun z : ℕ → ℝ => blockSum μ z t) :=
    fun t _ => Finset.measurable_sum _ fun s _ => (measurable_pi_apply s).sub measurable_const
  obtain ⟨hN, hP⟩ : MeasurableSet (tubeNeg μ r B) ∧ MeasurableSet (tubePos μ r B) :=
    measurableSet_tube hbs r
  have hfutm : Measurable fut := measurable_pi_lambda _ fun t => hX.iid.measurable (k * B + t)
  have hblock := (hX.shift (k * B)).block_tube_sign hr hB hvar hκ
  have hpN : 1 / 72 ≤ P.real (fut ⁻¹' tubeNeg μ r B) := hblock.1
  have hpP : 1 / 72 ≤ P.real (fut ⁻¹' tubePos μ r B) := hblock.2
  have hfac : ∀ {A : Set (ℕ → ℝ)}, MeasurableSet A → ∀ {C : Set Ω},
      MeasurableSet[F (k * B)] C → P.real (C ∩ fut ⁻¹' A) = P.real (fut ⁻¹' A) * P.real C := by
    intro A hA C hC
    rw [Set.inter_comm]
    simp only [measureReal_def]
    rw [measure_future_inter_gapFiltration hX.iid (k * B) hA hC, ENNReal.toReal_mul]
  have hstep : goodEvent X μ r B (k + 1) =
      (E ∩ {ω | 0 ≤ x ω} ∩ fut ⁻¹' tubeNeg μ r B) ∪
        (E ∩ {ω | x ω < 0} ∩ fut ⁻¹' tubePos μ r B) := rfl
  have hdisj : Disjoint (E ∩ {ω | 0 ≤ x ω} ∩ fut ⁻¹' tubeNeg μ r B)
      (E ∩ {ω | x ω < 0} ∩ fut ⁻¹' tubePos μ r B) := by
    rw [Set.disjoint_left]
    rintro ω ⟨⟨_, h1⟩, _⟩ ⟨⟨_, h2⟩, _⟩
    simp only [Set.mem_ofPred_eq] at h1 h2
    linarith
  have hm2 : MeasurableSet (E ∩ {ω | x ω < 0} ∩ fut ⁻¹' tubePos μ r B) :=
    (F.le _ _ hA2).inter (hfutm hP)
  rw [hstep, measureReal_union hdisj hm2, hfac hN hA1, hfac hP hA2]
  have hdiff : E ∩ {ω | x ω < 0} = E \ {ω | 0 ≤ x ω} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq, not_le]
  have hsum := measureReal_inter_add_sdiff (μ := P) (s := E) (F.le _ _ hx0)
  rw [← hdiff] at hsum
  have h1 : 0 ≤ P.real (E ∩ {ω | 0 ≤ x ω}) := measureReal_nonneg
  have h2 : 0 ≤ P.real (E ∩ {ω | x ω < 0}) := measureReal_nonneg
  nlinarith

/-- **Small-ball lower bound.** If `1 ≤ B`, `1152 B σ² ≤ μ² eps²` and `κ² ≤ σ⁶ B`, then the first
segment has more than `k B` keys with probability at least `(1/72)^k`. -/
theorem layerSegLen_smallBall [IsProbabilityMeasure P] (hX : GapLaw P X μ σ κ) {eps : ℝ}
    (heps : 0 < eps) {B : ℕ} (hB : 1 ≤ B) (hvar : 1152 * B * σ ^ 2 ≤ μ ^ 2 * eps ^ 2)
    (hκ : κ ^ 2 ≤ σ ^ 6 * B) :
    ∀ k : ℕ, (1 / 72 : ℝ) ^ k ≤ P.real {ω | ((k * B : ℕ) : ℕ∞) < layerSegLen eps X ω} := by
  set r := μ * eps / 4 with hrdef
  have hμ := hX.mu_pos
  have hr : 0 < r := by positivity
  have hvar' : 72 * (B * σ ^ 2) ≤ r ^ 2 := by
    have : r ^ 2 = μ ^ 2 * eps ^ 2 / 16 := by rw [hrdef]; ring
    rw [this]
    linarith
  have hgood : ∀ k, (1 / 72 : ℝ) ^ k ≤ P.real (goodEvent X μ r B k) := by
    intro k
    induction k with
    | zero => simp [goodEvent]
    | succ k ih =>
      have := goodEvent_step hX hr hB hvar' hκ k
      rw [pow_succ]
      nlinarith
  intro k
  refine (hgood k).trans (measureReal_mono fun ω hω => ?_)
  obtain ⟨-, h⟩ := goodEvent_bound hr.le k ω hω
  exact lt_layerSegLen_of_abs_partialSum_le hμ fun t ht =>
    (h t ht).trans (by rw [hrdef]; linarith)

end PGM
