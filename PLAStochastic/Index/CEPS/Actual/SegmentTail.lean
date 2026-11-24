import PLAStochastic.Index.CEPS.Actual.Hadamard

/-!
# P-CEPS WP8: a geometric tail of the first segment for every `ε`

Theorem (E) needs `T < ∞` a.s. and `E T < ∞`. The class bounds of `momClass_setup` give these only for
`ε ≥ ε₀`. Here they are proved for every `ε` and every gap law charging `(0, a')` and `(b', ∞)` with
`0 < a' < b'` (`gapSegLen_geometric_tail`), in particular for every regular law (`RegLaw.segLen_finite`).

A block of `k` gaps in `(0, a')` followed by `k` gaps in `(b', ∞)` is infeasible once
`k (b' - a') > 2ε (a' + b')` (`not_feasible_of_badBlock`): the two half-blocks force slopes
`A > (k - 2ε)/(k a')` and `A < (k + 2ε)/(k b')`. Disjoint blocks are independent, so the survival
`P(T > n)` is at most `(1 - p)^{⌊n / 2k⌋}`, `p = P(block)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

/-! ## An infeasible block -/

/-- `k` gaps in `(0, a')` followed by `k` gaps in `(b', ∞)`. -/
def cepsBadBlock (a' b' : ℝ) (k : ℕ) (g : ℕ → ℝ) : Prop :=
  (∀ i < k, g i ∈ Ioo 0 a') ∧ ∀ i < k, g (k + i) ∈ Ioi b'

theorem not_feasible_of_badBlock {eps a' b' : ℝ} (ha' : 0 < a') (hab : a' < b') {k : ℕ}
    (hk : 2 * eps * (a' + b') < k * (b' - a')) {g : ℕ → ℝ} {s : ℕ}
    (hbad : cepsBadBlock a' b' k (WienerHopf.shift s g)) :
    ¬ prefixAffineFeasible eps (gapKeys g) (s + 2 * k + 1) := by
  rintro ⟨A, B, h⟩
  have heps : 0 ≤ eps := (abs_nonneg _).trans (h 0 (by omega))
  have hk0 : (0 : ℝ) < k := by
    have : 0 ≤ 2 * eps * (a' + b') := mul_nonneg (mul_nonneg zero_le_two heps) (by linarith)
    by_contra hk0
    push Not at hk0
    nlinarith
  set D₁ := gapKeys g (s + k) - gapKeys g s
  set D₂ := gapKeys g (s + 2 * k) - gapKeys g (s + k)
  have hD₁ : D₁ = ∑ i ∈ Finset.range k, g (s + i) := by
    simp only [D₁]
    rw [← gapKeys_shift]; rfl
  have hD₂ : D₂ = ∑ i ∈ Finset.range k, g (s + (k + i)) := by
    simp only [D₂]
    rw [show s + 2 * k = (s + k) + k by ring, ← gapKeys_shift]
    unfold gapKeys
    exact Finset.sum_congr rfl fun i _ => by
      show g (s + k + i) = g (s + (k + i))
      rw [add_assoc]
  have hD₁pos : 0 < D₁ := by
    rw [hD₁]
    exact Finset.sum_pos (fun i hi => (hbad.1 i (Finset.mem_range.1 hi)).1)
      (Finset.nonempty_range_iff.2 (by exact_mod_cast hk0.ne'))
  have hD₁lt : D₁ < k * a' := by
    rw [hD₁]
    calc ∑ i ∈ Finset.range k, g (s + i) < ∑ i ∈ Finset.range k, a' :=
          Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by exact_mod_cast hk0.ne'))
            fun i hi => (hbad.1 i (Finset.mem_range.1 hi)).2
      _ = k * a' := by simp
  have hD₂gt : k * b' < D₂ := by
    rw [hD₂]
    calc (k : ℝ) * b' = ∑ i ∈ Finset.range k, b' := by simp
      _ < ∑ i ∈ Finset.range k, g (s + (k + i)) :=
          Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by exact_mod_cast hk0.ne'))
            fun i hi => hbad.2 i (Finset.mem_range.1 hi)
  have h0 := abs_le.1 (h s (by omega))
  have h1 := abs_le.1 (h (s + k) (by omega))
  have h2 := abs_le.1 (h (s + 2 * k) (by omega))
  push_cast at h0 h1 h2
  -- the slope from the two half-blocks
  have hAD₁ : (k : ℝ) - 2 * eps ≤ A * D₁ := by simp only [D₁]; nlinarith
  have hAD₂ : A * D₂ ≤ (k : ℝ) + 2 * eps := by simp only [D₂]; nlinarith
  have hk2 : 2 * eps < k := by nlinarith
  have hA : 0 < A := by
    by_contra hA
    push Not at hA
    nlinarith
  have h3 : (k : ℝ) - 2 * eps < A * (k * a') := lt_of_le_of_lt hAD₁ (mul_lt_mul_of_pos_left hD₁lt hA)
  have h4 : A * (k * b') < (k : ℝ) + 2 * eps := lt_of_lt_of_le (mul_lt_mul_of_pos_left hD₂gt hA) hAD₂
  nlinarith [mul_lt_mul_of_pos_right h3 (lt_trans ha' hab), mul_lt_mul_of_pos_right h4 ha']

/-! ## Independent blocks -/

theorem measurableSet_cepsBadBlock (a' b' : ℝ) (k : ℕ) :
    MeasurableSet {g : ℕ → ℝ | cepsBadBlock a' b' k g} := by
  have e : {g : ℕ → ℝ | cepsBadBlock a' b' k g} =
      (⋂ i ∈ Finset.range k, {g : ℕ → ℝ | g i ∈ Ioo 0 a'}) ∩
        ⋂ i ∈ Finset.range k, {g : ℕ → ℝ | g (k + i) ∈ Ioi b'} := by
    ext g; simp [cepsBadBlock]
  rw [e]
  exact (Finset.measurableSet_biInter _ fun i _ => measurableSet_Ioo.preimage (measurable_pi_apply i)).inter
    (Finset.measurableSet_biInter _ fun i _ => measurableSet_Ioi.preimage (measurable_pi_apply (k + i)))

/-- No bad block among the first `J` disjoint blocks of length `2k`. -/
def cepsNoBad (a' b' : ℝ) (k J : ℕ) (g : ℕ → ℝ) : Prop :=
  ∀ m < J, ¬ cepsBadBlock a' b' k (WienerHopf.shift (2 * k * m) g)

theorem measurableSet_cepsNoBad (a' b' : ℝ) (k J : ℕ) :
    MeasurableSet {g : ℕ → ℝ | cepsNoBad a' b' k J g} := by
  have e : {g : ℕ → ℝ | cepsNoBad a' b' k J g} = ⋂ m ∈ Finset.range J,
      (WienerHopf.shift (2 * k * m)) ⁻¹' {g : ℕ → ℝ | cepsBadBlock a' b' k g}ᶜ := by
    ext g; simp [cepsNoBad]
  rw [e]
  exact Finset.measurableSet_biInter _ fun m _ =>
    (measurableSet_cepsBadBlock a' b' k).compl.preimage (WienerHopf.measurable_shift _)

theorem iidLaw_box (ν : ProbabilityMeasure ℝ) {E : Set ℝ} (hE : MeasurableSet E) (k : ℕ) :
    (iidLaw ν).real {g : ℕ → ℝ | ∀ i < k, g i ∈ E} = ((ν : Measure ℝ).real E) ^ k := by
  have e : {g : ℕ → ℝ | ∀ i < k, g i ∈ E} = Set.pi (Finset.range k : Set ℕ) (fun _ => E) := by
    ext g; simp
  rw [e, measureReal_def, iidLaw, Measure.infinitePi_pi (fun _ : ℕ => (ν : Measure ℝ))
    (fun _ _ => hE), Finset.prod_const, Finset.card_range, ENNReal.toReal_pow]
  rfl

theorem integral_indicator_one_real {α : Type*} [MeasurableSpace α] (μ : Measure α) {E : Set α}
    (hE : MeasurableSet E) : ∫ g, E.indicator (fun _ => (1 : ℝ)) g ∂μ = μ.real E := by
  rw [integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one]

theorem measurableSet_box {E : Set ℝ} (hE : MeasurableSet E) (k : ℕ) :
    MeasurableSet {g : ℕ → ℝ | ∀ i < k, g i ∈ E} := by
  have e : {g : ℕ → ℝ | ∀ i < k, g i ∈ E} = ⋂ i ∈ Finset.range k, {g : ℕ → ℝ | g i ∈ E} := by
    ext g; simp
  rw [e]
  exact Finset.measurableSet_biInter _ fun i _ => hE.preimage (measurable_pi_apply i)

theorem dependsOnPrefix_box (E : Set ℝ) (k : ℕ) :
    WienerHopf.DependsOnPrefix k ({g : ℕ → ℝ | ∀ i < k, g i ∈ E}.indicator fun _ => (1 : ℝ)) := by
  intro ω ω' h
  have hiff : (∀ i < k, ω i ∈ E) ↔ (∀ i < k, ω' i ∈ E) :=
    ⟨fun h' i hi => h i hi ▸ h' i hi, fun h' i hi => (h i hi).symm ▸ h' i hi⟩
  by_cases hω : ∀ i < k, ω i ∈ E
  · rw [indicator_of_mem (show ω ∈ {g : ℕ → ℝ | ∀ i < k, g i ∈ E} from hω),
      indicator_of_mem (show ω' ∈ {g : ℕ → ℝ | ∀ i < k, g i ∈ E} from hiff.1 hω)]
  · rw [indicator_of_notMem (show ω ∉ {g : ℕ → ℝ | ∀ i < k, g i ∈ E} from hω),
      indicator_of_notMem (show ω' ∉ {g : ℕ → ℝ | ∀ i < k, g i ∈ E} from fun h' => hω (hiff.2 h'))]

theorem iidLaw_badBlock (ν : ProbabilityMeasure ℝ) (a' b' : ℝ) (k : ℕ) :
    (iidLaw ν).real {g : ℕ → ℝ | cepsBadBlock a' b' k g} =
      ((ν : Measure ℝ).real (Ioo 0 a')) ^ k * ((ν : Measure ℝ).real (Ioi b')) ^ k := by
  have hFs := measurableSet_box (measurableSet_Ioo (a := (0 : ℝ)) (b := a')) k
  have hGs := measurableSet_box (measurableSet_Ioi (a := b')) k
  have hsplit : ∀ g : ℕ → ℝ, {g : ℕ → ℝ | cepsBadBlock a' b' k g}.indicator (fun _ => (1 : ℝ)) g =
      {g : ℕ → ℝ | ∀ i < k, g i ∈ Ioo 0 a'}.indicator (fun _ => (1 : ℝ)) g *
        {g : ℕ → ℝ | ∀ i < k, g i ∈ Ioi b'}.indicator (fun _ => (1 : ℝ)) (WienerHopf.shift k g) := by
    intro g
    by_cases h1 : ∀ i < k, g i ∈ Ioo 0 a'
    · by_cases h2 : ∀ i < k, WienerHopf.shift k g i ∈ Ioi b'
      · rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | cepsBadBlock a' b' k g} from ⟨h1, h2⟩),
          indicator_of_mem (show g ∈ {g : ℕ → ℝ | ∀ i < k, g i ∈ Ioo 0 a'} from h1),
          indicator_of_mem (show WienerHopf.shift k g ∈ {g : ℕ → ℝ | ∀ i < k, g i ∈ Ioi b'} from h2),
          mul_one]
      · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | cepsBadBlock a' b' k g} from
            fun h => h2 h.2),
          indicator_of_notMem (show WienerHopf.shift k g ∉ {g : ℕ → ℝ | ∀ i < k, g i ∈ Ioi b'} from h2),
          mul_zero]
    · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | cepsBadBlock a' b' k g} from fun h => h1 h.1),
        indicator_of_notMem (show g ∉ {g : ℕ → ℝ | ∀ i < k, g i ∈ Ioo 0 a'} from h1), zero_mul]
  have h := WienerHopf.integral_mul_shift (𝕜 := ℝ) (ρ := (ν : Measure ℝ)) (k := k)
    (F := {g : ℕ → ℝ | ∀ i < k, g i ∈ Ioo 0 a'}.indicator fun _ => (1 : ℝ))
    (G := {g : ℕ → ℝ | ∀ i < k, g i ∈ Ioi b'}.indicator fun _ => (1 : ℝ))
    (measurable_const.indicator hFs) (dependsOnPrefix_box (Ioo 0 a') k)
    (measurable_const.indicator hGs)
  rw [← integral_indicator_one_real _ (measurableSet_cepsBadBlock a' b' k)]
  simp_rw [hsplit]
  rw [show iidLaw ν = WienerHopf.pathLaw (ν : Measure ℝ) from rfl, h,
    ← show iidLaw ν = WienerHopf.pathLaw (ν : Measure ℝ) from rfl,
    integral_indicator_one_real _ hFs, integral_indicator_one_real _ hGs,
    iidLaw_box ν measurableSet_Ioo, iidLaw_box ν measurableSet_Ioi]

theorem cepsNoBad_succ (a' b' : ℝ) (k J : ℕ) (g : ℕ → ℝ) :
    {g : ℕ → ℝ | cepsNoBad a' b' k (J + 1) g}.indicator (fun _ => (1 : ℝ)) g =
      {g : ℕ → ℝ | cepsNoBad a' b' k J g}.indicator (fun _ => (1 : ℝ)) g *
        {g : ℕ → ℝ | cepsBadBlock a' b' k g}ᶜ.indicator (fun _ => (1 : ℝ))
          (WienerHopf.shift (2 * k * J) g) := by
  have hiff : cepsNoBad a' b' k (J + 1) g ↔ cepsNoBad a' b' k J g ∧
      ¬ cepsBadBlock a' b' k (WienerHopf.shift (2 * k * J) g) := by
    constructor
    · intro h; exact ⟨fun m hm => h m (by omega), h J (by omega)⟩
    · rintro ⟨h1, h2⟩ m hm
      rcases Nat.lt_or_ge m J with hmJ | hmJ
      · exact h1 m hmJ
      · have : m = J := by omega
        subst this; exact h2
  by_cases h1 : cepsNoBad a' b' k J g
  · by_cases h2 : cepsBadBlock a' b' k (WienerHopf.shift (2 * k * J) g)
    · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | cepsNoBad a' b' k (J + 1) g} from
          fun h => (hiff.1 h).2 h2),
        indicator_of_notMem (show WienerHopf.shift (2 * k * J) g ∉
          {g : ℕ → ℝ | cepsBadBlock a' b' k g}ᶜ from fun h => h h2), mul_zero]
    · rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | cepsNoBad a' b' k (J + 1) g} from
          hiff.2 ⟨h1, h2⟩), indicator_of_mem (show g ∈ {g : ℕ → ℝ | cepsNoBad a' b' k J g} from h1),
        indicator_of_mem (show WienerHopf.shift (2 * k * J) g ∈
          {g : ℕ → ℝ | cepsBadBlock a' b' k g}ᶜ from h2), mul_one]
  · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | cepsNoBad a' b' k (J + 1) g} from
        fun h => h1 (hiff.1 h).1),
      indicator_of_notMem (show g ∉ {g : ℕ → ℝ | cepsNoBad a' b' k J g} from h1), zero_mul]

theorem dependsOnPrefix_cepsNoBad (a' b' : ℝ) (k J : ℕ) :
    WienerHopf.DependsOnPrefix (2 * k * J)
      ({g : ℕ → ℝ | cepsNoBad a' b' k J g}.indicator fun _ => (1 : ℝ)) := by
  intro ω ω' h
  have hiff : cepsNoBad a' b' k J ω ↔ cepsNoBad a' b' k J ω' := by
    have hblock : ∀ m < J, cepsBadBlock a' b' k (WienerHopf.shift (2 * k * m) ω) ↔
        cepsBadBlock a' b' k (WienerHopf.shift (2 * k * m) ω') := by
      intro m hm
      have hmJ : 2 * k * (m + 1) ≤ 2 * k * J := Nat.mul_le_mul_left _ hm
      unfold cepsBadBlock WienerHopf.shift
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => ?_, fun i hi => ?_⟩
        · rw [← h _ (by nlinarith)]; exact h1 i hi
        · rw [← h _ (by nlinarith)]; exact h2 i hi
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => ?_, fun i hi => ?_⟩
        · rw [h _ (by nlinarith)]; exact h1 i hi
        · rw [h _ (by nlinarith)]; exact h2 i hi
    exact ⟨fun h' m hm hb => h' m hm ((hblock m hm).2 hb),
      fun h' m hm hb => h' m hm ((hblock m hm).1 hb)⟩
  by_cases hω : cepsNoBad a' b' k J ω
  · rw [indicator_of_mem (show ω ∈ {g : ℕ → ℝ | cepsNoBad a' b' k J g} from hω),
      indicator_of_mem (show ω' ∈ {g : ℕ → ℝ | cepsNoBad a' b' k J g} from hiff.1 hω)]
  · rw [indicator_of_notMem (show ω ∉ {g : ℕ → ℝ | cepsNoBad a' b' k J g} from hω),
      indicator_of_notMem (show ω' ∉ {g : ℕ → ℝ | cepsNoBad a' b' k J g} from fun h' => hω (hiff.2 h'))]

/-- `P(no bad block among J blocks) = (1 - p)^J`. -/
theorem iidLaw_cepsNoBad (ν : ProbabilityMeasure ℝ) (a' b' : ℝ) (k J : ℕ) :
    (iidLaw ν).real {g : ℕ → ℝ | cepsNoBad a' b' k J g} =
      (1 - ((ν : Measure ℝ).real (Ioo 0 a')) ^ k * ((ν : Measure ℝ).real (Ioi b')) ^ k) ^ J := by
  induction J with
  | zero =>
    have : {g : ℕ → ℝ | cepsNoBad a' b' k 0 g} = univ := by
      ext g; simp [cepsNoBad]
    rw [this, probReal_univ, pow_zero]
  | succ J ih =>
    have hB := measurableSet_cepsBadBlock a' b' k
    rw [← integral_indicator_one_real _ (measurableSet_cepsNoBad a' b' k (J + 1))]
    simp_rw [cepsNoBad_succ]
    have h := WienerHopf.integral_mul_shift (𝕜 := ℝ) (ρ := (ν : Measure ℝ)) (k := 2 * k * J)
      (F := {g : ℕ → ℝ | cepsNoBad a' b' k J g}.indicator fun _ => (1 : ℝ))
      (G := {g : ℕ → ℝ | cepsBadBlock a' b' k g}ᶜ.indicator fun _ => (1 : ℝ))
      (measurable_const.indicator (measurableSet_cepsNoBad a' b' k J))
      (dependsOnPrefix_cepsNoBad a' b' k J) (measurable_const.indicator hB.compl)
    rw [show iidLaw ν = WienerHopf.pathLaw (ν : Measure ℝ) from rfl, h,
      ← show iidLaw ν = WienerHopf.pathLaw (ν : Measure ℝ) from rfl,
      integral_indicator_one_real _ (measurableSet_cepsNoBad a' b' k J),
      integral_indicator_one_real _ hB.compl, ih, probReal_compl_eq_one_sub hB,
      iidLaw_badBlock, pow_succ]

/-- The survival `P(T > n)` decays like `(1 - p)^{⌊n/2k⌋}`. -/
theorem iidLaw_segLen_gt_le (ν : ProbabilityMeasure ℝ) {eps a' b' : ℝ} (ha' : 0 < a')
    (hab : a' < b') {k : ℕ} (hk : 2 * eps * (a' + b') < k * (b' - a')) (n : ℕ) :
    (iidLaw ν).real {g : ℕ → ℝ | (n : ℕ∞) < gapSegLen eps g} ≤
      (1 - ((ν : Measure ℝ).real (Ioo 0 a')) ^ k * ((ν : Measure ℝ).real (Ioi b')) ^ k) ^
        (n / (2 * k)) := by
  rw [← iidLaw_cepsNoBad ν a' b' k]
  refine measureReal_mono (fun g hg => ?_)
  simp only [mem_ofPred_eq] at hg ⊢
  rw [gapSegLen, lt_segLen_iff] at hg
  intro m hm hbad
  refine not_feasible_of_badBlock ha' hab hk hbad (prefixAffineFeasible_mono hg ?_)
  have h1 : 2 * k * (m + 1) ≤ 2 * k * (n / (2 * k)) := Nat.mul_le_mul_left _ hm
  have h2 : 2 * k * (n / (2 * k)) ≤ n := Nat.mul_div_le n (2 * k)
  nlinarith

/-! ## Finiteness and integrability of the first segment -/

theorem exists_geometric_of_pow_div {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {N : ℕ} (hN0 : N ≠ 0) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧ ∀ n : ℕ, ρ ^ (n / N) ≤ C * r ^ n := by
  set ρ' := max ρ (1 / 2) with hρ'
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hρ'1 : ρ' < 1 := max_lt hρ1 (by norm_num)
  set r := ρ' ^ ((N : ℝ)⁻¹) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hρ'0.le _
  have hr1 : r < 1 := Real.rpow_lt_one hρ'0.le hρ'1 (by positivity)
  have hrN : r ^ N = ρ' := Real.rpow_inv_natCast_pow hρ'0.le hN0
  refine ⟨1 / ρ', r, by positivity, hr0, hr1, fun n => ?_⟩
  have h1 : ρ ^ (n / N) ≤ ρ' ^ (n / N) := pow_le_pow_left₀ hρ0 (le_max_left _ _) _
  have h2 : ρ' ^ (n / N) * ρ' ≤ r ^ n := by
    rw [← hrN, ← pow_mul, ← pow_add]
    refine pow_le_pow_of_le_one hr0 hr1.le ?_
    have h1 := Nat.div_add_mod n N
    have h2 := Nat.mod_lt n (Nat.pos_of_ne_zero hN0)
    omega
  calc ρ ^ (n / N) ≤ ρ' ^ (n / N) := h1
    _ ≤ 1 / ρ' * r ^ n := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hρ'0]
        exact h2

/-- **The first segment is a.s. finite and integrable** for every `ε` and every gap law charging
`(0, a')` and `(b', ∞)`, `0 < a' < b'`. -/
theorem gapSegLen_finite_integrable (ν : ProbabilityMeasure ℝ) {a' b' : ℝ} (ha' : 0 < a')
    (hab : a' < b') (h1 : 0 < (ν : Measure ℝ).real (Ioo 0 a'))
    (h2 : 0 < (ν : Measure ℝ).real (Ioi b')) (eps : ℝ) :
    (∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤) ∧
      Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν) := by
  set k : ℕ := ⌈2 * eps * (a' + b') / (b' - a')⌉₊ + 1 with hkdef
  have hba : 0 < b' - a' := by linarith
  have hk : 2 * eps * (a' + b') < k * (b' - a') := by
    have h3 : 2 * eps * (a' + b') / (b' - a') ≤ ⌈2 * eps * (a' + b') / (b' - a')⌉₊ := Nat.le_ceil _
    have h4 : (⌈2 * eps * (a' + b') / (b' - a')⌉₊ : ℝ) < k := by rw [hkdef]; push_cast; linarith
    have := (div_lt_iff₀ hba).1 (h3.trans_lt h4)
    linarith
  set p := ((ν : Measure ℝ).real (Ioo 0 a')) ^ k * ((ν : Measure ℝ).real (Ioi b')) ^ k with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p ≤ 1 := by
    have := measureReal_le_one (μ := (ν : Measure ℝ)) (s := Ioo 0 a')
    have := measureReal_le_one (μ := (ν : Measure ℝ)) (s := Ioi b')
    rw [hp]
    calc _ ≤ (1 : ℝ) ^ k * 1 ^ k := mul_le_mul (pow_le_pow_left₀ h1.le (by assumption) k)
          (pow_le_pow_left₀ h2.le (by assumption) k) (by positivity) (by positivity)
      _ = 1 := by simp
  have hk0 : 2 * k ≠ 0 := by omega
  obtain ⟨C, r, hC, hr0, hr1, hb⟩ := exists_geometric_of_pow_div (sub_nonneg.2 hp1)
    (by linarith : 1 - p < 1) hk0
  have htail : ∀ n : ℕ, (iidLaw ν).real {g : ℕ → ℝ | (n : ℕ∞) < gapSegLen eps g} ≤ C * r ^ n :=
    fun n => (iidLaw_segLen_gt_le ν ha' hab hk n).trans (hb n)
  have hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤ := by
    have hnull : (iidLaw ν).real {g : ℕ → ℝ | gapSegLen eps g = ⊤} = 0 := by
      refine le_antisymm (ge_of_tendsto ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C
        |>.trans (by simp)) (Eventually.of_forall fun n => ?_)) measureReal_nonneg
      refine (measureReal_mono fun g hg => ?_).trans (htail n)
      simp only [mem_ofPred_eq] at hg ⊢
      rw [hg]
      exact ENat.natCast_lt_top n
    have hnull' : (iidLaw ν) {g : ℕ → ℝ | gapSegLen eps g = ⊤} = 0 := by
      rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hnull
      exact hnull.resolve_right (measure_ne_top _ _)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull'] with g hg
    exact hg
  refine ⟨hfin, ⟨(measurable_toNat_gapSegLen eps).aestronglyMeasurable, ?_⟩⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun g => Nat.cast_nonneg _)]
  have hpt : ∀ g : ℕ → ℝ, ENNReal.ofReal ((gapSegLen eps g).toNat : ℝ) ≤
      ∑' n : ℕ, {g : ℕ → ℝ | (n : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : ENNReal)) g := by
    intro g
    rw [ENNReal.ofReal_natCast]
    refine le_trans ?_ (ENNReal.sum_le_tsum (Finset.range (gapSegLen eps g).toNat))
    have hone : ∀ x ∈ Finset.range (gapSegLen eps g).toNat,
        {g : ℕ → ℝ | (x : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : ENNReal)) g = 1 := by
      intro x hx
      refine indicator_of_mem ?_ _
      simp only [mem_ofPred_eq]
      have := Finset.mem_range.1 hx
      exact lt_of_lt_of_le (by exact_mod_cast this) (ENat.natCast_toNat_le_self _)
    rw [Finset.sum_congr rfl hone]
    simp
  calc ∫⁻ g, ENNReal.ofReal ((gapSegLen eps g).toNat : ℝ) ∂(iidLaw ν)
      ≤ ∫⁻ g, ∑' n : ℕ, {g : ℕ → ℝ | (n : ℕ∞) < gapSegLen eps g}.indicator
          (fun _ => (1 : ENNReal)) g ∂(iidLaw ν) := lintegral_mono hpt
    _ = ∑' n : ℕ, (iidLaw ν) {g : ℕ → ℝ | (n : ℕ∞) < gapSegLen eps g} := by
        rw [lintegral_tsum fun n => (measurable_const.indicator
          (measurableSet_lt_gapSegLen eps n)).aemeasurable]
        congr 1
        funext n
        rw [lintegral_indicator_const (measurableSet_lt_gapSegLen eps n), one_mul]
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C * r ^ n) := ENNReal.tsum_le_tsum fun n => by
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (htail n)
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
          ((summable_geometric_of_lt_one hr0 hr1).mul_left C)]
        exact ENNReal.ofReal_lt_top

/-! ## Regular laws -/

/-- A regular law charges both `(0, a')` and `(b', ∞)` for some `0 < a' < b'`: a mean-one law with
positive variance is not concentrated on either side of `1`. -/
theorem RegLaw.exists_two_sided {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (h : RegLaw D θ vlo vhi ν) (hvlo : 0 < vlo) :
    ∃ a' b' : ℝ, 0 < a' ∧ a' < b' ∧ 0 < (ν : Measure ℝ).real (Ioo 0 a') ∧
      0 < (ν : Measure ℝ).real (Ioi b') := by
  obtain ⟨f, hfm, hf0, hfz, -, hν⟩ := h.density
  have hIic : (ν : Measure ℝ) (Iic 0) = 0 := by
    rw [hν, withDensity_apply _ measurableSet_Iic]
    refine (setLIntegral_congr_fun measurableSet_Iic fun x hx => ?_).trans lintegral_zero
    simp [hfz x hx]
  have hmean : ∫ x, x ∂(ν : Measure ℝ) = 1 := h.mean
  have hint : Integrable (fun x : ℝ => x) (ν : Measure ℝ) := by
    by_contra hni
    rw [integral_undef hni] at hmean
    norm_num at hmean
  have hvar : 0 < ∫ x, (x - 1) ^ 2 ∂(ν : Measure ℝ) := by
    have := h.var_ge
    unfold lawVar at this
    rw [show lawMean ν = 1 from h.mean] at this
    linarith
  have hsub : ∫ x, (x - 1) ∂(ν : Measure ℝ) = 0 := by
    rw [integral_sub hint (integrable_const 1), hmean]; simp
  -- both sides of `1` are charged
  have hlow : (ν : Measure ℝ) (Ioo 0 1) ≠ 0 := by
    intro h0
    have hae : ∀ᵐ x ∂(ν : Measure ℝ), 0 ≤ x - 1 := by
      have hnull : (ν : Measure ℝ) (Iic 0 ∪ Ioo 0 1) = 0 := measure_union_null hIic h0
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
      simp only [mem_union, mem_Iic, mem_Ioo, not_or, not_and, not_lt] at hx
      have := hx.2 (lt_of_not_ge hx.1)
      linarith
    have hzero := (integral_eq_zero_iff_of_nonneg_ae hae (hint.sub (integrable_const 1))).1 hsub
    have : ∫ x, (x - 1) ^ 2 ∂(ν : Measure ℝ) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hzero] with x hx
      simp only [Pi.zero_apply] at hx ⊢
      rw [hx]; ring
    linarith
  have hhigh : (ν : Measure ℝ) (Ioi 1) ≠ 0 := by
    intro h0
    have hae : ∀ᵐ x ∂(ν : Measure ℝ), 0 ≤ 1 - x := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
      simp only [mem_Ioi, not_lt] at hx
      linarith
    have hsub' : ∫ x, (1 - x) ∂(ν : Measure ℝ) = 0 := by
      rw [integral_sub (integrable_const 1) hint, hmean]; simp
    have hzero := (integral_eq_zero_iff_of_nonneg_ae hae ((integrable_const 1).sub hint)).1 hsub'
    have : ∫ x, (x - 1) ^ 2 ∂(ν : Measure ℝ) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hzero] with x hx
      simp only [Pi.zero_apply] at hx ⊢
      have : x = 1 := by linarith
      rw [this]; ring
    linarith
  -- pass to strictly separated levels
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (ν : Measure ℝ) (Ioo 0 (1 - 1 / ((n : ℝ) + 2))) ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hlow
    have e : Ioo (0 : ℝ) 1 = ⋃ n : ℕ, Ioo 0 (1 - 1 / ((n : ℝ) + 2)) := by
      ext x
      simp only [mem_Ioo, mem_iUnion]
      constructor
      · rintro ⟨hx0, hx1⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx1)
        refine ⟨n, hx0, ?_⟩
        have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith
      · rintro ⟨n, hx0, hx1⟩
        have : 0 < 1 / ((n : ℝ) + 2) := by positivity
        exact ⟨hx0, by linarith⟩
    rw [e]
    exact measure_iUnion_null hc
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (ν : Measure ℝ) (Ioi (1 + 1 / ((m : ℝ) + 1))) ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hhigh
    have e : Ioi (1 : ℝ) = ⋃ m : ℕ, Ioi (1 + 1 / ((m : ℝ) + 1)) := by
      ext x
      simp only [mem_Ioi, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
        exact ⟨m, by linarith⟩
      · rintro ⟨m, hm⟩
        have : 0 < 1 / ((m : ℝ) + 1) := by positivity
        linarith
    rw [e]
    exact measure_iUnion_null hc
  have hn2 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  refine ⟨1 - 1 / ((n : ℝ) + 2), 1 + 1 / ((m : ℝ) + 1), by linarith, ?_,
    ENNReal.toReal_pos hn (measure_ne_top _ _), ENNReal.toReal_pos hm (measure_ne_top _ _)⟩
  have : 0 < 1 / ((m : ℝ) + 1) := by positivity
  have : 0 < 1 / ((n : ℝ) + 2) := by positivity
  linarith

/-- For a regular law the first segment is a.s. finite and integrable, for every `ε`. -/
theorem RegLaw.segLen_finite {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (h : RegLaw D θ vlo vhi ν) (hvlo : 0 < vlo) (eps : ℝ) :
    (∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤) ∧
      Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν) := by
  obtain ⟨a', b', ha', hab, h1, h2⟩ := h.exists_two_sided hvlo
  exact gapSegLen_finite_integrable ν ha' hab h1 h2 eps

/-- **Theorem (E) on the regular class, every `ε > 0`.** For `RegLaw D θ vlo vhi ν` with `vlo > 0`,
any bounded density `f` of `ν` vanishing on `(-∞, 0]`, `ε > 0` and `Re t ≥ 0`:
`E e^{-tS_T} = φ(t)^{⌊2ε⌋+1} - (1 - φ(t)) ∫_{(-1,∞)} J_t`, with `J_t` integrable,
`∫ ‖J_t‖ ≤ ∫ ‖J_0‖ = E T - ⌊2ε⌋ - 1`. -/
theorem ceps_exact_marked_rep_of_regLaw_pos {D θ vlo vhi eps : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hvlo : 0 < vlo) (heps : 0 < eps) {f : ℝ → ℝ}
    (hf : CepsGapDensity ν f D) {t : ℂ} (ht : 0 ≤ t.re) :
    ∫ g, Complex.exp (-t * stopSum eps g) ∂(iidLaw ν) =
        cepsLaplace ν t ^ (⌊2 * eps⌋₊ + 1) -
          (1 - cepsLaplace ν t) * ∫ μ in Ioi (-1 : ℝ), cepsActualPair ν f eps t μ ∧
      IntegrableOn (cepsActualPair ν f eps t) (Ioi (-1 : ℝ)) ∧
      ∫ μ in Ioi (-1 : ℝ), ‖cepsActualPair ν f eps t μ‖ ≤
        ∫ μ in Ioi (-1 : ℝ), ‖cepsActualPair ν f eps 0 μ‖ ∧
      ∫ μ in Ioi (-1 : ℝ), ‖cepsActualPair ν f eps 0 μ‖ = lawC eps ν - ((⌊2 * eps⌋₊ : ℝ) + 1) := by
  obtain ⟨hfin, hT⟩ := hν.segLen_finite hvlo eps
  exact ⟨hf.ceps_exact_marked_rep heps hfin hT ht, hf.ceps_exact_marked_rep_domination heps hfin hT ht⟩

end

end PGM
