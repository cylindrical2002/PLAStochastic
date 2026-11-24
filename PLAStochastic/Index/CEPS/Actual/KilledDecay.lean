import PLAStochastic.Index.CEPS.Actual.Defs
import PLAStochastic.Index.CEPS.Actual.Telescope

/-!
# P-CEPS WP8: geometric decay of killed survival in a closed band

For a gap law with a density and any slope `a ≠ 0`, the walk `y ↦ y + β - a x` killed outside the
closed band `[0, l]` survives `n` steps with probability at most `C rⁿ`, `r < 1`, uniformly in the
start (`CepsGapDensity.krSurv_geometric`). The step `β - aX` has no atom at `0`, so some direction
carries mass `p > 0` beyond `δ > 0`; `N` such steps in a row (`Nδ > l`) leave the band, so `N`-step
survival is at most `1 - p^N`, and the Markov property iterates this bound. The downward case is
the upward one after the reflection `y ↦ l - y` (`krSurv_reflect`).

Consequences: for `Re t ≥ 0`, `Re q ≥ 0` the series defining the strip entrance `H_t`, the bridge
`U` and the marked bridge `𝔘` converge absolutely for every drift `μ` and width `l`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

/-! ## Reflection of the band -/

theorem kWalk_reflect (l y β a : ℝ) (g : ℕ → ℝ) (k : ℕ) :
    kWalk (l - y) (-β) (-a) g k = l - kWalk y β a g k := by
  unfold kWalk; ring

theorem indicator_Icc_reflect (l x : ℝ) :
    (Icc 0 l).indicator (fun _ => (1 : ℝ)) (l - x) = (Icc 0 l).indicator (fun _ => (1 : ℝ)) x := by
  by_cases h : x ∈ Icc 0 l
  · have h' : l - x ∈ Icc 0 l := ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [indicator_of_mem h, indicator_of_mem h']
  · have h' : l - x ∉ Icc 0 l := fun h' => h ⟨by linarith [h'.2], by linarith [h'.1]⟩
    rw [indicator_of_notMem h, indicator_of_notMem h']

theorem krAlive_reflect (l β a : ℝ) (n : ℕ) (y : ℝ) (g : ℕ → ℝ) :
    krAlive (Icc 0 l) (-β) (-a) n (l - y) g = krAlive (Icc 0 l) β a n y g := by
  unfold krAlive
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [kWalk_reflect, indicator_Icc_reflect]

theorem krSurv_reflect (ν : ProbabilityMeasure ℝ) (l β a : ℝ) (n : ℕ) (y : ℝ) :
    krSurv (Icc 0 l) (ν : Measure ℝ) (-β) (-a) n (l - y) =
      krSurv (Icc 0 l) (ν : Measure ℝ) β a n y := by
  rw [krSurv_eq_integral measurableSet_Icc, krSurv_eq_integral measurableSet_Icc]
  simp_rw [krAlive_reflect]

/-! ## A block of upward steps leaves the band -/

theorem kWalk_sub_eq_sum (y β a : ℝ) (g : ℕ → ℝ) (N : ℕ) :
    kWalk y β a g N - y = ∑ m ∈ Finset.range N, (β - a * g m) := by
  unfold kWalk gapKeys
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
  ring

theorem krAlive_eq_zero_of_up {l β a δ : ℝ} {N : ℕ} (hN : l < N * δ) {y : ℝ} (hy : 0 ≤ y)
    {g : ℕ → ℝ} (hg : ∀ m < N, δ < β - a * g m) : krAlive (Icc 0 l) β a N y g = 0 := by
  have hsum : (N : ℝ) * δ ≤ ∑ m ∈ Finset.range N, (β - a * g m) := by
    have := Finset.sum_le_sum fun m (hm : m ∈ Finset.range N) => (hg m (Finset.mem_range.1 hm)).le
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have hw : kWalk y β a g N ∉ Icc 0 l := by
    intro h
    have := kWalk_sub_eq_sum y β a g N
    linarith [h.2]
  unfold krAlive
  exact Finset.prod_eq_zero (Finset.mem_range.2 (Nat.lt_succ_self N)) (indicator_of_notMem hw _)

theorem krSurv_le_of_up (ν : ProbabilityMeasure ℝ) {l β a δ p : ℝ} {N : ℕ} (hN : l < N * δ)
    (hp0 : 0 ≤ p) (hp : p ≤ (ν : Measure ℝ).real {x | δ < β - a * x}) (y : ℝ) :
    krSurv (Icc 0 l) (ν : Measure ℝ) β a N y ≤ 1 - p ^ N := by
  have hp1 : p ≤ 1 := hp.trans measureReal_le_one
  have hpN : p ^ N ≤ 1 := pow_le_one₀ hp0 hp1
  rcases lt_or_ge y 0 with hy | hy
  · rw [krSurv_eq_zero_of_notMem (fun h : y ∈ Icc 0 l => by linarith [h.1])]
    linarith
  set A : Set ℝ := {x | δ < β - a * x} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const (by fun_prop)
  set E : Set (ℕ → ℝ) := Set.pi (Finset.range N : Set ℕ) (fun _ => A) with hE
  have hEm : MeasurableSet E := MeasurableSet.pi (Finset.range N).countable_toSet fun _ _ => hAm
  have hPE : (iidLaw ν).real E = ((ν : Measure ℝ).real A) ^ N := by
    rw [measureReal_def, iidLaw, hE, Measure.infinitePi_pi (fun _ : ℕ => (ν : Measure ℝ)) (fun _ _ => hAm), Finset.prod_const,
      Finset.card_range, ENNReal.toReal_pow]
    rfl
  have hle : ∀ g : ℕ → ℝ, krAlive (Icc 0 l) β a N y g ≤ 1 - E.indicator (fun _ => (1 : ℝ)) g := by
    intro g
    by_cases hg : g ∈ E
    · rw [indicator_of_mem hg, sub_self, krAlive_eq_zero_of_up hN hy fun m hm => hg m (by simpa)]
    · rw [indicator_of_notMem hg, sub_zero]
      exact krAlive_le_one _ _ _
  rw [krSurv_eq_integral measurableSet_Icc]
  calc ∫ g, krAlive (Icc 0 l) β a N y g ∂(iidLaw ν)
      ≤ ∫ g, (1 - E.indicator (fun _ => (1 : ℝ)) g) ∂(iidLaw ν) :=
        integral_mono (kr_integrable_of_bdd (measurable_krAlive_right measurableSet_Icc β a N y)
          (abs_krAlive_le_one N y)) ((integrable_const 1).sub ((integrable_const 1).indicator hEm))
          hle
    _ = 1 - (ν : Measure ℝ).real A ^ N := by
        rw [integral_sub (integrable_const 1) ((integrable_const 1).indicator hEm),
          integral_const, probReal_univ, one_smul, integral_indicator hEm, setIntegral_const,
          smul_eq_mul, mul_one, hPE]
    _ ≤ 1 - p ^ N := by
        have := pow_le_pow_left₀ hp0 hp N
        linarith

/-! ## Iterating a block bound -/

theorem krSurv_add_le (ν : ProbabilityMeasure ℝ) {l β a ρ : ℝ} {N : ℕ}
    (hN : ∀ y, krSurv (Icc 0 l) (ν : Measure ℝ) β a N y ≤ ρ) (m : ℕ) (y : ℝ) :
    krSurv (Icc 0 l) (ν : Measure ℝ) β a (m + N) y ≤
      ρ * krSurv (Icc 0 l) (ν : Measure ℝ) β a m y := by
  have hJ : MeasurableSet (Icc (0 : ℝ) l) := measurableSet_Icc
  have hM : ∀ y, |krSurv (Icc 0 l) (ν : Measure ℝ) β a N y| ≤ max 1 |ρ| := fun y => by
    rw [abs_of_nonneg (krSurv_nonneg hJ ν β a N y)]
    exact (krSurv_le_one hJ ν β a N y).trans (le_max_left _ _)
  have hMc : ∀ _y : ℝ, |ρ| ≤ max 1 |ρ| := fun _ => le_max_right _ _
  unfold krSurv
  rw [krRow_add]
  calc krRow (Icc 0 l) (ν : Measure ℝ) β a m (krRow (Icc 0 l) (ν : Measure ℝ) β a N fun _ => 1) y
      ≤ krRow (Icc 0 l) (ν : Measure ℝ) β a m (fun _ => ρ) y :=
        krRow_mono hJ ν β a m (measurable_krSurv hJ ν β a N) measurable_const hM hMc hN y
    _ = ρ * krRow (Icc 0 l) (ν : Measure ℝ) β a m (fun _ => 1) y := by
        rw [krRow_eq_integral hJ ν β a m measurable_const (M := |ρ|) (fun _ => le_rfl) y,
          krRow_eq_integral hJ ν β a m measurable_const (M := 1) (fun _ => by simp) y,
          ← integral_const_mul]
        congr 1
        funext g
        ring

theorem krSurv_mul_le_pow (ν : ProbabilityMeasure ℝ) {l β a ρ : ℝ} {N : ℕ} (hρ : 0 ≤ ρ)
    (hN : ∀ y, krSurv (Icc 0 l) (ν : Measure ℝ) β a N y ≤ ρ) (n : ℕ) (y : ℝ) :
    krSurv (Icc 0 l) (ν : Measure ℝ) β a (N * n) y ≤ ρ ^ n := by
  induction n generalizing y with
  | zero =>
    simpa using krSurv_le_one measurableSet_Icc ν β a 0 y
  | succ n ih =>
    rw [Nat.mul_succ, pow_succ]
    calc krSurv (Icc 0 l) (ν : Measure ℝ) β a (N * n + N) y
        ≤ ρ * krSurv (Icc 0 l) (ν : Measure ℝ) β a (N * n) y := krSurv_add_le ν hN _ y
      _ ≤ ρ * ρ ^ n := mul_le_mul_of_nonneg_left (ih y) hρ
      _ = ρ ^ n * ρ := mul_comm _ _

theorem krSurv_geometric_of_block (ν : ProbabilityMeasure ℝ) {l β a ρ : ℝ} {N : ℕ} (hN0 : N ≠ 0)
    (hρ1 : ρ < 1) (hN : ∀ y, krSurv (Icc 0 l) (ν : Measure ℝ) β a N y ≤ ρ) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
      ∀ n y, krSurv (Icc 0 l) (ν : Measure ℝ) β a n y ≤ C * r ^ n := by
  set ρ' := max ρ (1 / 2) with hρ'
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hρ'1 : ρ' < 1 := max_lt hρ1 (by norm_num)
  have hN' : ∀ y, krSurv (Icc 0 l) (ν : Measure ℝ) β a N y ≤ ρ' := fun y =>
    (hN y).trans (le_max_left _ _)
  set r := ρ' ^ ((N : ℝ)⁻¹) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hρ'0.le _
  have hr1 : r < 1 := Real.rpow_lt_one hρ'0.le hρ'1 (by positivity)
  have hrN : r ^ N = ρ' := Real.rpow_inv_natCast_pow hρ'0.le hN0
  refine ⟨1 / ρ', r, by positivity, hr0, hr1, fun n y => ?_⟩
  have h1 : krSurv (Icc 0 l) (ν : Measure ℝ) β a n y ≤ ρ' ^ (n / N) :=
    (krSurv_le_of_le measurableSet_Icc ν β a (Nat.mul_div_le n N) y).trans
      (krSurv_mul_le_pow ν hρ'0.le hN' (n / N) y)
  have h2 : ρ' ^ (n / N) * ρ' ≤ r ^ n := by
    rw [← hrN, ← pow_mul, ← pow_add]
    refine pow_le_pow_of_le_one hr0 hr1.le ?_
    have h1 := Nat.div_add_mod n N
    have h2 := Nat.mod_lt n (Nat.pos_of_ne_zero hN0)
    omega
  calc krSurv (Icc 0 l) (ν : Measure ℝ) β a n y ≤ ρ' ^ (n / N) := h1
    _ ≤ 1 / ρ' * r ^ n := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hρ'0]
        exact h2

/-! ## Geometric decay for gap laws with a density -/

variable {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} {D : ℝ}

/-- A non-degenerate step has mass beyond some `δ > 0` in one direction. -/
theorem CepsGapDensity.exists_step_mass (hf : CepsGapDensity ν f D) (β : ℝ) {a : ℝ}
    (ha : a ≠ 0) : ∃ δ p : ℝ, 0 < δ ∧ 0 < p ∧
      (p ≤ (ν : Measure ℝ).real {x | δ < β - a * x} ∨
        p ≤ (ν : Measure ℝ).real {x | β - a * x < -δ}) := by
  have hnull : (ν : Measure ℝ) {x | β - a * x = 0} = 0 := by
    have e : {x : ℝ | β - a * x = 0} = {β / a} := by
      ext x
      simp only [mem_ofPred_eq, mem_singleton_iff]
      constructor
      · intro h; field_simp; linarith
      · intro h; rw [h]; field_simp; ring
    rw [e]
    exact hf.absolutelyContinuous (Real.volume_singleton)
  have hU : {x : ℝ | β - a * x ≠ 0} =
      ⋃ n : ℕ, ({x | 1 / ((n : ℝ) + 1) < β - a * x} ∪ {x | β - a * x < -(1 / ((n : ℝ) + 1))}) := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_union]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.2 h)
      rcases lt_or_gt_of_ne h with h' | h'
      · refine ⟨n, Or.inr ?_⟩
        rw [abs_of_neg h'] at hn; linarith
      · refine ⟨n, Or.inl ?_⟩
        rw [abs_of_pos h'] at hn; linarith
    · rintro ⟨n, h | h⟩
      · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        intro h0; rw [h0] at h; linarith
      · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        intro h0; rw [h0] at h; linarith
  have hpos : (ν : Measure ℝ) {x | β - a * x ≠ 0} ≠ 0 := by
    intro h0
    have hall : (ν : Measure ℝ) univ = 0 := by
      have e : (univ : Set ℝ) = {x | β - a * x ≠ 0} ∪ {x | β - a * x = 0} := by
        ext x; simp [em']
      rw [e]
      exact measure_union_null h0 hnull
    simp at hall
  rw [hU] at hpos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (ν : Measure ℝ)
      ({x | 1 / ((n : ℝ) + 1) < β - a * x} ∪ {x | β - a * x < -(1 / ((n : ℝ) + 1))}) ≠ 0 := by
    by_contra h
    push Not at h
    exact hpos (measure_iUnion_null h)
  set δ : ℝ := 1 / ((n : ℝ) + 1)
  have hδ : 0 < δ := by positivity
  by_cases h1 : (ν : Measure ℝ) {x | δ < β - a * x} = 0
  · have h2 : (ν : Measure ℝ) {x | β - a * x < -δ} ≠ 0 := fun h2 => hn (measure_union_null h1 h2)
    refine ⟨δ, (ν : Measure ℝ).real {x | β - a * x < -δ}, hδ, ?_, Or.inr le_rfl⟩
    exact ENNReal.toReal_pos h2 (measure_ne_top _ _)
  · refine ⟨δ, (ν : Measure ℝ).real {x | δ < β - a * x}, hδ, ?_, Or.inl le_rfl⟩
    exact ENNReal.toReal_pos h1 (measure_ne_top _ _)

/-- **Geometric decay of killed survival** in a closed band, uniformly in the start. -/
theorem CepsGapDensity.krSurv_geometric (hf : CepsGapDensity ν f D) (l β : ℝ) {a : ℝ}
    (ha : a ≠ 0) : ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
      ∀ n y, krSurv (Icc 0 l) (ν : Measure ℝ) β a n y ≤ C * r ^ n := by
  obtain ⟨δ, p, hδ, hp, hdir⟩ := hf.exists_step_mass β ha
  set N : ℕ := ⌈l / δ⌉₊ + 1 with hNdef
  have hN0 : N ≠ 0 := Nat.succ_ne_zero _
  have hN : l < N * δ := by
    have h1 : l / δ ≤ ⌈l / δ⌉₊ := Nat.le_ceil _
    have h2 : (⌈l / δ⌉₊ : ℝ) < N := by rw [hNdef]; push_cast; linarith
    have := (div_lt_iff₀ hδ).1 (h1.trans_lt h2)
    linarith
  have hp1 : p ≤ 1 := by
    rcases hdir with h | h <;> exact h.trans measureReal_le_one
  have hρ1 : 1 - p ^ N < 1 := by linarith [pow_pos hp N]
  rcases hdir with hup | hdown
  · exact krSurv_geometric_of_block ν hN0 hρ1 fun y => krSurv_le_of_up ν hN hp.le hup y
  · have hup' : p ≤ (ν : Measure ℝ).real {x | δ < -β - -a * x} := by
      refine hdown.trans_eq ?_
      congr 1
      ext x
      simp only [mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    obtain ⟨C, r, hC, hr0, hr1, hb⟩ := krSurv_geometric_of_block ν (β := -β) (a := -a) (l := l)
      hN0 hρ1 fun y => krSurv_le_of_up ν hN hp.le hup' y
    refine ⟨C, r, hC, hr0, hr1, fun n y => ?_⟩
    rw [← krSurv_reflect ν l β a n y]
    exact hb n (l - y)

/-! ## Absolute convergence of the strip series -/

theorem summable_geometric_weight {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (c : ℝ) :
    Summable (fun n : ℕ => ((n : ℝ) + c) * r ^ n) := by
  have hr : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 hr
    simpa only [pow_one] using this
  have h2 : Summable (fun n : ℕ => c * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left c
  have e : (fun n : ℕ => ((n : ℝ) + c) * r ^ n) = fun n : ℕ => (n : ℝ) * r ^ n + c * r ^ n := by
    funext n; ring
  rw [e]
  exact h1.add h2

theorem norm_cexp_neg_mul_nat_le_one {q : ℂ} (hq : 0 ≤ q.re) (n : ℕ) :
    ‖Complex.exp (-q * n)‖ ≤ 1 := by
  simpa using norm_cexp_neg_mul_le_one hq (Nat.cast_nonneg n)

theorem norm_cexp_neg_mul_succ_le_one {q : ℂ} (hq : 0 ≤ q.re) (n : ℕ) :
    ‖Complex.exp (-q * ((n : ℂ) + 1))‖ ≤ 1 := by
  have := norm_cexp_neg_mul_le_one hq (s := (n : ℝ) + 1) (by positivity)
  simpa using this

theorem krAlive_ne_zero_mem {l β a y : ℝ} {n : ℕ} {g : ℕ → ℝ}
    (h : krAlive (Icc 0 l) β a n y g ≠ 0) : ∀ k ≤ n, kWalk y β a g k ∈ Icc 0 l := by
  intro k hk
  by_contra hk'
  apply h
  unfold krAlive
  exact Finset.prod_eq_zero (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) (indicator_of_notMem hk' _)

/-- For `Re t ≥ 0` the outer-walk mark is bounded by the survival probability. -/
theorem norm_cepsStripTerm_le (ν : ProbabilityMeasure ℝ) {t : ℂ} (ht : 0 ≤ t.re) (μ l : ℝ)
    (n : ℕ) :
    ‖cepsStripTerm ν t μ l n‖ ≤ krSurv (Icc 0 l) (ν : Measure ℝ) (-(1 + μ)) (-1) n 0 := by
  unfold cepsStripTerm
  rw [krSurv_eq_integral measurableSet_Icc]
  refine (norm_integral_le_of_norm_le (kr_integrable_of_bdd
    (measurable_krAlive_right measurableSet_Icc _ _ n 0) (abs_krAlive_le_one n 0))
    (Eventually.of_forall fun g => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (krAlive_nonneg _ _ _)]
  by_cases h0 : krAlive (Icc 0 l) (-(1 + μ)) (-1) n 0 g = 0
  · rw [h0, zero_mul]
  · have hm := krAlive_ne_zero_mem h0 n le_rfl
    calc krAlive (Icc 0 l) (-(1 + μ)) (-1) n 0 g *
          ‖Complex.exp (-t * kWalk 0 (-(1 + μ)) (-1) g n)‖
        ≤ krAlive (Icc 0 l) (-(1 + μ)) (-1) n 0 g * 1 :=
          mul_le_mul_of_nonneg_left (norm_cexp_neg_mul_le_one ht hm.1) (krAlive_nonneg _ _ _)
      _ = _ := mul_one _

theorem CepsGapDensity.summable_cepsStripTerm (hf : CepsGapDensity ν f D) {t q : ℂ}
    (ht : 0 ≤ t.re) (hq : 0 ≤ q.re) (μ l : ℝ) :
    Summable (fun n : ℕ => ‖Complex.exp (-q * n) * cepsStripTerm ν t μ l n‖) := by
  obtain ⟨C, r, hC, hr0, hr1, hb⟩ := hf.krSurv_geometric l (-(1 + μ)) (a := -1) (by norm_num)
  refine ((summable_geometric_of_lt_one hr0 hr1).mul_left C).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_
  rw [norm_mul]
  calc ‖Complex.exp (-q * n)‖ * ‖cepsStripTerm ν t μ l n‖ ≤ 1 * (C * r ^ n) :=
        mul_le_mul (norm_cexp_neg_mul_nat_le_one hq n)
          ((norm_cepsStripTerm_le ν ht μ l n).trans (hb n 0)) (norm_nonneg _) zero_le_one
    _ = C * r ^ n := one_mul _

theorem CepsGapDensity.cepsBridgeDens_le (hf : CepsGapDensity ν f D) (μ l : ℝ) (n : ℕ) :
    cepsBridgeDens ν f μ l (n + 1) ≤ D * krSurv (Icc 0 l) (ν : Measure ℝ) (1 + μ) 1 n 0 := by
  have h := krDens_le_div_mul_krSurv (J := Icc 0 l) ν (β := 1 + μ) (a := 1) measurableSet_Icc
    hf.measurable hf.nonneg hf.le n 0 l
  simpa [cepsBridgeDens] using h

theorem CepsGapDensity.cepsBridgeDens_nonneg (hf : CepsGapDensity ν f D) (μ l : ℝ) (n : ℕ) :
    0 ≤ cepsBridgeDens ν f μ l n :=
  krDens_nonneg ν hf.nonneg n 0 l

theorem CepsGapDensity.summable_cepsMarkedBridge (hf : CepsGapDensity ν f D) {q : ℂ}
    (hq : 0 ≤ q.re) (w μ l : ℝ) :
    Summable (fun n : ℕ => ‖(((n : ℝ) + 1 - w : ℝ) : ℂ) * Complex.exp (-q * ((n : ℂ) + 1)) *
      cepsBridgeDens ν f μ l (n + 1)‖) := by
  obtain ⟨C, r, hC, hr0, hr1, hb⟩ := hf.krSurv_geometric l (1 + μ) (a := 1) one_ne_zero
  refine ((summable_geometric_weight hr0 hr1 (1 + |w|)).mul_left (D * C)).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_
  have hD := hf.nonneg_D
  have hk0 := hf.cepsBridgeDens_nonneg μ l (n + 1)
  have hk : cepsBridgeDens ν f μ l (n + 1) ≤ D * (C * r ^ n) :=
    (hf.cepsBridgeDens_le μ l n).trans (mul_le_mul_of_nonneg_left (hb n 0) hD)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hk0]
  have hw : |(n : ℝ) + 1 - w| ≤ (n : ℝ) + (1 + |w|) := by
    have := abs_sub ((n : ℝ) + 1) w
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)] at this
    linarith
  calc |(n : ℝ) + 1 - w| * ‖Complex.exp (-q * ((n : ℂ) + 1))‖ * cepsBridgeDens ν f μ l (n + 1)
      ≤ ((n : ℝ) + (1 + |w|)) * 1 * (D * (C * r ^ n)) :=
        mul_le_mul (mul_le_mul hw (norm_cexp_neg_mul_succ_le_one hq n) (norm_nonneg _)
          (by positivity)) hk hk0 (by positivity)
    _ = D * C * (((n : ℝ) + (1 + |w|)) * r ^ n) := by ring

theorem CepsGapDensity.summable_cepsBridge (hf : CepsGapDensity ν f D) {q : ℂ}
    (hq : 0 ≤ q.re) (μ l : ℝ) :
    Summable (fun n : ℕ => ‖Complex.exp (-q * ((n : ℂ) + 1)) * cepsBridgeDens ν f μ l (n + 1)‖) := by
  obtain ⟨C, r, hC, hr0, hr1, hb⟩ := hf.krSurv_geometric l (1 + μ) (a := 1) one_ne_zero
  refine ((summable_geometric_of_lt_one hr0 hr1).mul_left (D * C)).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_
  have hD := hf.nonneg_D
  have hk0 := hf.cepsBridgeDens_nonneg μ l (n + 1)
  have hk : cepsBridgeDens ν f μ l (n + 1) ≤ D * (C * r ^ n) :=
    (hf.cepsBridgeDens_le μ l n).trans (mul_le_mul_of_nonneg_left (hb n 0) hD)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0]
  calc ‖Complex.exp (-q * ((n : ℂ) + 1))‖ * cepsBridgeDens ν f μ l (n + 1)
      ≤ 1 * (D * (C * r ^ n)) := mul_le_mul (norm_cexp_neg_mul_succ_le_one hq n) hk hk0
        zero_le_one
    _ = D * C * r ^ n := by ring

end

end PGM
