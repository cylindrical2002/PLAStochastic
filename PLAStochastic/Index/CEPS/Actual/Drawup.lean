import PLAStochastic.Index.CEPS.Actual.FirstPassage

/-!
# P-CEPS WP8: the exact drawup cycle identity (S-2 (d))

`research/2026-10-02-lean-ceps/blueprint-CS.md` §3.6, identity (3.8). For the walk
`W_n = kWalk 0 β a g n` from `0` the drawup `D_n = W_n - min_{m ≤ n} W_m` first exceeds `l` at
`τ_l`. Since `D_j = max_{i ≤ j} (W_j - W_i)`, the event `{τ_l > N}` is
`cepsDrawupOK : ∀ i ≤ j ≤ N, W_j - W_i ≤ l`, and `{τ_l = N + 1}` is `cepsDrawupCross`.

Each time the walk makes a new minimum the drawup restarts. Started at the bottom of the band
`[0, l]`, the walk either leaves it upward (then `τ_l` is that exit time) or downward (a new minimum,
after which the drawup of the increments starts afresh). With the bottom-started exit transforms
`u = cepsStripExit … (Ioi l)` and `ℓ = cepsStripExit … (Iio 0)` (marks relative to the start):

`E[e^{-qτ_l} e^{s W_{τ_l}}; τ_l < ∞] · (1 - ℓ) = u`   (`cepsDrawup_cycle`).

No density is needed; for the `Y_δ`-walk (`β = 1 + δ`, `a = 1`) the mark at `q = t(1+δ)`, `s = t`
is `e^{-t S_{τ_l}}` (`cepsDrawupTerm_gapKeys`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

/-! ## The drawup events -/

/-- `τ_l > N`: no increment `W_j - W_i`, `i ≤ j ≤ N`, exceeds `l`. -/
def cepsDrawupOK (β a l : ℝ) (g : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i j, i ≤ j → j ≤ N → kWalk 0 β a g j - kWalk 0 β a g i ≤ l

/-- `τ_l = N + 1`. -/
def cepsDrawupCross (β a l : ℝ) (g : ℕ → ℝ) (N : ℕ) : Prop :=
  cepsDrawupOK β a l g N ∧ ∃ i ≤ N + 1, l < kWalk 0 β a g (N + 1) - kWalk 0 β a g i

theorem measurableSet_cepsDrawupOK (β a l : ℝ) (N : ℕ) :
    MeasurableSet {g : ℕ → ℝ | cepsDrawupOK β a l g N} := by
  have e : {g : ℕ → ℝ | cepsDrawupOK β a l g N} = ⋂ i : ℕ, ⋂ j : ℕ,
      {g : ℕ → ℝ | i ≤ j → j ≤ N → kWalk 0 β a g j - kWalk 0 β a g i ≤ l} := by
    ext g; simp [cepsDrawupOK]
  rw [e]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases h : i ≤ j ∧ j ≤ N
  · have e' : {g : ℕ → ℝ | i ≤ j → j ≤ N → kWalk 0 β a g j - kWalk 0 β a g i ≤ l} =
        {g : ℕ → ℝ | kWalk 0 β a g j - kWalk 0 β a g i ≤ l} := by
      ext g; simp [h.1, h.2]
    rw [e']
    exact measurableSet_le ((measurable_kWalk_right 0 β a j).sub (measurable_kWalk_right 0 β a i))
      measurable_const
  · have e' : {g : ℕ → ℝ | i ≤ j → j ≤ N → kWalk 0 β a g j - kWalk 0 β a g i ≤ l} = univ := by
      ext g
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ h
    rw [e']
    exact MeasurableSet.univ

theorem measurableSet_cepsDrawupCross (β a l : ℝ) (N : ℕ) :
    MeasurableSet {g : ℕ → ℝ | cepsDrawupCross β a l g N} := by
  have e : {g : ℕ → ℝ | cepsDrawupCross β a l g N} = {g : ℕ → ℝ | cepsDrawupOK β a l g N} ∩
      ⋃ i ∈ Finset.range (N + 2),
        {g : ℕ → ℝ | l < kWalk 0 β a g (N + 1) - kWalk 0 β a g i} := by
    ext g
    simp only [cepsDrawupCross, mem_inter_iff, mem_ofPred_eq, mem_iUnion, Finset.mem_range,
      exists_prop]
    constructor
    · rintro ⟨h1, i, hi, h2⟩; exact ⟨h1, i, by omega, h2⟩
    · rintro ⟨h1, i, hi, h2⟩; exact ⟨h1, i, by omega, h2⟩
  rw [e]
  exact (measurableSet_cepsDrawupOK β a l N).inter (Finset.measurableSet_biUnion _ fun i _ =>
    measurableSet_lt measurable_const
      ((measurable_kWalk_right 0 β a (N + 1)).sub (measurable_kWalk_right 0 β a i)))

theorem cepsDrawupCross_disjoint (β a l : ℝ) (g : ℕ → ℝ) (K : ℕ) :
    ∑ N ∈ Finset.range K, {g : ℕ → ℝ | cepsDrawupCross β a l g N}.indicator (fun _ => (1 : ℝ)) g ≤ 1 := by
  have hstep : ∀ N, {g : ℕ → ℝ | cepsDrawupCross β a l g N}.indicator (fun _ => (1 : ℝ)) g ≤
      {g : ℕ → ℝ | cepsDrawupOK β a l g N}.indicator (fun _ => (1 : ℝ)) g -
        {g : ℕ → ℝ | cepsDrawupOK β a l g (N + 1)}.indicator (fun _ => (1 : ℝ)) g := by
    intro N
    by_cases hc : cepsDrawupCross β a l g N
    · obtain ⟨hok, i, hi, hlt⟩ := hc
      have hnot : ¬ cepsDrawupOK β a l g (N + 1) := fun h => by
        have := h i (N + 1) hi le_rfl
        linarith
      rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | cepsDrawupCross β a l g N} from ⟨hok, i, hi, hlt⟩),
        indicator_of_mem (show g ∈ {g : ℕ → ℝ | cepsDrawupOK β a l g N} from hok),
        indicator_of_notMem (show g ∉ {g : ℕ → ℝ | cepsDrawupOK β a l g (N + 1)} from hnot)]
      norm_num
    · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | cepsDrawupCross β a l g N} from hc)]
      by_cases h1 : cepsDrawupOK β a l g (N + 1)
      · have h0 : cepsDrawupOK β a l g N := fun i j hij hj => h1 i j hij (by omega)
        rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | cepsDrawupOK β a l g N} from h0),
          indicator_of_mem (show g ∈ {g : ℕ → ℝ | cepsDrawupOK β a l g (N + 1)} from h1)]
        norm_num
      · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | cepsDrawupOK β a l g (N + 1)} from h1),
          sub_zero]
        exact indicator_nonneg (fun _ _ => zero_le_one) _
  calc _ ≤ ∑ N ∈ Finset.range K,
        ({g : ℕ → ℝ | cepsDrawupOK β a l g N}.indicator (fun _ => (1 : ℝ)) g -
          {g : ℕ → ℝ | cepsDrawupOK β a l g (N + 1)}.indicator (fun _ => (1 : ℝ)) g) :=
        Finset.sum_le_sum fun N _ => hstep N
    _ = _ := Finset.sum_range_sub' _ _
    _ ≤ 1 := by
        have h1 : {g : ℕ → ℝ | cepsDrawupOK β a l g 0}.indicator (fun _ => (1 : ℝ)) g ≤ 1 := by
          by_cases h : g ∈ {g : ℕ → ℝ | cepsDrawupOK β a l g 0} <;> simp [h]
        have h2 := indicator_nonneg (fun _ _ => zero_le_one)
          (s := {g : ℕ → ℝ | cepsDrawupOK β a l g K}) (f := fun _ => (1 : ℝ)) g
        linarith

/-! ## The drawup transform -/

/-- `E[e^{s W_{N+1}}; τ_l = N + 1]`. -/
def cepsDrawupTerm (ν : ProbabilityMeasure ℝ) (β a l : ℝ) (s : ℂ) (N : ℕ) : ℂ :=
  ∫ g, {g : ℕ → ℝ | cepsDrawupCross β a l g N}.indicator (fun _ => (1 : ℂ)) g *
    Complex.exp (s * (kWalk 0 β a g (N + 1) : ℂ)) ∂(iidLaw ν)

/-- The drawup transform `E[e^{-qτ_l} e^{s W_{τ_l}}; τ_l < ∞]`. -/
def cepsDrawup (ν : ProbabilityMeasure ℝ) (β a l : ℝ) (s q : ℂ) : ℂ :=
  ∑' N : ℕ, Complex.exp (-q * ((N : ℂ) + 1)) * cepsDrawupTerm ν β a l s N

/-- The probability `P(τ_l = N + 1)`. -/
def cepsDrawupProb (ν : ProbabilityMeasure ℝ) (β a l : ℝ) (N : ℕ) : ℝ :=
  (iidLaw ν).real {g : ℕ → ℝ | cepsDrawupCross β a l g N}

theorem summable_cepsDrawupProb (ν : ProbabilityMeasure ℝ) (β a l : ℝ) :
    Summable (cepsDrawupProb ν β a l) := by
  refine summable_of_sum_range_le (c := 1) (fun N => measureReal_nonneg) fun K => ?_
  have hint : ∀ N, Integrable ({g : ℕ → ℝ | cepsDrawupCross β a l g N}.indicator
      (fun _ => (1 : ℝ))) (iidLaw ν) := fun N =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_cepsDrawupCross β a l N)
  have e : ∀ N, cepsDrawupProb ν β a l N = ∫ g, {g : ℕ → ℝ | cepsDrawupCross β a l g N}.indicator
      (fun _ => (1 : ℝ)) g ∂(iidLaw ν) := fun N => by
    rw [integral_indicator (measurableSet_cepsDrawupCross β a l N), setIntegral_const, smul_eq_mul,
      mul_one]
    rfl
  simp_rw [e]
  rw [← integral_finsetSum _ fun N _ => hint N]
  exact (integral_mono (integrable_finsetSum _ fun N _ => hint N) (integrable_const 1)
    fun g => cepsDrawupCross_disjoint β a l g K).trans (by simp)

theorem norm_cepsDrawupTerm_le (ν : ProbabilityMeasure ℝ) (β a l : ℝ) {s : ℂ} (hs : s.re = 0)
    (N : ℕ) : ‖cepsDrawupTerm ν β a l s N‖ ≤ cepsDrawupProb ν β a l N := by
  unfold cepsDrawupTerm cepsDrawupProb
  refine (norm_integral_le_of_norm_le ((integrable_const (1 : ℝ)).indicator
    (measurableSet_cepsDrawupCross β a l N)) (Eventually.of_forall fun g => ?_)).trans
    (le_of_eq ?_)
  · by_cases h : g ∈ {g : ℕ → ℝ | cepsDrawupCross β a l g N}
    · rw [indicator_of_mem h, indicator_of_mem h, one_mul, norm_cexp_mul_ofReal_of_re_eq_zero hs]
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul, norm_zero]
  · rw [integral_indicator (measurableSet_cepsDrawupCross β a l N), setIntegral_const, smul_eq_mul,
      mul_one]

theorem summable_cepsDrawup (ν : ProbabilityMeasure ℝ) (β a l : ℝ) {s q : ℂ} (hs : s.re = 0)
    (hq : 0 ≤ q.re) :
    Summable fun N : ℕ => ‖Complex.exp (-q * ((N : ℂ) + 1)) * cepsDrawupTerm ν β a l s N‖ := by
  refine (summable_cepsDrawupProb ν β a l).of_nonneg_of_le (fun N => norm_nonneg _) fun N => ?_
  rw [norm_mul]
  calc _ ≤ 1 * cepsDrawupProb ν β a l N :=
        mul_le_mul (norm_cexp_neg_mul_succ_le_one hq N) (norm_cepsDrawupTerm_le ν β a l hs N)
          (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-! ## Pathwise regeneration -/

theorem kWalk_zero_shift (β a : ℝ) (g : ℕ → ℝ) (k j : ℕ) :
    kWalk 0 β a (WienerHopf.shift k g) j = kWalk 0 β a g (k + j) - kWalk 0 β a g k := by
  unfold kWalk WienerHopf.shift
  rw [gapKeys_shift]
  push_cast
  ring

/-- Inside the band up to `N`, the drawup crosses at `N + 1` exactly by an upward exit. -/
theorem cepsDrawupCross_iff_of_alive {β a l : ℝ} (hl : 0 ≤ l) {g : ℕ → ℝ} {N : ℕ}
    (h : ∀ k ≤ N, kWalk 0 β a g k ∈ Icc 0 l) :
    cepsDrawupCross β a l g N ↔ l < kWalk 0 β a g (N + 1) := by
  constructor
  · rintro ⟨-, i, hi, hlt⟩
    rcases Nat.lt_or_ge i (N + 1) with hi' | hi'
    · have := (h i (by omega)).1; linarith
    · have : i = N + 1 := by omega
      subst this; linarith
  · intro hlt
    refine ⟨fun i j hij hj => ?_, 0, Nat.zero_le _, by rw [kWalk_zero]; linarith⟩
    have h1 := h i (by omega)
    have h2 := h j hj
    linarith [h1.1, h2.2]

/-- An upward exit of the band before `N + 1` already crossed. -/
theorem not_cepsDrawupCross_of_high {β a l : ℝ} {g : ℕ → ℝ} {n N : ℕ} (hnN : n < N)
    (hhigh : l < kWalk 0 β a g (n + 1)) : ¬ cepsDrawupCross β a l g N := by
  rintro ⟨hok, -⟩
  have := hok 0 (n + 1) (Nat.zero_le _) (by omega)
  rw [kWalk_zero, sub_zero] at this
  linarith

/-- A downward exit of the band is a new minimum: the drawup restarts from it. -/
theorem cepsDrawupCross_iff_of_low {β a l : ℝ} {g : ℕ → ℝ} {n N : ℕ} (hnN : n < N)
    (h : ∀ k ≤ n, kWalk 0 β a g k ∈ Icc 0 l) (hlow : kWalk 0 β a g (n + 1) < 0) :
    cepsDrawupCross β a l g N ↔
      cepsDrawupCross β a l (WienerHopf.shift (n + 1) g) (N - (n + 1)) := by
  have hW : ∀ j, kWalk 0 β a (WienerHopf.shift (n + 1) g) j =
      kWalk 0 β a g (n + 1 + j) - kWalk 0 β a g (n + 1) := kWalk_zero_shift β a g (n + 1)
  constructor
  · rintro ⟨hok, i, hi, hlt⟩
    refine ⟨fun i' j' hij hj => ?_, ?_⟩
    · rw [hW, hW]
      have := hok (n + 1 + i') (n + 1 + j') (by omega) (by omega)
      linarith
    · rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
      · refine ⟨0, Nat.zero_le _, ?_⟩
        rw [hW, hW, Nat.add_zero, show n + 1 + (N - (n + 1) + 1) = N + 1 by omega]
        have := (h i (by omega)).1
        linarith
      · refine ⟨i - (n + 1), by omega, ?_⟩
        rw [hW, hW, show n + 1 + (N - (n + 1) + 1) = N + 1 by omega,
          show n + 1 + (i - (n + 1)) = i by omega]
        linarith
  · rintro ⟨hok, i, hi, hlt⟩
    refine ⟨fun i' j' hij hj => ?_, n + 1 + i, by omega, ?_⟩
    · rcases Nat.lt_or_ge j' (n + 1) with hj' | hj'
      · have h1 := h i' (by omega)
        have h2 := h j' (by omega)
        linarith [h1.1, h2.2]
      · rcases Nat.lt_or_ge i' (n + 1) with hi' | hi'
        · have h1 := (h i' (by omega)).1
          have := hok 0 (j' - (n + 1)) (Nat.zero_le _) (by omega)
          rw [hW, hW, Nat.add_zero, show n + 1 + (j' - (n + 1)) = j' by omega] at this
          linarith
        · have := hok (i' - (n + 1)) (j' - (n + 1)) (by omega) (by omega)
          rw [hW, hW, show n + 1 + (j' - (n + 1)) = j' by omega,
            show n + 1 + (i' - (n + 1)) = i' by omega] at this
          linarith
    · rw [hW, hW, show n + 1 + (N - (n + 1) + 1) = N + 1 by omega] at hlt
      linarith

/-! ## The decomposition of each crossing time -/

theorem indicator_Icc_add_Iio_add_Ioi_real {l : ℝ} (hl : 0 ≤ l) (x : ℝ) :
    (Icc 0 l).indicator (fun _ => (1 : ℝ)) x + ((Iio 0).indicator (fun _ => (1 : ℝ)) x +
      (Ioi l).indicator (fun _ => (1 : ℝ)) x) = 1 := by
  have h := indicator_Icc_add_Iio_add_Ioi hl x
  simp only [indicator_one_ofReal] at h
  exact_mod_cast (by rw [← add_assoc]; exact_mod_cast h :
    ((Icc 0 l).indicator (fun _ => (1 : ℝ)) x + ((Iio 0).indicator (fun _ => (1 : ℝ)) x +
      (Ioi l).indicator (fun _ => (1 : ℝ)) x) : ℂ) = 1)

/-- Partition of unity by the first exit of `[0, l]` from the bottom. -/
theorem krAlive_partition {l : ℝ} (hl : 0 ≤ l) (β a : ℝ) (g : ℕ → ℝ) (N : ℕ) :
    krAlive (Icc 0 l) β a N 0 g + ∑ n ∈ Finset.range N, krAlive (Icc 0 l) β a n 0 g *
      ((Iio 0).indicator (fun _ => (1 : ℝ)) (kWalk 0 β a g (n + 1)) +
        (Ioi l).indicator (fun _ => (1 : ℝ)) (kWalk 0 β a g (n + 1))) = 1 := by
  induction N with
  | zero =>
    simp [krAlive_zero, indicator_of_mem (show (0 : ℝ) ∈ Icc 0 l from ⟨le_rfl, hl⟩)]
  | succ N ih =>
    rw [Finset.sum_range_succ, krAlive_succ_last]
    have h := indicator_Icc_add_Iio_add_Ioi_real hl (kWalk 0 β a g (N + 1))
    linear_combination ih + krAlive (Icc 0 l) β a N 0 g * h

theorem ofReal_krAlive_mul_eq {l β a : ℝ} {n : ℕ} {g : ℕ → ℝ} {X Y : ℂ}
    (h : krAlive (Icc 0 l) β a n 0 g ≠ 0 → X = Y) :
    (krAlive (Icc 0 l) β a n 0 g : ℂ) * X = (krAlive (Icc 0 l) β a n 0 g : ℂ) * Y := by
  by_cases h0 : krAlive (Icc 0 l) β a n 0 g = 0
  · rw [h0]; simp
  · rw [h h0]

/-- The post-exit drawup integrand on the shifted path. -/
def cepsDrawupIntegrand (β a l : ℝ) (s : ℂ) (M : ℕ) (h : ℕ → ℝ) : ℂ :=
  {g : ℕ → ℝ | cepsDrawupCross β a l g M}.indicator (fun _ => (1 : ℂ)) h *
    Complex.exp (s * (kWalk 0 β a h (M + 1) : ℂ))

theorem measurable_cepsDrawupIntegrand (β a l : ℝ) (s : ℂ) (M : ℕ) :
    Measurable (cepsDrawupIntegrand β a l s M) :=
  (measurable_const.indicator (measurableSet_cepsDrawupCross β a l M)).mul
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_kWalk_right 0 β a (M + 1)))))

theorem norm_cepsDrawupIntegrand_le (β a l : ℝ) {s : ℂ} (hs : s.re = 0) (M : ℕ) (h : ℕ → ℝ) :
    ‖cepsDrawupIntegrand β a l s M h‖ ≤ 1 := by
  unfold cepsDrawupIntegrand
  rw [norm_mul, norm_cexp_mul_ofReal_of_re_eq_zero hs, mul_one]
  by_cases hh : h ∈ {g : ℕ → ℝ | cepsDrawupCross β a l g M} <;> simp [hh]

theorem cepsDrawupIntegrand_pathwise {β a l : ℝ} (hl : 0 ≤ l) (s : ℂ) (N : ℕ) (g : ℕ → ℝ) :
    cepsDrawupIntegrand β a l s N g =
      (krAlive (Icc 0 l) β a N 0 g : ℂ) * (Ioi l).indicator (fun _ => (1 : ℂ)) (kWalk 0 β a g (N + 1)) *
        Complex.exp (s * ((kWalk 0 β a g (N + 1) - 0 : ℝ) : ℂ)) +
      ∑ n ∈ Finset.range N, ((krAlive (Icc 0 l) β a n 0 g : ℂ) *
        (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk 0 β a g (n + 1)) *
        Complex.exp (s * ((kWalk 0 β a g (n + 1) - 0 : ℝ) : ℂ))) *
        cepsDrawupIntegrand β a l s (N - (n + 1)) (WienerHopf.shift (n + 1) g) := by
  have hpart := congrArg (fun x : ℝ => (x : ℂ)) (krAlive_partition hl β a g N)
  simp only [Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_one,
    ← indicator_one_ofReal] at hpart
  conv_lhs => rw [← mul_one (cepsDrawupIntegrand β a l s N g), ← hpart]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_comm]
    unfold cepsDrawupIntegrand
    simp only [mul_assoc]
    refine ofReal_krAlive_mul_eq fun h0 => ?_
    have halive := krAlive_ne_zero_mem h0
    have hiff := cepsDrawupCross_iff_of_alive hl halive
    rw [sub_zero]
    by_cases hc : cepsDrawupCross β a l g N
    · rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | cepsDrawupCross β a l g N} from hc),
        indicator_of_mem (show kWalk 0 β a g (N + 1) ∈ Ioi l from hiff.1 hc)]
    · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | cepsDrawupCross β a l g N} from hc),
        indicator_of_notMem (show kWalk 0 β a g (N + 1) ∉ Ioi l from fun h => hc (hiff.2 h))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hnN := Finset.mem_range.1 hn
    have hhigh : (krAlive (Icc 0 l) β a n 0 g : ℂ) *
        (Ioi l).indicator (fun _ => (1 : ℂ)) (kWalk 0 β a g (n + 1)) *
          cepsDrawupIntegrand β a l s N g = 0 := by
      by_cases hh : kWalk 0 β a g (n + 1) ∈ Ioi l
      · have hnc := not_cepsDrawupCross_of_high (β := β) (a := a) (g := g) hnN hh
        unfold cepsDrawupIntegrand
        rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | cepsDrawupCross β a l g N} from hnc)]
        ring
      · rw [indicator_of_notMem hh]; ring
    have hlow : (krAlive (Icc 0 l) β a n 0 g : ℂ) *
        (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk 0 β a g (n + 1)) *
          cepsDrawupIntegrand β a l s N g =
        (krAlive (Icc 0 l) β a n 0 g : ℂ) *
        (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk 0 β a g (n + 1)) *
          (Complex.exp (s * ((kWalk 0 β a g (n + 1) - 0 : ℝ) : ℂ)) *
          cepsDrawupIntegrand β a l s (N - (n + 1)) (WienerHopf.shift (n + 1) g)) := by
      simp only [mul_assoc]
      refine ofReal_krAlive_mul_eq fun h0 => ?_
      by_cases hlo : kWalk 0 β a g (n + 1) ∈ Iio 0
      · have halive := krAlive_ne_zero_mem h0
        have hiff := cepsDrawupCross_iff_of_low hnN halive hlo
        congr 1
        unfold cepsDrawupIntegrand
        have hW : kWalk 0 β a (WienerHopf.shift (n + 1) g) (N - (n + 1) + 1) =
            kWalk 0 β a g (N + 1) - kWalk 0 β a g (n + 1) := by
          rw [kWalk_zero_shift, show n + 1 + (N - (n + 1) + 1) = N + 1 by omega]
        rw [hW]
        have hexp : Complex.exp (s * (kWalk 0 β a g (N + 1) : ℂ)) =
            Complex.exp (s * ((kWalk 0 β a g (n + 1) - 0 : ℝ) : ℂ)) *
              Complex.exp (s * ((kWalk 0 β a g (N + 1) - kWalk 0 β a g (n + 1) : ℝ) : ℂ)) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [hexp]
        by_cases hc : cepsDrawupCross β a l g N
        · rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | cepsDrawupCross β a l g N} from hc),
            indicator_of_mem (show WienerHopf.shift (n + 1) g ∈
              {g : ℕ → ℝ | cepsDrawupCross β a l g (N - (n + 1))} from hiff.1 hc)]
          ring
        · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | cepsDrawupCross β a l g N} from hc),
            indicator_of_notMem (show WienerHopf.shift (n + 1) g ∉
              {g : ℕ → ℝ | cepsDrawupCross β a l g (N - (n + 1))} from fun h => hc (hiff.2 h))]
          ring
      · rw [indicator_of_notMem hlo]; ring
    rw [mul_comm, mul_add, add_mul, hlow, hhigh, add_zero]
    ring

theorem cepsDrawupTerm_decomp (ν : ProbabilityMeasure ℝ) (β a : ℝ) {l : ℝ} (hl : 0 ≤ l) {s : ℂ}
    (hs : s.re = 0) (N : ℕ) :
    cepsDrawupTerm ν β a l s N = cepsStripExitTerm ν β a l 0 (Ioi l) s N +
      ∑ n ∈ Finset.range N,
        cepsStripExitTerm ν β a l 0 (Iio 0) s n * cepsDrawupTerm ν β a l s (N - (n + 1)) := by
  have hpre : ∀ n, Measurable fun g : ℕ → ℝ => (krAlive (Icc 0 l) β a n 0 g : ℂ) *
      (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk 0 β a g (n + 1)) *
      Complex.exp (s * ((kWalk 0 β a g (n + 1) - 0 : ℝ) : ℂ)) := fun n =>
    measurable_cepsStripExit_integrand β a l 0 measurableSet_Iio s n
  have hterm : ∀ n ∈ Finset.range N, Integrable (fun g : ℕ → ℝ =>
      ((krAlive (Icc 0 l) β a n 0 g : ℂ) * (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk 0 β a g (n + 1)) *
        Complex.exp (s * ((kWalk 0 β a g (n + 1) - 0 : ℝ) : ℂ))) *
        cepsDrawupIntegrand β a l s (N - (n + 1)) (WienerHopf.shift (n + 1) g)) (iidLaw ν) := by
    intro n _
    have hm := (hpre n).mul ((measurable_cepsDrawupIntegrand β a l s (N - (n + 1))).comp
      (WienerHopf.measurable_shift (n + 1)))
    refine integrable_of_norm_le_one hm fun g => ?_
    rw [norm_mul]
    calc _ ≤ 1 * 1 := mul_le_mul (norm_cepsStripExit_integrand_le β a l 0 (Iio 0) hs n g)
          (norm_cepsDrawupIntegrand_le β a l hs _ _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  change ∫ g, cepsDrawupIntegrand β a l s N g ∂(iidLaw ν) = _
  rw [integral_congr_ae (Eventually.of_forall fun g => cepsDrawupIntegrand_pathwise hl s N g),
    integral_add (integrable_of_norm_le_one
      (measurable_cepsStripExit_integrand β a l 0 measurableSet_Ioi s N)
      (norm_cepsStripExit_integrand_le β a l 0 _ hs N)) (integrable_finsetSum _ hterm),
    integral_finsetSum _ hterm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  have hFd : WienerHopf.DependsOnPrefix (n + 1) fun g : ℕ → ℝ =>
      (krAlive (Icc 0 l) β a n 0 g : ℂ) * (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk 0 β a g (n + 1)) *
        Complex.exp (s * ((kWalk 0 β a g (n + 1) - 0 : ℝ) : ℂ)) := by
    intro ω ω' h
    simp only
    rw [krAlive_congr fun i hi => h i (by omega), surv_kWalk_congr h]
  change ∫ g, _ ∂(WienerHopf.pathLaw (ν : Measure ℝ)) = _
  rw [WienerHopf.integral_mul_shift (ρ := (ν : Measure ℝ)) (hpre n) hFd
    (measurable_cepsDrawupIntegrand β a l s (N - (n + 1)))]
  rfl

/-- **S-2 (d): the drawup cycle identity** (3.8). With the bottom-started exit transforms
`u` (upward) and `ℓ` (downward, a new minimum), `G · (1 - ℓ) = u` for the drawup transform `G`. -/
theorem cepsDrawup_cycle (ν : ProbabilityMeasure ℝ) (β a : ℝ) {l : ℝ} (hl : 0 ≤ l) {s q : ℂ}
    (hs : s.re = 0) (hq : 0 ≤ q.re) :
    cepsDrawup ν β a l s q * (1 - cepsStripExit ν β a l 0 (Iio 0) s q) =
      cepsStripExit ν β a l 0 (Ioi l) s q := by
  set A : ℕ → ℂ := fun n => Complex.exp (-q * ((n : ℂ) + 1)) * cepsStripExitTerm ν β a l 0 (Iio 0) s n
    with hA
  set B : ℕ → ℂ := fun m => Complex.exp (-q * ((m : ℂ) + 1)) * cepsDrawupTerm ν β a l s m with hB
  have hexitS : ∀ E : Set ℝ, MeasurableSet E → Disjoint (Icc 0 l) E → Summable fun n : ℕ =>
      ‖Complex.exp (-q * ((n : ℂ) + 1)) * cepsStripExitTerm ν β a l 0 E s n‖ := by
    intro E hE hJE
    refine (summable_cepsExitProb ν measurableSet_Icc hE hJE β a 0).1.of_nonneg_of_le
      (fun n => norm_nonneg _) fun n => ?_
    rw [norm_mul]
    calc _ ≤ 1 * cepsExitProb ν (Icc 0 l) β a 0 E n :=
          mul_le_mul (norm_cexp_neg_mul_succ_le_one hq n)
            (norm_integral_exit_le ν measurableSet_Icc hE β a 0 n fun _ => norm_cexp_mark_le hs _)
            (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hAs : Summable fun n => ‖A n‖ := hexitS _ measurableSet_Iio (disjoint_Icc_Iio l)
  have hBs : Summable fun m => ‖B m‖ := summable_cepsDrawup ν β a l hs hq
  have hHs := (hexitS _ measurableSet_Ioi (disjoint_Icc_Ioi l)).of_norm
  set e : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N, A n * B (N - (n + 1)) with he
  have hterm : ∀ N : ℕ, Complex.exp (-q * ((N : ℂ) + 1)) * cepsDrawupTerm ν β a l s N =
      Complex.exp (-q * ((N : ℂ) + 1)) * cepsStripExitTerm ν β a l 0 (Ioi l) s N + e N := by
    intro N
    rw [cepsDrawupTerm_decomp ν β a hl hs N, mul_add, Finset.mul_sum, he]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnN := Finset.mem_range.1 hn
    simp only [hA, hB]
    have hexp : Complex.exp (-q * ((N : ℂ) + 1)) = Complex.exp (-q * ((n : ℂ) + 1)) *
        Complex.exp (-q * (((N - (n + 1) : ℕ) : ℂ) + 1)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [Nat.cast_sub (by omega : n + 1 ≤ N)]
      push_cast
      ring
    rw [hexp]
    ring
  have heS : Summable e := by
    have : e = fun N : ℕ => Complex.exp (-q * ((N : ℂ) + 1)) * cepsDrawupTerm ν β a l s N -
        Complex.exp (-q * ((N : ℂ) + 1)) * cepsStripExitTerm ν β a l 0 (Ioi l) s N := by
      funext N; rw [hterm N]; ring
    rw [this]
    exact hBs.of_norm.sub hHs
  have hesum : ∑' N, e N = (∑' n, A n) * ∑' m, B m := by
    rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).2 heS),
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hAs hBs]
    have he0 : e 0 = 0 := by simp [he]
    rw [he0, zero_add]
    congr 1
    funext K
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, he]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 2
    omega
  have hG : cepsDrawup ν β a l s q = cepsStripExit ν β a l 0 (Ioi l) s q +
      cepsStripExit ν β a l 0 (Iio 0) s q * cepsDrawup ν β a l s q := by
    have h1 : cepsDrawup ν β a l s q = ∑' N : ℕ, (Complex.exp (-q * ((N : ℂ) + 1)) *
        cepsStripExitTerm ν β a l 0 (Ioi l) s N + e N) := tsum_congr hterm
    conv_lhs => rw [h1]
    rw [hHs.tsum_add heS, hesum]
    rfl
  linear_combination hG

/-- The drawup cycle identity solved: `G = u / (1 - ℓ)` when `ℓ ≠ 1`. -/
theorem cepsDrawup_eq_div (ν : ProbabilityMeasure ℝ) (β a : ℝ) {l : ℝ} (hl : 0 ≤ l) {s q : ℂ}
    (hs : s.re = 0) (hq : 0 ≤ q.re) (hℓ : cepsStripExit ν β a l 0 (Iio 0) s q ≠ 1) :
    cepsDrawup ν β a l s q =
      cepsStripExit ν β a l 0 (Ioi l) s q / (1 - cepsStripExit ν β a l 0 (Iio 0) s q) := by
  rw [eq_div_iff (sub_ne_zero.2 (Ne.symm hℓ)), cepsDrawup_cycle ν β a hl hs hq]

/-- For the `Y_δ`-walk `W_n = n(1+δ) - S_n` the drawup mark at `q = t(1+δ)`, `s = t` is
`e^{-t S_{τ_l}}`. -/
theorem cepsDrawupTerm_gapKeys (ν : ProbabilityMeasure ℝ) (δ l : ℝ) (t : ℂ) (N : ℕ) :
    Complex.exp (-(t * ((1 + δ : ℝ) : ℂ)) * ((N : ℂ) + 1)) * cepsDrawupTerm ν (1 + δ) 1 l t N =
      ∫ g, {g : ℕ → ℝ | cepsDrawupCross (1 + δ) 1 l g N}.indicator (fun _ => (1 : ℂ)) g *
        Complex.exp (-t * (gapKeys g (N + 1) : ℂ)) ∂(iidLaw ν) := by
  unfold cepsDrawupTerm
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  unfold kWalk
  push_cast
  ring

end

end PGM
