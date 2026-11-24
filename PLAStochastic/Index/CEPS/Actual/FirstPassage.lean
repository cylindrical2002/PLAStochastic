import PLAStochastic.Index.CEPS.Actual.Strip

/-!
# P-CEPS WP8: the exact two-first-passage decomposition (S-2 (b))

`research/2026-10-02-lean-ceps/blueprint-CS.md` lemma S-2 (b); source (L7)–(L8) of
`pgm-analysis/research/2026-09-28-gep-expansion/linear-coefficient-attack.md` §2.2.

For the walk `W_n = kWalk x β a g n` (step `β - aX`) let

`cepsPassBelow ν β a x s q = ∑ₙ e^{-q(n+1)} E[e^{s(W_{n+1} - x)}; W_0, …, W_n ≥ 0, W_{n+1} < 0]`

be the transform of the first passage below `0` (mark relative to the start). Started in the band
`[0, l]`, the walk either leaves it downward first (the low exit transform of `Strip`) or upward,
after which it restarts at the exit point `W_{τ}` and must still pass below `0`:

`cepsPassBelow y = u_low(y) + ∑ₙ e^{-q(n+1)} E[e^{s(W_{n+1} - y)} cepsPassBelow(W_{n+1}); alive to n, W_{n+1} > l]`

(`cepsPassBelow_decomp`); nothing is approximated. The first passage above `l` is the reflected
transform (`cepsPassAbove`), with the mirror decomposition `cepsPassAbove_decomp`. No density is
needed: all series are dominated by probabilities of disjoint exit events.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

/-! ## Exit events are disjoint -/

theorem krAlive_mul_exit_le {J E : Set ℝ} (hJE : Disjoint J E) (β a y : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    krAlive J β a n y g * E.indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) ≤
      krAlive J β a n y g - krAlive J β a (n + 1) y g := by
  rw [krAlive_succ_last]
  have h : J.indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) +
      E.indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) ≤ 1 := by
    by_cases hJ : kWalk y β a g (n + 1) ∈ J
    · have hE : kWalk y β a g (n + 1) ∉ E := fun hE => Set.disjoint_left.1 hJE hJ hE
      simp [hJ, hE]
    · by_cases hE : kWalk y β a g (n + 1) ∈ E <;> simp [hJ, hE]
  have h0 := krAlive_nonneg (J := J) (β := β) (a := a) n y g
  nlinarith

theorem sum_krAlive_exit_le {J E : Set ℝ} (hJE : Disjoint J E) (β a y : ℝ) (K : ℕ)
    (g : ℕ → ℝ) :
    ∑ n ∈ Finset.range K,
      krAlive J β a n y g * E.indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) ≤ 1 := by
  calc _ ≤ ∑ n ∈ Finset.range K, (krAlive J β a n y g - krAlive J β a (n + 1) y g) :=
        Finset.sum_le_sum fun n _ => krAlive_mul_exit_le hJE β a y n g
    _ = krAlive J β a 0 y g - krAlive J β a K y g := Finset.sum_range_sub' _ _
    _ ≤ 1 := by linarith [krAlive_le_one (J := J) (β := β) (a := a) 0 y g,
        krAlive_nonneg (J := J) (β := β) (a := a) K y g]

/-- The probability of exiting `J` through `E` at time `n + 1`. -/
def cepsExitProb (ν : ProbabilityMeasure ℝ) (J : Set ℝ) (β a y : ℝ) (E : Set ℝ) (n : ℕ) : ℝ :=
  ∫ g, krAlive J β a n y g * E.indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) ∂(iidLaw ν)

theorem measurable_krAlive_exit {J E : Set ℝ} (hJ : MeasurableSet J) (hE : MeasurableSet E)
    (β a : ℝ) (n : ℕ) :
    Measurable fun p : ℝ × (ℕ → ℝ) =>
      krAlive J β a n p.1 p.2 * E.indicator (fun _ => (1 : ℝ)) (kWalk p.1 β a p.2 (n + 1)) :=
  (measurable_krAlive_prod hJ β a n).mul
    ((measurable_const.indicator hE).comp (measurable_kWalk_prod β a (n + 1)))

theorem krAlive_exit_nonneg (J E : Set ℝ) (β a y : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    0 ≤ krAlive J β a n y g * E.indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) :=
  mul_nonneg (krAlive_nonneg _ _ _) (indicator_nonneg (fun _ _ => zero_le_one) _)

theorem krAlive_exit_le_one (J E : Set ℝ) (β a y : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    krAlive J β a n y g * E.indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) ≤ 1 := by
  have h1 := krAlive_le_one (J := J) (β := β) (a := a) n y g
  have h2 : E.indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) ≤ 1 := by
    by_cases h : kWalk y β a g (n + 1) ∈ E <;> simp [h]
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (indicator_nonneg (fun _ _ => zero_le_one) _) zero_le_one
    _ = 1 := one_mul 1

theorem integrable_krAlive_exit (ν : ProbabilityMeasure ℝ) {J E : Set ℝ} (hJ : MeasurableSet J)
    (hE : MeasurableSet E) (β a y : ℝ) (n : ℕ) :
    Integrable (fun g => krAlive J β a n y g *
      E.indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1))) (iidLaw ν) :=
  kr_integrable_of_bdd ((measurable_krAlive_exit hJ hE β a n).comp
    (measurable_const.prodMk measurable_id)) (M := 1) fun g => by
      rw [abs_of_nonneg (krAlive_exit_nonneg J E β a y n g)]
      exact krAlive_exit_le_one J E β a y n g

theorem cepsExitProb_nonneg (ν : ProbabilityMeasure ℝ) (J E : Set ℝ) (β a y : ℝ) (n : ℕ) :
    0 ≤ cepsExitProb ν J β a y E n :=
  integral_nonneg fun g => krAlive_exit_nonneg J E β a y n g

theorem sum_cepsExitProb_le (ν : ProbabilityMeasure ℝ) {J E : Set ℝ} (hJ : MeasurableSet J)
    (hE : MeasurableSet E) (hJE : Disjoint J E) (β a y : ℝ) (K : ℕ) :
    ∑ n ∈ Finset.range K, cepsExitProb ν J β a y E n ≤ 1 := by
  unfold cepsExitProb
  rw [← integral_finsetSum _ fun n _ => integrable_krAlive_exit ν hJ hE β a y n]
  exact (integral_mono (integrable_finsetSum _ fun n _ => integrable_krAlive_exit ν hJ hE β a y n)
    (integrable_const 1) fun g => sum_krAlive_exit_le hJE β a y K g).trans (by simp)

theorem summable_cepsExitProb (ν : ProbabilityMeasure ℝ) {J E : Set ℝ} (hJ : MeasurableSet J)
    (hE : MeasurableSet E) (hJE : Disjoint J E) (β a y : ℝ) :
    Summable (cepsExitProb ν J β a y E) ∧ ∑' n, cepsExitProb ν J β a y E n ≤ 1 := by
  have hs : Summable (cepsExitProb ν J β a y E) :=
    summable_of_sum_range_le (fun n => cepsExitProb_nonneg ν J E β a y n)
      (sum_cepsExitProb_le ν hJ hE hJE β a y)
  exact ⟨hs, hs.tsum_le_of_sum_range_le (sum_cepsExitProb_le ν hJ hE hJE β a y)⟩

theorem measurable_cepsExitProb (ν : ProbabilityMeasure ℝ) {J E : Set ℝ} (hJ : MeasurableSet J)
    (hE : MeasurableSet E) (β a : ℝ) (n : ℕ) :
    Measurable fun x => cepsExitProb ν J β a x E n :=
  ((measurable_krAlive_exit hJ hE β a n).stronglyMeasurable.integral_prod_right'
    (ν := iidLaw ν)).measurable

/-- A complex exit term with a mark of modulus one is bounded by the exit probability. -/
theorem norm_integral_exit_le (ν : ProbabilityMeasure ℝ) {J E : Set ℝ} (hJ : MeasurableSet J)
    (hE : MeasurableSet E) (β a y : ℝ) (n : ℕ) {Φ : (ℕ → ℝ) → ℂ} (hΦ : ∀ g, ‖Φ g‖ ≤ 1) :
    ‖∫ g, (krAlive J β a n y g : ℂ) * E.indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) * Φ g
      ∂(iidLaw ν)‖ ≤ cepsExitProb ν J β a y E n := by
  refine norm_integral_le_of_norm_le (integrable_krAlive_exit ν hJ hE β a y n)
    (Eventually.of_forall fun g => ?_)
  rw [indicator_one_ofReal, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (krAlive_nonneg _ _ _),
    abs_of_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)]
  calc _ ≤ krAlive J β a n y g * E.indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) * 1 :=
        mul_le_mul_of_nonneg_left (hΦ g) (krAlive_exit_nonneg J E β a y n g)
    _ = _ := mul_one _

/-! ## First-passage transforms -/

/-- `E[e^{s(W_{n+1} - x)}; W_0, …, W_n ≥ 0, W_{n+1} < 0]` for the walk from `x`. -/
def cepsPassBelowTerm (ν : ProbabilityMeasure ℝ) (β a x : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  ∫ g, (krAlive (Ici 0) β a n x g : ℂ) * (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk x β a g (n + 1)) *
    Complex.exp (s * ((kWalk x β a g (n + 1) - x : ℝ) : ℂ)) ∂(iidLaw ν)

/-- The first-passage-below transform `E[e^{-qσ} e^{s(W_σ - x)}; σ < ∞]`,
`σ = inf {n ≥ 1 : W_n < 0}`, as a series over `σ = n + 1`. -/
def cepsPassBelow (ν : ProbabilityMeasure ℝ) (β a x : ℝ) (s q : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-q * ((n : ℂ) + 1)) * cepsPassBelowTerm ν β a x s n

/-- The first-passage-above-`l` transform: the passage below `0` of the reflected walk
`l - W` with the reflected mark. -/
def cepsPassAbove (ν : ProbabilityMeasure ℝ) (β a l x : ℝ) (s q : ℂ) : ℂ :=
  cepsPassBelow ν (-β) (-a) (l - x) (-s) q

theorem disjoint_Ici_Iio : Disjoint (Ici (0 : ℝ)) (Iio 0) := by
  rw [Set.disjoint_left]; intro x h1 h2; simp at h1 h2; linarith

theorem disjoint_Icc_Iio (l : ℝ) : Disjoint (Icc (0 : ℝ) l) (Iio 0) := by
  rw [Set.disjoint_left]; intro x h1 h2; simp at h2; linarith [h1.1]

theorem disjoint_Icc_Ioi (l : ℝ) : Disjoint (Icc (0 : ℝ) l) (Ioi l) := by
  rw [Set.disjoint_left]; intro x h1 h2; simp at h2; linarith [h1.2]

theorem norm_cexp_mark_le {s : ℂ} (hs : s.re = 0) (x : ℝ) : ‖Complex.exp (s * (x : ℂ))‖ ≤ 1 :=
  (norm_cexp_mul_ofReal_of_re_eq_zero hs x).le

theorem norm_cepsPassBelowTerm_le (ν : ProbabilityMeasure ℝ) (β a x : ℝ) {s : ℂ} (hs : s.re = 0)
    (n : ℕ) : ‖cepsPassBelowTerm ν β a x s n‖ ≤ cepsExitProb ν (Ici 0) β a x (Iio 0) n :=
  norm_integral_exit_le ν measurableSet_Ici measurableSet_Iio β a x n fun _ =>
    norm_cexp_mark_le hs _

theorem summable_cepsPassBelow (ν : ProbabilityMeasure ℝ) (β a x : ℝ) {s q : ℂ} (hs : s.re = 0)
    (hq : 0 ≤ q.re) :
    Summable fun n : ℕ => ‖Complex.exp (-q * ((n : ℂ) + 1)) * cepsPassBelowTerm ν β a x s n‖ := by
  refine (summable_cepsExitProb ν measurableSet_Ici measurableSet_Iio disjoint_Ici_Iio β a x).1
    |>.of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_
  rw [norm_mul]
  calc _ ≤ 1 * cepsExitProb ν (Ici 0) β a x (Iio 0) n :=
        mul_le_mul (norm_cexp_neg_mul_succ_le_one hq n) (norm_cepsPassBelowTerm_le ν β a x hs n)
          (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem norm_cepsPassBelow_le_one (ν : ProbabilityMeasure ℝ) (β a x : ℝ) {s q : ℂ}
    (hs : s.re = 0) (hq : 0 ≤ q.re) : ‖cepsPassBelow ν β a x s q‖ ≤ 1 := by
  obtain ⟨hP, hP1⟩ := summable_cepsExitProb ν measurableSet_Ici measurableSet_Iio
    disjoint_Ici_Iio β a x
  refine (norm_tsum_le_tsum_norm (summable_cepsPassBelow ν β a x hs hq)).trans
    ((Summable.tsum_le_tsum (fun n => ?_) (summable_cepsPassBelow ν β a x hs hq) hP).trans hP1)
  rw [norm_mul]
  calc _ ≤ 1 * cepsExitProb ν (Ici 0) β a x (Iio 0) n :=
        mul_le_mul (norm_cexp_neg_mul_succ_le_one hq n) (norm_cepsPassBelowTerm_le ν β a x hs n)
          (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem measurable_cepsPassBelowTerm (ν : ProbabilityMeasure ℝ) (β a : ℝ) (s : ℂ) (n : ℕ) :
    Measurable fun x => cepsPassBelowTerm ν β a x s n := by
  have h : Measurable fun p : ℝ × (ℕ → ℝ) =>
      (krAlive (Ici 0) β a n p.1 p.2 : ℂ) *
        (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk p.1 β a p.2 (n + 1)) *
        Complex.exp (s * ((kWalk p.1 β a p.2 (n + 1) - p.1 : ℝ) : ℂ)) :=
    ((Complex.measurable_ofReal.comp (measurable_krAlive_prod measurableSet_Ici β a n)).mul
      ((measurable_const.indicator measurableSet_Iio).comp (measurable_kWalk_prod β a (n + 1)))).mul
      (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        ((measurable_kWalk_prod β a (n + 1)).sub measurable_fst))))
  exact (h.stronglyMeasurable.integral_prod_right' (ν := iidLaw ν)).measurable

/-! ## Markov splitting at a fixed time with a prefix-dependent start -/

/-- **Markov property at time `k`**: for a prefix functional `F`, a prefix position `W` and a jointly
measurable bounded `G`, `E[F · G(W, θ_k)] = E[F · ∫ G(W, ·)]`. -/
theorem integral_mul_shift_dep (ν : ProbabilityMeasure ℝ) (k : ℕ) {F : (ℕ → ℝ) → ℂ}
    (hF : Measurable F) (hFd : ∀ g g' : ℕ → ℝ, (∀ i < k, g i = g' i) → F g = F g')
    {W : (ℕ → ℝ) → ℝ} (hW : Measurable W) (hWd : ∀ g g' : ℕ → ℝ, (∀ i < k, g i = g' i) → W g = W g')
    {G : ℝ → (ℕ → ℝ) → ℂ} (hG : Measurable (Function.uncurry G)) (hFb : ∀ g, ‖F g‖ ≤ 1)
    (hGb : ∀ x h, ‖G x h‖ ≤ 1) :
    ∫ g, F g * G (W g) (fun i => g (i + k)) ∂(iidLaw ν) =
      ∫ g, F g * ∫ h, G (W g) h ∂(iidLaw ν) ∂(iidLaw ν) := by
  have hsh : Measurable fun g : ℕ → ℝ => fun i => g (i + k) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (i + k)
  have hH : Measurable fun g : ℕ → ℝ => F g * G (W g) (fun i => g (i + k)) :=
    hF.mul (hG.comp (hW.prodMk hsh))
  have hHb : ∀ g : ℕ → ℝ, ‖F g * G (W g) (fun i => g (i + k))‖ ≤ 1 := fun g => by
    rw [norm_mul]
    calc _ ≤ 1 * 1 := mul_le_mul (hFb g) (hGb _ _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hcat := surv_integral_cat ν ν ∅ k hH hHb
  simp only [wordLaw_self] at hcat
  rw [hcat]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have hagree : ∀ h : ℕ → ℝ, ∀ i < k, surv_cat k g h i = g i := fun h i hi =>
    surv_cat_apply_lt hi g h
  have hrest : ∀ h : ℕ → ℝ, (fun i => surv_cat k g h (i + k)) = h := fun h => funext fun i => by
    rw [add_comm]; exact surv_cat_apply_add k i g h
  simp only
  simp_rw [hFd _ g (hagree _), hWd _ g (hagree _), hrest]
  rw [integral_const_mul]

/-! ## The pathwise first-exit identity -/

theorem kWalk_shift (y β a : ℝ) (g : ℕ → ℝ) (k m : ℕ) :
    kWalk (kWalk y β a g k) β a (fun i => g (i + k)) m = kWalk y β a g (k + m) :=
  (kWalk_add y β a g k m).symm

/-- **First exit of `[0, l]` before passing below `0`.** Staying `≥ 0` up to `N` means staying in
`[0, l]` up to `N`, or leaving `[0, l]` upward at a first time `n + 1 ≤ N` and staying `≥ 0` afterwards. -/
theorem krAlive_Ici_first_exit {l : ℝ} (β a : ℝ) {y : ℝ} (hy : y ∈ Icc 0 l) (g : ℕ → ℝ) (N : ℕ) :
    krAlive (Ici 0) β a N y g = krAlive (Icc 0 l) β a N y g +
      ∑ n ∈ Finset.range N, krAlive (Icc 0 l) β a n y g *
        (Ioi l).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) *
        krAlive (Ici 0) β a (N - (n + 1)) (kWalk y β a g (n + 1)) (fun i => g (i + (n + 1))) := by
  have hl : 0 ≤ l := hy.1.trans hy.2
  induction N with
  | zero =>
    simp only [krAlive_zero, Finset.range_zero, Finset.sum_empty, add_zero]
    rw [indicator_of_mem (show y ∈ Ici 0 from hy.1), indicator_of_mem hy]
  | succ N ih =>
    rw [krAlive_succ_last, ih, Finset.sum_range_succ, krAlive_succ_last (J := Icc 0 l)]
    have hsplit : (Ici 0).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (N + 1)) =
        (Icc 0 l).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (N + 1)) +
          (Ioi l).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (N + 1)) := by
      set x := kWalk y β a g (N + 1)
      rcases lt_or_ge x 0 with h0 | h0
      · rw [indicator_of_notMem (show x ∉ Ici 0 from fun h => by simp at h; linarith),
          indicator_of_notMem (show x ∉ Icc 0 l from fun h => by linarith [h.1]),
          indicator_of_notMem (show x ∉ Ioi l from fun h => by simp at h; linarith)]
        ring
      rcases le_or_gt x l with h1 | h1
      · rw [indicator_of_mem (show x ∈ Ici 0 from h0), indicator_of_mem (show x ∈ Icc 0 l from
          ⟨h0, h1⟩), indicator_of_notMem (show x ∉ Ioi l from fun h => by simp at h; linarith)]
        ring
      · rw [indicator_of_mem (show x ∈ Ici 0 from h0),
          indicator_of_notMem (show x ∉ Icc 0 l from fun h => by linarith [h.2]),
          indicator_of_mem (show x ∈ Ioi l from h1)]
        ring
    have hlast : (Ioi l).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (N + 1)) *
        krAlive (Ici 0) β a (N + 1 - (N + 1)) (kWalk y β a g (N + 1))
          (fun i => g (i + (N + 1))) =
        (Ioi l).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (N + 1)) := by
      rw [Nat.sub_self, krAlive_zero]
      by_cases h : kWalk y β a g (N + 1) ∈ Ioi l
      · rw [indicator_of_mem h, indicator_of_mem (show kWalk y β a g (N + 1) ∈ Ici 0 from
          le_of_lt (lt_of_le_of_lt hl h)), mul_one]
      · rw [indicator_of_notMem h, zero_mul]
    have hmid : ∀ n ∈ Finset.range N,
        krAlive (Ici 0) β a (N - (n + 1)) (kWalk y β a g (n + 1)) (fun i => g (i + (n + 1))) *
          (Ici 0).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (N + 1)) =
        krAlive (Ici 0) β a (N + 1 - (n + 1)) (kWalk y β a g (n + 1)) (fun i => g (i + (n + 1))) := by
      intro n hn
      have hnN := Finset.mem_range.1 hn
      have e : N + 1 - (n + 1) = (N - (n + 1)) + 1 := by omega
      rw [e, krAlive_succ_last, kWalk_shift]
      congr 3
      omega
    rw [add_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun n hn => by
      rw [mul_assoc, hmid n hn]]
    rw [hsplit, mul_add, mul_assoc (krAlive (Icc 0 l) β a N y g) _ _, hlast]
    ring

/-! ## The decomposition of each passage time -/

/-- The integrand of `cepsPassBelowTerm` from the start `x`. -/
def cepsPassBelowIntegrand (β a : ℝ) (s : ℂ) (m : ℕ) (x : ℝ) (h : ℕ → ℝ) : ℂ :=
  (krAlive (Ici 0) β a m x h : ℂ) * (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk x β a h (m + 1)) *
    Complex.exp (s * ((kWalk x β a h (m + 1) - x : ℝ) : ℂ))

/-- The prefix up to an upward exit of `[0, l]` at time `n + 1`, with its mark. -/
def cepsHighPre (β a l y : ℝ) (s : ℂ) (n : ℕ) (g : ℕ → ℝ) : ℂ :=
  (krAlive (Icc 0 l) β a n y g : ℂ) * (Ioi l).indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) *
    Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ))

/-- `E[e^{s(W_{n+1} - y)} P_m(W_{n+1}); alive in [0, l] up to n, W_{n+1} > l]`, `P_m` the `m`-th
passage-below term from the exit point. -/
def cepsHighThen (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (s : ℂ) (n m : ℕ) : ℂ :=
  ∫ g, cepsHighPre β a l y s n g * cepsPassBelowTerm ν β a (kWalk y β a g (n + 1)) s m ∂(iidLaw ν)

theorem measurable_cepsPassBelowIntegrand (β a : ℝ) (s : ℂ) (m : ℕ) :
    Measurable (Function.uncurry (cepsPassBelowIntegrand β a s m)) :=
  ((Complex.measurable_ofReal.comp (measurable_krAlive_prod measurableSet_Ici β a m)).mul
    ((measurable_const.indicator measurableSet_Iio).comp (measurable_kWalk_prod β a (m + 1)))).mul
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_kWalk_prod β a (m + 1)).sub measurable_fst))))

theorem norm_cepsPassBelowIntegrand_le (β a : ℝ) {s : ℂ} (hs : s.re = 0) (m : ℕ) (x : ℝ)
    (h : ℕ → ℝ) : ‖cepsPassBelowIntegrand β a s m x h‖ ≤ 1 := by
  have := norm_cepsStripExit_integrand_le β a 0 x (Iio 0) hs m h
  unfold cepsPassBelowIntegrand
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (krAlive_nonneg _ _ _),
    norm_cexp_mul_ofReal_of_re_eq_zero hs, mul_one]
  have h2 : ‖(Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk x β a h (m + 1))‖ ≤ 1 := by
    by_cases hh : kWalk x β a h (m + 1) ∈ Iio 0 <;> simp [hh]
  calc _ ≤ 1 * 1 := mul_le_mul (krAlive_le_one _ _ _) h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem measurable_cepsHighPre (β a l y : ℝ) (s : ℂ) (n : ℕ) :
    Measurable (cepsHighPre β a l y s n) :=
  measurable_cepsStripExit_integrand β a l y measurableSet_Ioi s n

theorem norm_cepsHighPre_le (β a l y : ℝ) {s : ℂ} (hs : s.re = 0) (n : ℕ) (g : ℕ → ℝ) :
    ‖cepsHighPre β a l y s n g‖ ≤ 1 :=
  norm_cepsStripExit_integrand_le β a l y (Ioi l) hs n g

theorem cepsPassBelowIntegrand_pathwise (β a : ℝ) {l y : ℝ} (hy : y ∈ Icc 0 l) (s : ℂ)
    (N : ℕ) (g : ℕ → ℝ) :
    cepsPassBelowIntegrand β a s N y g =
      (krAlive (Icc 0 l) β a N y g : ℂ) * (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk y β a g (N + 1)) *
        Complex.exp (s * ((kWalk y β a g (N + 1) - y : ℝ) : ℂ)) +
      ∑ n ∈ Finset.range N, cepsHighPre β a l y s n g *
        cepsPassBelowIntegrand β a s (N - (n + 1)) (kWalk y β a g (n + 1))
          (fun i => g (i + (n + 1))) := by
  unfold cepsPassBelowIntegrand cepsHighPre
  rw [krAlive_Ici_first_exit β a hy g N]
  simp only [Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnN := Finset.mem_range.1 hn
  have hw : kWalk (kWalk y β a g (n + 1)) β a (fun i => g (i + (n + 1))) (N - (n + 1) + 1) =
      kWalk y β a g (N + 1) := by
    rw [kWalk_shift]
    congr 1
    omega
  rw [hw, indicator_one_ofReal (Ioi l)]
  have hm : Complex.exp (s * ((kWalk y β a g (N + 1) - y : ℝ) : ℂ)) =
      Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ)) *
        Complex.exp (s * ((kWalk y β a g (N + 1) - kWalk y β a g (n + 1) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hm]
  ring

theorem cepsPassBelowTerm_eq_integral (ν : ProbabilityMeasure ℝ) (β a x : ℝ) (s : ℂ) (m : ℕ) :
    cepsPassBelowTerm ν β a x s m = ∫ h, cepsPassBelowIntegrand β a s m x h ∂(iidLaw ν) := rfl

theorem measurable_cepsHighPre_mul_pass (β a l y : ℝ) (s : ℂ) (n m : ℕ) :
    Measurable fun g : ℕ → ℝ => cepsHighPre β a l y s n g *
      cepsPassBelowIntegrand β a s m (kWalk y β a g (n + 1)) (fun i => g (i + (n + 1))) := by
  have h1 := measurable_cepsHighPre β a l y s n
  have h2 := (measurable_cepsPassBelowIntegrand β a s m).comp
    ((measurable_kWalk_right y β a (n + 1)).prodMk
      (measurable_pi_lambda _ fun i => measurable_pi_apply (i + (n + 1))))
  exact h1.mul h2

theorem cepsPassBelowTerm_decomp (ν : ProbabilityMeasure ℝ) (β a : ℝ) {l y : ℝ}
    (hy : y ∈ Icc 0 l) {s : ℂ} (hs : s.re = 0) (N : ℕ) :
    cepsPassBelowTerm ν β a y s N = cepsStripExitTerm ν β a l y (Iio 0) s N +
      ∑ n ∈ Finset.range N, cepsHighThen ν β a l y s n (N - (n + 1)) := by
  have hterm : ∀ n ∈ Finset.range N, Integrable (fun g => cepsHighPre β a l y s n g *
      cepsPassBelowIntegrand β a s (N - (n + 1)) (kWalk y β a g (n + 1))
        (fun i => g (i + (n + 1)))) (iidLaw ν) := fun n _ =>
    integrable_of_norm_le_one (measurable_cepsHighPre_mul_pass β a l y s n _) fun g => by
      rw [norm_mul]
      calc _ ≤ 1 * 1 := mul_le_mul (norm_cepsHighPre_le β a l y hs n g)
            (norm_cepsPassBelowIntegrand_le β a hs _ _ _) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  rw [cepsPassBelowTerm_eq_integral, integral_congr_ae (Eventually.of_forall fun g =>
    cepsPassBelowIntegrand_pathwise β a hy s N g)]
  rw [integral_add (integrable_of_norm_le_one
      (measurable_cepsStripExit_integrand β a l y measurableSet_Iio s N)
      (norm_cepsStripExit_integrand_le β a l y _ hs N)) (integrable_finsetSum _ hterm),
    integral_finsetSum _ hterm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold cepsHighThen
  simp_rw [cepsPassBelowTerm_eq_integral]
  rw [integral_mul_shift_dep ν (n + 1) (measurable_cepsHighPre β a l y s n)
    (fun g g' h => by
      unfold cepsHighPre
      rw [krAlive_congr fun i hi => h i (by omega), surv_kWalk_congr h])
    (measurable_kWalk_right y β a (n + 1)) (fun g g' h => surv_kWalk_congr h)
    (measurable_cepsPassBelowIntegrand β a s (N - (n + 1))) (norm_cepsHighPre_le β a l y hs n)
    (norm_cepsPassBelowIntegrand_le β a hs _)]

/-! ## Summing over the passage time -/

theorem tsum_antidiagonal_eq_tsum {c : ℕ × ℕ → ℂ} (hc : Summable c) :
    ∑' K, ∑ p ∈ Finset.antidiagonal K, c p = ∑' p, c p := by
  conv_lhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq c]
  exact ((Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.2 hc).tsum_sigma'
    (fun n => (hasSum_fintype _).summable)).symm

/-- The real high-exit indicator `1{alive in [0, l] up to n, W_{n+1} > l}`. -/
theorem norm_cepsHighPre_le_exit (β a l y : ℝ) {s : ℂ} (hs : s.re = 0) (n : ℕ) (g : ℕ → ℝ) :
    ‖cepsHighPre β a l y s n g‖ ≤
      krAlive (Icc 0 l) β a n y g * (Ioi l).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) := by
  unfold cepsHighPre
  rw [indicator_one_ofReal, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (krAlive_nonneg _ _ _),
    abs_of_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _),
    norm_cexp_mul_ofReal_of_re_eq_zero hs, mul_one]

theorem measurable_highExit_mul_prob (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (n m : ℕ) :
    Measurable fun g : ℕ → ℝ =>
      krAlive (Icc 0 l) β a n y g * (Ioi l).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) *
        cepsExitProb ν (Ici 0) β a (kWalk y β a g (n + 1)) (Iio 0) m :=
  ((measurable_krAlive_exit measurableSet_Icc measurableSet_Ioi β a n).comp
    (measurable_const.prodMk measurable_id)).mul
    ((measurable_cepsExitProb ν measurableSet_Ici measurableSet_Iio β a m).comp
      (measurable_kWalk_right y β a (n + 1)))

/-- The dominating double family `E[1{high exit at n+1} P(pass below at m+1 from W_{n+1})]`. -/
def cepsHighThenProb (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (p : ℕ × ℕ) : ℝ :=
  ∫ g, krAlive (Icc 0 l) β a p.1 y g * (Ioi l).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (p.1 + 1)) *
    cepsExitProb ν (Ici 0) β a (kWalk y β a g (p.1 + 1)) (Iio 0) p.2 ∂(iidLaw ν)

theorem cepsHighThenProb_nonneg (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (p : ℕ × ℕ) :
    0 ≤ cepsHighThenProb ν β a l y p :=
  integral_nonneg fun _ => mul_nonneg (krAlive_exit_nonneg _ _ _ _ _ _ _)
    (cepsExitProb_nonneg _ _ _ _ _ _ _)

theorem integrable_highExit_mul_prob (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (n m : ℕ) :
    Integrable (fun g : ℕ → ℝ =>
      krAlive (Icc 0 l) β a n y g * (Ioi l).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) *
        cepsExitProb ν (Ici 0) β a (kWalk y β a g (n + 1)) (Iio 0) m) (iidLaw ν) := by
  refine kr_integrable_of_bdd (measurable_highExit_mul_prob ν β a l y n m) (M := 1) fun g => ?_
  have h1 := krAlive_exit_le_one (Icc 0 l) (Ioi l) β a y n g
  have h2 := cepsExitProb_nonneg ν (Ici 0) (Iio 0) β a (kWalk y β a g (n + 1)) m
  have h3 : cepsExitProb ν (Ici 0) β a (kWalk y β a g (n + 1)) (Iio 0) m ≤ 1 := by
    have := sum_cepsExitProb_le ν measurableSet_Ici measurableSet_Iio disjoint_Ici_Iio β a
      (kWalk y β a g (n + 1)) (m + 1)
    rw [Finset.sum_range_succ] at this
    linarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.range m) =>
      cepsExitProb_nonneg ν (Ici 0) (Iio 0) β a (kWalk y β a g (n + 1)) k]
  rw [abs_of_nonneg (mul_nonneg (krAlive_exit_nonneg _ _ _ _ _ _ _) h2)]
  calc _ ≤ 1 * 1 := mul_le_mul h1 h3 h2 zero_le_one
    _ = 1 := one_mul 1

theorem summable_cepsHighThenProb (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) :
    Summable (cepsHighThenProb ν β a l y) := by
  refine summable_of_sum_le (c := 1) (cepsHighThenProb_nonneg ν β a l y) fun u => ?_
  obtain ⟨A, hA⟩ : ∃ A, ∀ p ∈ u, p.1 < A ∧ p.2 < A :=
    ⟨u.sup (fun p => p.1 + p.2) + 1, fun p hp => by
      have := Finset.le_sup (f := fun p : ℕ × ℕ => p.1 + p.2) hp
      constructor <;> omega⟩
  have hsub : u ⊆ Finset.range A ×ˢ Finset.range A := fun p hp => by
    simp only [Finset.mem_product, Finset.mem_range]
    exact hA p hp
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
    cepsHighThenProb_nonneg ν β a l y p).trans ?_
  rw [Finset.sum_product]
  have hrow : ∀ n ∈ Finset.range A, ∑ m ∈ Finset.range A, cepsHighThenProb ν β a l y (n, m) ≤
      cepsExitProb ν (Icc 0 l) β a y (Ioi l) n := by
    intro n _
    simp only [cepsHighThenProb]
    show _ ≤ ∫ g, krAlive (Icc 0 l) β a n y g *
      (Ioi l).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) ∂(iidLaw ν)
    rw [← integral_finsetSum _ fun m _ => integrable_highExit_mul_prob ν β a l y n m]
    refine integral_mono (integrable_finsetSum _ fun m _ => integrable_highExit_mul_prob ν β a l y n m)
      (integrable_krAlive_exit ν measurableSet_Icc measurableSet_Ioi β a y n) fun g => ?_
    simp only
    rw [← Finset.mul_sum]
    calc _ ≤ krAlive (Icc 0 l) β a n y g *
          (Ioi l).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) * 1 :=
          mul_le_mul_of_nonneg_left (sum_cepsExitProb_le ν measurableSet_Ici measurableSet_Iio
            disjoint_Ici_Iio β a _ A) (krAlive_exit_nonneg _ _ _ _ _ _ _)
      _ = _ := mul_one _
  exact (Finset.sum_le_sum hrow).trans (sum_cepsExitProb_le ν measurableSet_Icc measurableSet_Ioi
    (disjoint_Icc_Ioi l) β a y A)

theorem norm_cepsHighThen_le (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) {s : ℂ} (hs : s.re = 0)
    (n m : ℕ) : ‖cepsHighThen ν β a l y s n m‖ ≤ cepsHighThenProb ν β a l y (n, m) := by
  unfold cepsHighThen cepsHighThenProb
  refine norm_integral_le_of_norm_le (integrable_highExit_mul_prob ν β a l y n m)
    (Eventually.of_forall fun g => ?_)
  rw [norm_mul]
  exact mul_le_mul (norm_cepsHighPre_le_exit β a l y hs n g)
    (norm_cepsPassBelowTerm_le ν β a _ hs m) (norm_nonneg _) (krAlive_exit_nonneg _ _ _ _ _ _ _)

/-- **S-2 (b): the exact two-first-passage decomposition** (L7). Started in `[0, l]`, the first
passage below `0` is the low exit of the band, or an upward exit followed by a passage below `0`
from the exit point. -/
theorem cepsPassBelow_decomp (ν : ProbabilityMeasure ℝ) (β a : ℝ) {l y : ℝ} (hy : y ∈ Icc 0 l)
    {s q : ℂ} (hs : s.re = 0) (hq : 0 ≤ q.re) :
    cepsPassBelow ν β a y s q = cepsStripExit ν β a l y (Iio 0) s q +
      ∑' n : ℕ, Complex.exp (-q * ((n : ℂ) + 1)) * ∫ g, cepsHighPre β a l y s n g *
        cepsPassBelow ν β a (kWalk y β a g (n + 1)) s q ∂(iidLaw ν) := by
  set c : ℕ × ℕ → ℂ := fun p => Complex.exp (-q * ((p.1 : ℂ) + 1)) *
    Complex.exp (-q * ((p.2 : ℂ) + 1)) * cepsHighThen ν β a l y s p.1 p.2 with hcdef
  have hc : Summable c := by
    refine (summable_cepsHighThenProb ν β a l y).of_norm_bounded fun p => ?_
    rw [hcdef, norm_mul, norm_mul]
    calc _ ≤ 1 * 1 * cepsHighThenProb ν β a l y (p.1, p.2) :=
          mul_le_mul (mul_le_mul (norm_cexp_neg_mul_succ_le_one hq _)
            (norm_cexp_neg_mul_succ_le_one hq _) (norm_nonneg _) zero_le_one)
            (norm_cepsHighThen_le ν β a l y hs _ _) (norm_nonneg _) (by norm_num)
      _ = cepsHighThenProb ν β a l y p := by simp
  -- the rows
  have hrow : ∀ n : ℕ, ∑' m, c (n, m) = Complex.exp (-q * ((n : ℂ) + 1)) *
      ∫ g, cepsHighPre β a l y s n g * cepsPassBelow ν β a (kWalk y β a g (n + 1)) s q
        ∂(iidLaw ν) := by
    intro n
    have hint : ∫ g, cepsHighPre β a l y s n g * cepsPassBelow ν β a (kWalk y β a g (n + 1)) s q
        ∂(iidLaw ν) = ∑' m : ℕ, Complex.exp (-q * ((m : ℂ) + 1)) * cepsHighThen ν β a l y s n m := by
      have e : ∀ g : ℕ → ℝ, cepsHighPre β a l y s n g *
          cepsPassBelow ν β a (kWalk y β a g (n + 1)) s q =
          ∑' m : ℕ, Complex.exp (-q * ((m : ℂ) + 1)) * (cepsHighPre β a l y s n g *
            cepsPassBelowTerm ν β a (kWalk y β a g (n + 1)) s m) := by
        intro g
        unfold cepsPassBelow
        rw [← tsum_mul_left]
        congr 1
        funext m
        ring
      simp_rw [e]
      have hm1 : ∀ m : ℕ, Measurable fun g : ℕ → ℝ => Complex.exp (-q * ((m : ℂ) + 1)) *
          (cepsHighPre β a l y s n g * cepsPassBelowTerm ν β a (kWalk y β a g (n + 1)) s m) := by
        intro m
        have h1 := measurable_cepsHighPre β a l y s n
        have h2 := (measurable_cepsPassBelowTerm ν β a s m).comp
          (measurable_kWalk_right y β a (n + 1))
        exact (h1.mul h2).const_mul _
      rw [integral_tsum]
      · congr 1
        funext m
        rw [integral_const_mul]
        rfl
      · intro m
        exact (hm1 m).aestronglyMeasurable
      · have hb : ∀ (m : ℕ) (g : ℕ → ℝ), ‖Complex.exp (-q * ((m : ℂ) + 1)) * (cepsHighPre β a l y s n g *
            cepsPassBelowTerm ν β a (kWalk y β a g (n + 1)) s m)‖ ≤
            cepsExitProb ν (Ici 0) β a (kWalk y β a g (n + 1)) (Iio 0) m := by
          intro m g
          rw [norm_mul, norm_mul]
          calc _ ≤ 1 * (1 * cepsExitProb ν (Ici 0) β a (kWalk y β a g (n + 1)) (Iio 0) m) :=
                mul_le_mul (norm_cexp_neg_mul_succ_le_one hq _) (mul_le_mul
                  (norm_cepsHighPre_le β a l y hs n g) (norm_cepsPassBelowTerm_le ν β a _ hs m)
                  (norm_nonneg _) zero_le_one) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                  zero_le_one
            _ = _ := by ring
        refine ne_top_of_le_ne_top (b := ∫⁻ _ : ℕ → ℝ, 1 ∂(iidLaw ν)) (by simp) ?_
        rw [← lintegral_tsum fun m => (hm1 m).enorm.aemeasurable]
        refine lintegral_mono fun g => ?_
        obtain ⟨hP, hP1⟩ := summable_cepsExitProb ν measurableSet_Ici measurableSet_Iio
          disjoint_Ici_Iio β a (kWalk y β a g (n + 1))
        calc ∑' m : ℕ, ‖Complex.exp (-q * ((m : ℂ) + 1)) * (cepsHighPre β a l y s n g *
              cepsPassBelowTerm ν β a (kWalk y β a g (n + 1)) s m)‖ₑ
            ≤ ∑' m : ℕ, ENNReal.ofReal (cepsExitProb ν (Ici 0) β a (kWalk y β a g (n + 1)) (Iio 0) m) :=
              ENNReal.tsum_le_tsum fun m => by
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hb m g)
          _ = ENNReal.ofReal (∑' m : ℕ, cepsExitProb ν (Ici 0) β a (kWalk y β a g (n + 1)) (Iio 0) m) :=
              (ENNReal.ofReal_tsum_of_nonneg (fun m => cepsExitProb_nonneg _ _ _ _ _ _ _) hP).symm
          _ ≤ 1 := ENNReal.ofReal_le_one.2 hP1
    rw [hint, ← tsum_mul_left]
    congr 1
    funext m
    rw [hcdef]
    ring
  -- the passage series term by term
  have hlowS : Summable fun N : ℕ => Complex.exp (-q * ((N : ℂ) + 1)) *
      cepsStripExitTerm ν β a l y (Iio 0) s N := by
    refine Summable.of_norm_bounded
      (summable_cepsExitProb ν measurableSet_Icc measurableSet_Iio (disjoint_Icc_Iio l) β a y).1
      fun N => ?_
    rw [norm_mul]
    calc _ ≤ 1 * cepsExitProb ν (Icc 0 l) β a y (Iio 0) N :=
          mul_le_mul (norm_cexp_neg_mul_succ_le_one hq N)
            (norm_integral_exit_le ν measurableSet_Icc measurableSet_Iio β a y N fun _ =>
              norm_cexp_mark_le hs _) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  set d : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N, c (n, N - (n + 1)) with hd
  have hPN : ∀ N : ℕ, Complex.exp (-q * ((N : ℂ) + 1)) * cepsPassBelowTerm ν β a y s N =
      Complex.exp (-q * ((N : ℂ) + 1)) * cepsStripExitTerm ν β a l y (Iio 0) s N + d N := by
    intro N
    rw [cepsPassBelowTerm_decomp ν β a hy hs N, mul_add, Finset.mul_sum, hd]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnN := Finset.mem_range.1 hn
    rw [hcdef]
    simp only
    have hexp : Complex.exp (-q * ((N : ℂ) + 1)) = Complex.exp (-q * ((n : ℂ) + 1)) *
        Complex.exp (-q * (((N - (n + 1) : ℕ) : ℂ) + 1)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [Nat.cast_sub (by omega : n + 1 ≤ N)]
      push_cast
      ring
    rw [hexp]
  have hdS : Summable d := by
    have h1 := (summable_cepsPassBelow ν β a y hs hq).of_norm
    have : d = fun N : ℕ => Complex.exp (-q * ((N : ℂ) + 1)) * cepsPassBelowTerm ν β a y s N -
        Complex.exp (-q * ((N : ℂ) + 1)) * cepsStripExitTerm ν β a l y (Iio 0) s N := by
      funext N
      rw [hPN N]
      ring
    rw [this]
    exact h1.sub hlowS
  have hdsum : ∑' N, d N = ∑' p, c p := by
    rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).2 hdS)]
    have hd0 : d 0 = 0 := by simp [hd]
    rw [hd0, zero_add, ← tsum_antidiagonal_eq_tsum hc]
    congr 1
    funext K
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hd]
    refine Finset.sum_congr rfl fun n hn => ?_
    congr 2
    omega
  unfold cepsPassBelow
  rw [tsum_congr hPN, hlowS.tsum_add hdS, hdsum, hc.tsum_prod' fun n => hc.prod_factor n]
  unfold cepsStripExit
  congr 1
  exact tsum_congr hrow

/-- The prefix up to a downward exit of `[0, l]` at time `n + 1`, with its mark. -/
def cepsLowPre (β a l y : ℝ) (s : ℂ) (n : ℕ) (g : ℕ → ℝ) : ℂ :=
  (krAlive (Icc 0 l) β a n y g : ℂ) * (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) *
    Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ))

theorem cepsHighPre_reflect (β a l y : ℝ) (s : ℂ) (n : ℕ) (g : ℕ → ℝ) :
    cepsHighPre (-β) (-a) l (l - y) (-s) n g = cepsLowPre β a l y s n g := by
  unfold cepsHighPre cepsLowPre
  rw [krAlive_reflect, kWalk_reflect]
  have hind : (Ioi l).indicator (fun _ => (1 : ℂ)) (l - kWalk y β a g (n + 1)) =
      (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) := by
    by_cases h : kWalk y β a g (n + 1) < 0
    · rw [indicator_of_mem (show l - kWalk y β a g (n + 1) ∈ Ioi l by simp; linarith),
        indicator_of_mem (show kWalk y β a g (n + 1) ∈ Iio 0 from h)]
    · rw [indicator_of_notMem (show l - kWalk y β a g (n + 1) ∉ Ioi l by simp; linarith),
        indicator_of_notMem (show kWalk y β a g (n + 1) ∉ Iio 0 by simpa using h)]
  rw [hind]
  congr 2
  push_cast
  ring

/-- **S-2 (b), mirror form** (L8). Started in `[0, l]`, the first passage above `l` is the high
exit of the band, or a downward exit followed by a passage above `l` from the exit point. -/
theorem cepsPassAbove_decomp (ν : ProbabilityMeasure ℝ) (β a : ℝ) {l y : ℝ} (hy : y ∈ Icc 0 l)
    {s q : ℂ} (hs : s.re = 0) (hq : 0 ≤ q.re) :
    cepsPassAbove ν β a l y s q = cepsStripExit ν β a l y (Ioi l) s q +
      ∑' n : ℕ, Complex.exp (-q * ((n : ℂ) + 1)) * ∫ g, cepsLowPre β a l y s n g *
        cepsPassAbove ν β a l (kWalk y β a g (n + 1)) s q ∂(iidLaw ν) := by
  have hy' : l - y ∈ Icc 0 l := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hs' : (-s).re = 0 := by simp [hs]
  unfold cepsPassAbove
  rw [cepsPassBelow_decomp ν (-β) (-a) hy' hs' hq, cepsStripExit_reflect_low]
  congr 1
  refine tsum_congr fun n => ?_
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [cepsHighPre_reflect, kWalk_reflect]

end

end PGM
