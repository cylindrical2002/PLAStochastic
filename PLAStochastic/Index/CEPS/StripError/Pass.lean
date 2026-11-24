import PLAStochastic.Index.CEPS.Actual.Main

/-!
# WP9: band exits and first passages with an absolute mark

For the walk `V_n = kWalk y β a g n` (step `β - aX`) and a mark `φ` on the final position,

`stripPass ν J E β a y φ q = ∑ₙ e^{-q(n+1)} E[φ(V_{n+1}); V_0, …, V_n ∈ J, V_{n+1} ∈ E]`.

With `J = Icc 0 l` this is a band exit transform (`cepsStripExit` is the case of the relative
exponential mark); with `J = Ici 0`, `E = Iio 0` it is the first passage below `0`.
The two-first-passage decomposition of WP8 (`cepsPassBelow_decomp`) is proved here for an
arbitrary measurable mark bounded by one below `0`: started in `[0, l]`, the passage below `0`
is the low exit of the band, or an upward exit followed by the passage below `0` from the exit
point. With an absolute mark the complex marks `e^{-tV}` with `Re t ≤ 0` remain bounded, which is
what the strip error analysis needs at the roots `t = β±`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

/-- `E[φ(V_{n+1}); V_0, …, V_n ∈ J, V_{n+1} ∈ E]` for `V = kWalk y β a`. -/
def stripPassTerm (ν : ProbabilityMeasure ℝ) (J E : Set ℝ) (β a y : ℝ) (φ : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ g, (krAlive J β a n y g : ℂ) * E.indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) *
    φ (kWalk y β a g (n + 1)) ∂(iidLaw ν)

/-- `∑ₙ e^{-q(n+1)} E[φ(V_{n+1}); V_0, …, V_n ∈ J, V_{n+1} ∈ E]`. -/
def stripPass (ν : ProbabilityMeasure ℝ) (J E : Set ℝ) (β a y : ℝ) (φ : ℝ → ℂ) (q : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-q * ((n : ℂ) + 1)) * stripPassTerm ν J E β a y φ n

/-- The band exit transform is the absolute-mark exit with the relative exponential mark. -/
theorem cepsStripExit_eq_stripPass (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (E : Set ℝ)
    (s q : ℂ) :
    cepsStripExit ν β a l y E s q =
      stripPass ν (Icc 0 l) E β a y (fun v => Complex.exp (s * ((v - y : ℝ) : ℂ))) q := rfl

/-- At start `0` the relative mark is absolute. -/
theorem cepsStripExit_zero_eq_stripPass (ν : ProbabilityMeasure ℝ) (β a l : ℝ) (E : Set ℝ)
    (s q : ℂ) :
    cepsStripExit ν β a l 0 E s q =
      stripPass ν (Icc 0 l) E β a 0 (fun v => Complex.exp (s * (v : ℂ))) q := by
  rw [cepsStripExit_eq_stripPass]
  simp only [sub_zero]

/-! ## Measurability and bounds -/

theorem measurable_stripPass_integrand {J E : Set ℝ} (hJ : MeasurableSet J) (hE : MeasurableSet E)
    (β a : ℝ) {φ : ℝ → ℂ} (hφ : Measurable φ) (n : ℕ) :
    Measurable fun p : ℝ × (ℕ → ℝ) => (krAlive J β a n p.1 p.2 : ℂ) *
      E.indicator (fun _ => (1 : ℂ)) (kWalk p.1 β a p.2 (n + 1)) * φ (kWalk p.1 β a p.2 (n + 1)) := by
  have h1 : Measurable fun p : ℝ × (ℕ → ℝ) => (krAlive J β a n p.1 p.2 : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_krAlive_prod hJ β a n)
  have h2 : Measurable fun p : ℝ × (ℕ → ℝ) =>
      E.indicator (fun _ => (1 : ℂ)) (kWalk p.1 β a p.2 (n + 1)) :=
    (measurable_const.indicator hE).comp (measurable_kWalk_prod β a (n + 1))
  have h3 : Measurable fun p : ℝ × (ℕ → ℝ) => φ (kWalk p.1 β a p.2 (n + 1)) :=
    hφ.comp (measurable_kWalk_prod β a (n + 1))
  exact (h1.mul h2).mul h3

theorem measurable_stripPass_integrand_right {J E : Set ℝ} (hJ : MeasurableSet J)
    (hE : MeasurableSet E) (β a y : ℝ) {φ : ℝ → ℂ} (hφ : Measurable φ) (n : ℕ) :
    Measurable fun g : ℕ → ℝ => (krAlive J β a n y g : ℂ) *
      E.indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) * φ (kWalk y β a g (n + 1)) := by
  have h1 : Measurable fun g : ℕ → ℝ => (krAlive J β a n y g : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_krAlive_right hJ β a n y)
  have h2 : Measurable fun g : ℕ → ℝ =>
      E.indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) :=
    (measurable_const.indicator hE).comp (measurable_kWalk_right y β a (n + 1))
  have h3 : Measurable fun g : ℕ → ℝ => φ (kWalk y β a g (n + 1)) :=
    hφ.comp (measurable_kWalk_right y β a (n + 1))
  exact (h1.mul h2).mul h3

theorem norm_stripPass_integrand_le (J E : Set ℝ) (β a y : ℝ) {φ : ℝ → ℂ} {M : ℝ}
    (hφ : ∀ v ∈ E, ‖φ v‖ ≤ M) (n : ℕ) (g : ℕ → ℝ) :
    ‖(krAlive J β a n y g : ℂ) * E.indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) *
        φ (kWalk y β a g (n + 1))‖ ≤
      M * (krAlive J β a n y g * E.indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1))) := by
  rw [indicator_one_ofReal, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (krAlive_nonneg _ _ _),
    abs_of_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)]
  by_cases h : kWalk y β a g (n + 1) ∈ E
  · rw [indicator_of_mem h]
    have := hφ _ h
    nlinarith [krAlive_nonneg (J := J) (β := β) (a := a) n y g]
  · rw [indicator_of_notMem h]
    simp

theorem norm_stripPass_integrand_le_one (J E : Set ℝ) (β a y : ℝ) {φ : ℝ → ℂ}
    (hφ : ∀ v ∈ E, ‖φ v‖ ≤ 1) (n : ℕ) (g : ℕ → ℝ) :
    ‖(krAlive J β a n y g : ℂ) * E.indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) *
        φ (kWalk y β a g (n + 1))‖ ≤ 1 := by
  refine (norm_stripPass_integrand_le J E β a y hφ n g).trans ?_
  rw [one_mul]
  exact krAlive_exit_le_one J E β a y n g

theorem norm_stripPassTerm_le (ν : ProbabilityMeasure ℝ) {J E : Set ℝ} (hJ : MeasurableSet J)
    (hE : MeasurableSet E) (β a y : ℝ) {φ : ℝ → ℂ} {M : ℝ}
    (hφ : ∀ v ∈ E, ‖φ v‖ ≤ M) (n : ℕ) :
    ‖stripPassTerm ν J E β a y φ n‖ ≤ M * cepsExitProb ν J β a y E n := by
  unfold stripPassTerm cepsExitProb
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le ((integrable_krAlive_exit ν hJ hE β a y n).const_mul M)
    (Eventually.of_forall fun g => norm_stripPass_integrand_le J E β a y hφ n g)

theorem integrable_stripPass_integrand (ν : ProbabilityMeasure ℝ) {J E : Set ℝ}
    (hJ : MeasurableSet J) (hE : MeasurableSet E) (β a y : ℝ) {φ : ℝ → ℂ} (hφm : Measurable φ)
    {M : ℝ} (hφ : ∀ v ∈ E, ‖φ v‖ ≤ M) (n : ℕ) :
    Integrable (fun g : ℕ → ℝ => (krAlive J β a n y g : ℂ) *
      E.indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) * φ (kWalk y β a g (n + 1)))
      (iidLaw ν) :=
  ((integrable_krAlive_exit ν hJ hE β a y n).const_mul M).mono'
    (measurable_stripPass_integrand_right hJ hE β a y hφm n).aestronglyMeasurable
    (Eventually.of_forall fun g => norm_stripPass_integrand_le J E β a y hφ n g)

theorem summable_norm_stripPass (ν : ProbabilityMeasure ℝ) {J E : Set ℝ} (hJ : MeasurableSet J)
    (hE : MeasurableSet E) (hJE : Disjoint J E) (β a y : ℝ) {φ : ℝ → ℂ} {M : ℝ}
    (hφ : ∀ v ∈ E, ‖φ v‖ ≤ M) {q : ℂ} (hq : 0 ≤ q.re) :
    Summable fun n : ℕ => ‖Complex.exp (-q * ((n : ℂ) + 1)) * stripPassTerm ν J E β a y φ n‖ := by
  refine ((summable_cepsExitProb ν hJ hE hJE β a y).1.mul_left M).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_
  rw [norm_mul]
  calc _ ≤ 1 * (M * cepsExitProb ν J β a y E n) :=
        mul_le_mul (norm_cexp_neg_mul_succ_le_one hq n)
          (norm_stripPassTerm_le ν hJ hE β a y hφ n) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem summable_stripPass (ν : ProbabilityMeasure ℝ) {J E : Set ℝ} (hJ : MeasurableSet J)
    (hE : MeasurableSet E) (hJE : Disjoint J E) (β a y : ℝ) {φ : ℝ → ℂ} {M : ℝ}
    (hφ : ∀ v ∈ E, ‖φ v‖ ≤ M) {q : ℂ} (hq : 0 ≤ q.re) :
    Summable fun n : ℕ => Complex.exp (-q * ((n : ℂ) + 1)) * stripPassTerm ν J E β a y φ n :=
  (summable_norm_stripPass ν hJ hE hJE β a y hφ hq).of_norm

/-- A mark bounded by `M` on the exit set gives a transform bounded by `M`. -/
theorem norm_stripPass_le (ν : ProbabilityMeasure ℝ) {J E : Set ℝ} (hJ : MeasurableSet J)
    (hE : MeasurableSet E) (hJE : Disjoint J E) (β a y : ℝ) {φ : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hφ : ∀ v ∈ E, ‖φ v‖ ≤ M) {q : ℂ} (hq : 0 ≤ q.re) :
    ‖stripPass ν J E β a y φ q‖ ≤ M := by
  obtain ⟨hP, hP1⟩ := summable_cepsExitProb ν hJ hE hJE β a y
  refine (norm_tsum_le_tsum_norm (summable_norm_stripPass ν hJ hE hJE β a y hφ hq)).trans ?_
  calc ∑' n : ℕ, ‖Complex.exp (-q * ((n : ℂ) + 1)) * stripPassTerm ν J E β a y φ n‖
      ≤ ∑' n : ℕ, M * cepsExitProb ν J β a y E n := by
        refine (summable_norm_stripPass ν hJ hE hJE β a y hφ hq).tsum_le_tsum (fun n => ?_)
          (hP.mul_left M)
        rw [norm_mul]
        calc _ ≤ 1 * (M * cepsExitProb ν J β a y E n) :=
              mul_le_mul (norm_cexp_neg_mul_succ_le_one hq n)
                (norm_stripPassTerm_le ν hJ hE β a y hφ n) (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ = M * ∑' n : ℕ, cepsExitProb ν J β a y E n := tsum_mul_left
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hP1 hM
    _ = M := mul_one M

/-! ## Linearity in the mark -/

theorem stripPassTerm_congr (ν : ProbabilityMeasure ℝ) (J E : Set ℝ) (β a y : ℝ) {φ ψ : ℝ → ℂ}
    (h : ∀ v ∈ E, φ v = ψ v) (n : ℕ) :
    stripPassTerm ν J E β a y φ n = stripPassTerm ν J E β a y ψ n := by
  unfold stripPassTerm
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  by_cases hv : kWalk y β a g (n + 1) ∈ E
  · simp only [h _ hv]
  · simp [indicator_of_notMem hv]

theorem stripPass_congr (ν : ProbabilityMeasure ℝ) (J E : Set ℝ) (β a y : ℝ) {φ ψ : ℝ → ℂ}
    (h : ∀ v ∈ E, φ v = ψ v) (q : ℂ) :
    stripPass ν J E β a y φ q = stripPass ν J E β a y ψ q := by
  unfold stripPass
  simp_rw [stripPassTerm_congr ν J E β a y h]

theorem stripPassTerm_add (ν : ProbabilityMeasure ℝ) {J E : Set ℝ} (hJ : MeasurableSet J)
    (hE : MeasurableSet E) (β a y : ℝ) {φ ψ : ℝ → ℂ} (hφm : Measurable φ) (hψm : Measurable ψ)
    {M N : ℝ} (hφ : ∀ v ∈ E, ‖φ v‖ ≤ M) (hψ : ∀ v ∈ E, ‖ψ v‖ ≤ N)
    (n : ℕ) :
    stripPassTerm ν J E β a y (fun v => φ v + ψ v) n =
      stripPassTerm ν J E β a y φ n + stripPassTerm ν J E β a y ψ n := by
  unfold stripPassTerm
  rw [← integral_add (integrable_stripPass_integrand ν hJ hE β a y hφm hφ n)
    (integrable_stripPass_integrand ν hJ hE β a y hψm hψ n)]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  ring

theorem stripPassTerm_const_mul (ν : ProbabilityMeasure ℝ) (J E : Set ℝ) (β a y : ℝ)
    (c : ℂ) (φ : ℝ → ℂ) (n : ℕ) :
    stripPassTerm ν J E β a y (fun v => c * φ v) n = c * stripPassTerm ν J E β a y φ n := by
  unfold stripPassTerm
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  ring

theorem stripPass_add (ν : ProbabilityMeasure ℝ) {J E : Set ℝ} (hJ : MeasurableSet J)
    (hE : MeasurableSet E) (hJE : Disjoint J E) (β a y : ℝ) {φ ψ : ℝ → ℂ}
    (hφm : Measurable φ) (hψm : Measurable ψ) {M N : ℝ}
    (hφ : ∀ v ∈ E, ‖φ v‖ ≤ M) (hψ : ∀ v ∈ E, ‖ψ v‖ ≤ N) {q : ℂ} (hq : 0 ≤ q.re) :
    stripPass ν J E β a y (fun v => φ v + ψ v) q =
      stripPass ν J E β a y φ q + stripPass ν J E β a y ψ q := by
  unfold stripPass
  rw [← (summable_stripPass ν hJ hE hJE β a y hφ hq).tsum_add
    (summable_stripPass ν hJ hE hJE β a y hψ hq)]
  refine tsum_congr fun n => ?_
  rw [stripPassTerm_add ν hJ hE β a y hφm hψm hφ hψ n]
  ring

theorem stripPass_const_mul (ν : ProbabilityMeasure ℝ) (J E : Set ℝ) (β a y : ℝ) (c : ℂ)
    (φ : ℝ → ℂ) (q : ℂ) :
    stripPass ν J E β a y (fun v => c * φ v) q = c * stripPass ν J E β a y φ q := by
  unfold stripPass
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [stripPassTerm_const_mul]
  ring

/-! ## The pathwise first-exit identity with an absolute mark -/

/-- The integrand of the passage-below term from the start `x`. -/
def stripPassBelowIntegrand (β a : ℝ) (φ : ℝ → ℂ) (m : ℕ) (x : ℝ) (h : ℕ → ℝ) : ℂ :=
  (krAlive (Ici 0) β a m x h : ℂ) * (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk x β a h (m + 1)) *
    φ (kWalk x β a h (m + 1))

/-- The prefix up to an upward exit of `[0, l]` at time `n + 1`. -/
def stripHighPre (β a l y : ℝ) (n : ℕ) (g : ℕ → ℝ) : ℂ :=
  (krAlive (Icc 0 l) β a n y g : ℂ) * (Ioi l).indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1))

theorem measurable_stripHighPre (β a l y : ℝ) (n : ℕ) : Measurable (stripHighPre β a l y n) :=
  (Complex.measurable_ofReal.comp (measurable_krAlive_right measurableSet_Icc β a n y)).mul
    ((measurable_const.indicator measurableSet_Ioi).comp (measurable_kWalk_right y β a (n + 1)))

theorem norm_stripHighPre_le (β a l y : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    ‖stripHighPre β a l y n g‖ ≤
      krAlive (Icc 0 l) β a n y g * (Ioi l).indicator (fun _ => (1 : ℝ)) (kWalk y β a g (n + 1)) := by
  unfold stripHighPre
  rw [indicator_one_ofReal, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (krAlive_nonneg _ _ _),
    abs_of_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)]

theorem norm_stripHighPre_le_one (β a l y : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    ‖stripHighPre β a l y n g‖ ≤ 1 :=
  (norm_stripHighPre_le β a l y n g).trans (krAlive_exit_le_one _ _ β a y n g)

theorem stripPassBelowIntegrand_pathwise (β a : ℝ) {l y : ℝ} (hy : y ∈ Icc 0 l) (φ : ℝ → ℂ)
    (N : ℕ) (g : ℕ → ℝ) :
    stripPassBelowIntegrand β a φ N y g =
      (krAlive (Icc 0 l) β a N y g : ℂ) * (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk y β a g (N + 1)) *
        φ (kWalk y β a g (N + 1)) +
      ∑ n ∈ Finset.range N, stripHighPre β a l y n g *
        stripPassBelowIntegrand β a φ (N - (n + 1)) (kWalk y β a g (n + 1))
          (fun i => g (i + (n + 1))) := by
  unfold stripPassBelowIntegrand stripHighPre
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
  ring

theorem measurable_stripPassBelowIntegrand (β a : ℝ) {φ : ℝ → ℂ} (hφ : Measurable φ) (m : ℕ) :
    Measurable (Function.uncurry (stripPassBelowIntegrand β a φ m)) := by
  have h := measurable_stripPass_integrand (J := Ici 0) (E := Iio 0) measurableSet_Ici
    measurableSet_Iio β a hφ m
  exact h

theorem measurable_stripPassBelowIntegrand_shift (β a : ℝ) {φ : ℝ → ℂ} (hφ : Measurable φ)
    (y : ℝ) (n m : ℕ) :
    Measurable fun g : ℕ → ℝ =>
      stripPassBelowIntegrand β a φ m (kWalk y β a g (n + 1)) (fun i => g (i + (n + 1))) := by
  have hsh : Measurable fun g : ℕ → ℝ => (kWalk y β a g (n + 1), fun i => g (i + (n + 1))) :=
    (measurable_kWalk_right y β a (n + 1)).prodMk
      (measurable_pi_lambda _ fun i => measurable_pi_apply (i + (n + 1)))
  have h := (measurable_stripPassBelowIntegrand β a hφ m).comp hsh
  exact h

theorem norm_stripPassBelowIntegrand_le (β a : ℝ) {φ : ℝ → ℂ} (hφ : ∀ v ∈ Iio (0 : ℝ), ‖φ v‖ ≤ 1)
    (m : ℕ) (x : ℝ) (h : ℕ → ℝ) : ‖stripPassBelowIntegrand β a φ m x h‖ ≤ 1 :=
  norm_stripPass_integrand_le_one (Ici 0) (Iio 0) β a x hφ m h

/-- `E[pre_n · P_m(V_{n+1})]`, `P_m` the `m`-th passage-below term from the exit point. -/
def stripHighThen (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (φ : ℝ → ℂ) (n m : ℕ) : ℂ :=
  ∫ g, stripHighPre β a l y n g * stripPassTerm ν (Ici 0) (Iio 0) β a (kWalk y β a g (n + 1)) φ m
    ∂(iidLaw ν)

theorem stripPassTerm_below_decomp (ν : ProbabilityMeasure ℝ) (β a : ℝ) {l y : ℝ}
    (hy : y ∈ Icc 0 l) {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : ∀ v ∈ Iio (0 : ℝ), ‖φ v‖ ≤ 1)
    (N : ℕ) :
    stripPassTerm ν (Ici 0) (Iio 0) β a y φ N = stripPassTerm ν (Icc 0 l) (Iio 0) β a y φ N +
      ∑ n ∈ Finset.range N, stripHighThen ν β a l y φ n (N - (n + 1)) := by
  have hmeas : ∀ n m : ℕ, Measurable fun g : ℕ → ℝ => stripHighPre β a l y n g *
      stripPassBelowIntegrand β a φ m (kWalk y β a g (n + 1)) (fun i => g (i + (n + 1))) := by
    intro n m
    exact (measurable_stripHighPre β a l y n).mul
      (measurable_stripPassBelowIntegrand_shift β a hφm y n m)
  have hterm : ∀ n ∈ Finset.range N, Integrable (fun g => stripHighPre β a l y n g *
      stripPassBelowIntegrand β a φ (N - (n + 1)) (kWalk y β a g (n + 1))
        (fun i => g (i + (n + 1)))) (iidLaw ν) := fun n _ =>
    integrable_of_norm_le_one (hmeas n _) fun g => by
      rw [norm_mul]
      calc _ ≤ 1 * 1 := mul_le_mul (norm_stripHighPre_le_one β a l y n g)
            (norm_stripPassBelowIntegrand_le β a hφ _ _ _) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  have hstart : stripPassTerm ν (Ici 0) (Iio 0) β a y φ N =
      ∫ g, stripPassBelowIntegrand β a φ N y g ∂(iidLaw ν) := rfl
  rw [hstart, integral_congr_ae (Eventually.of_forall fun g =>
    stripPassBelowIntegrand_pathwise β a hy φ N g)]
  rw [integral_add (integrable_stripPass_integrand ν measurableSet_Icc measurableSet_Iio β a y hφm
      hφ N) (integrable_finsetSum _ hterm), integral_finsetSum _ hterm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold stripHighThen
  have hshift := integral_mul_shift_dep ν (n + 1) (measurable_stripHighPre β a l y n)
    (fun g g' h => by
      unfold stripHighPre
      rw [krAlive_congr fun i hi => h i (by omega), surv_kWalk_congr h])
    (measurable_kWalk_right y β a (n + 1)) (fun g g' h => surv_kWalk_congr h)
    (measurable_stripPassBelowIntegrand β a hφm (N - (n + 1))) (norm_stripHighPre_le_one β a l y n)
    (norm_stripPassBelowIntegrand_le β a hφ _)
  rw [hshift]
  rfl

/-! ## Summing over the passage time -/

theorem norm_stripPassTerm_below_le (ν : ProbabilityMeasure ℝ) (β a x : ℝ) {φ : ℝ → ℂ}
    (hφ : ∀ v ∈ Iio (0 : ℝ), ‖φ v‖ ≤ 1) (m : ℕ) :
    ‖stripPassTerm ν (Ici 0) (Iio 0) β a x φ m‖ ≤ cepsExitProb ν (Ici 0) β a x (Iio 0) m := by
  have := norm_stripPassTerm_le ν (J := Ici 0) (E := Iio 0) measurableSet_Ici measurableSet_Iio
    β a x hφ m
  rwa [one_mul] at this

theorem norm_stripHighThen_le (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) {φ : ℝ → ℂ}
    (hφ : ∀ v ∈ Iio (0 : ℝ), ‖φ v‖ ≤ 1) (n m : ℕ) :
    ‖stripHighThen ν β a l y φ n m‖ ≤ cepsHighThenProb ν β a l y (n, m) := by
  unfold stripHighThen cepsHighThenProb
  refine norm_integral_le_of_norm_le (integrable_highExit_mul_prob ν β a l y n m)
    (Eventually.of_forall fun g => ?_)
  rw [norm_mul]
  exact mul_le_mul (norm_stripHighPre_le β a l y n g)
    (norm_stripPassTerm_below_le ν β a _ hφ m) (norm_nonneg _) (krAlive_exit_nonneg _ _ _ _ _ _ _)

theorem measurable_stripPassTerm_start (ν : ProbabilityMeasure ℝ) {J E : Set ℝ}
    (hJ : MeasurableSet J) (hE : MeasurableSet E) (β a : ℝ) {φ : ℝ → ℂ} (hφ : Measurable φ)
    (n : ℕ) : Measurable fun x => stripPassTerm ν J E β a x φ n :=
  ((measurable_stripPass_integrand hJ hE β a hφ n).stronglyMeasurable.integral_prod_right'
    (ν := iidLaw ν)).measurable

/-- **Two-first-passage decomposition with an absolute mark.** Started in `[0, l]`, the first
passage below `0` is the low exit of the band, or an upward exit followed by a passage below `0`
from the exit point. The mark only needs to be measurable and bounded by one below `0`. -/
theorem stripPass_below_decomp (ν : ProbabilityMeasure ℝ) (β a : ℝ) {l y : ℝ} (hy : y ∈ Icc 0 l)
    {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : ∀ v ∈ Iio (0 : ℝ), ‖φ v‖ ≤ 1) {q : ℂ}
    (hq : 0 ≤ q.re) :
    stripPass ν (Ici 0) (Iio 0) β a y φ q =
      stripPass ν (Icc 0 l) (Iio 0) β a y φ q +
        stripPass ν (Icc 0 l) (Ioi l) β a y (fun x => stripPass ν (Ici 0) (Iio 0) β a x φ q) q := by
  set c : ℕ × ℕ → ℂ := fun p => Complex.exp (-q * ((p.1 : ℂ) + 1)) *
    Complex.exp (-q * ((p.2 : ℂ) + 1)) * stripHighThen ν β a l y φ p.1 p.2 with hcdef
  have hc : Summable c := by
    refine (summable_cepsHighThenProb ν β a l y).of_norm_bounded fun p => ?_
    rw [hcdef, norm_mul, norm_mul]
    calc _ ≤ 1 * 1 * cepsHighThenProb ν β a l y (p.1, p.2) :=
          mul_le_mul (mul_le_mul (norm_cexp_neg_mul_succ_le_one hq _)
            (norm_cexp_neg_mul_succ_le_one hq _) (norm_nonneg _) zero_le_one)
            (norm_stripHighThen_le ν β a l y hφ _ _) (norm_nonneg _) (by norm_num)
      _ = cepsHighThenProb ν β a l y p := by simp
  -- the inner passage, as a function of the start
  have hPm : Measurable fun x => stripPass ν (Ici 0) (Iio 0) β a x φ q := by
    unfold stripPass
    exact Measurable.tsum fun m => (measurable_stripPassTerm_start ν (J := Ici 0) (E := Iio 0)
      measurableSet_Ici measurableSet_Iio β a hφm m).const_mul _
  have hP1 : ∀ x, ‖stripPass ν (Ici 0) (Iio 0) β a x φ q‖ ≤ 1 := fun x =>
    norm_stripPass_le ν measurableSet_Ici measurableSet_Iio disjoint_Ici_Iio β a x zero_le_one hφ hq
  -- the rows
  have hrow : ∀ n : ℕ, ∑' m, c (n, m) = Complex.exp (-q * ((n : ℂ) + 1)) *
      stripPassTerm ν (Icc 0 l) (Ioi l) β a y
        (fun x => stripPass ν (Ici 0) (Iio 0) β a x φ q) n := by
    intro n
    have hint : stripPassTerm ν (Icc 0 l) (Ioi l) β a y
        (fun x => stripPass ν (Ici 0) (Iio 0) β a x φ q) n =
        ∑' m : ℕ, Complex.exp (-q * ((m : ℂ) + 1)) * stripHighThen ν β a l y φ n m := by
      have e : ∀ g : ℕ → ℝ, (krAlive (Icc 0 l) β a n y g : ℂ) *
          (Ioi l).indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) *
          stripPass ν (Ici 0) (Iio 0) β a (kWalk y β a g (n + 1)) φ q =
          ∑' m : ℕ, Complex.exp (-q * ((m : ℂ) + 1)) * (stripHighPre β a l y n g *
            stripPassTerm ν (Ici 0) (Iio 0) β a (kWalk y β a g (n + 1)) φ m) := by
        intro g
        unfold stripPass
        rw [← tsum_mul_left]
        congr 1
        funext m
        unfold stripHighPre
        ring
      unfold stripPassTerm
      simp_rw [e]
      have hm1 : ∀ m : ℕ, Measurable fun g : ℕ → ℝ => Complex.exp (-q * ((m : ℂ) + 1)) *
          (stripHighPre β a l y n g *
            stripPassTerm ν (Ici 0) (Iio 0) β a (kWalk y β a g (n + 1)) φ m) := by
        intro m
        have h1 := measurable_stripHighPre β a l y n
        have h2 := (measurable_stripPassTerm_start ν (J := Ici 0) (E := Iio 0) measurableSet_Ici
          measurableSet_Iio β a hφm m).comp (measurable_kWalk_right y β a (n + 1))
        exact (h1.mul h2).const_mul _
      rw [integral_tsum]
      · congr 1
        funext m
        rw [integral_const_mul]
        rfl
      · intro m
        exact (hm1 m).aestronglyMeasurable
      · have hb : ∀ (m : ℕ) (g : ℕ → ℝ), ‖Complex.exp (-q * ((m : ℂ) + 1)) * (stripHighPre β a l y n g *
            stripPassTerm ν (Ici 0) (Iio 0) β a (kWalk y β a g (n + 1)) φ m)‖ ≤
            cepsExitProb ν (Ici 0) β a (kWalk y β a g (n + 1)) (Iio 0) m := by
          intro m g
          rw [norm_mul, norm_mul]
          calc _ ≤ 1 * (1 * cepsExitProb ν (Ici 0) β a (kWalk y β a g (n + 1)) (Iio 0) m) :=
                mul_le_mul (norm_cexp_neg_mul_succ_le_one hq _) (mul_le_mul
                  (norm_stripHighPre_le_one β a l y n g) (norm_stripPassTerm_below_le ν β a _ hφ m)
                  (norm_nonneg _) zero_le_one) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                  zero_le_one
            _ = _ := by ring
        refine ne_top_of_le_ne_top (b := ∫⁻ _ : ℕ → ℝ, 1 ∂(iidLaw ν)) (by simp) ?_
        rw [← lintegral_tsum fun m => (hm1 m).enorm.aemeasurable]
        refine lintegral_mono fun g => ?_
        obtain ⟨hP, hP1'⟩ := summable_cepsExitProb ν measurableSet_Ici measurableSet_Iio
          disjoint_Ici_Iio β a (kWalk y β a g (n + 1))
        calc ∑' m : ℕ, ‖Complex.exp (-q * ((m : ℂ) + 1)) * (stripHighPre β a l y n g *
              stripPassTerm ν (Ici 0) (Iio 0) β a (kWalk y β a g (n + 1)) φ m)‖ₑ
            ≤ ∑' m : ℕ, ENNReal.ofReal (cepsExitProb ν (Ici 0) β a (kWalk y β a g (n + 1)) (Iio 0) m) :=
              ENNReal.tsum_le_tsum fun m => by
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hb m g)
          _ = ENNReal.ofReal (∑' m : ℕ, cepsExitProb ν (Ici 0) β a (kWalk y β a g (n + 1)) (Iio 0) m) :=
              (ENNReal.ofReal_tsum_of_nonneg (fun m => cepsExitProb_nonneg _ _ _ _ _ _ _) hP).symm
          _ ≤ 1 := ENNReal.ofReal_le_one.2 hP1'
    rw [hint, ← tsum_mul_left]
    congr 1
    funext m
    rw [hcdef]
    ring
  -- the passage series term by term
  have hlowS := summable_stripPass ν measurableSet_Icc measurableSet_Iio (disjoint_Icc_Iio l) β a y
    hφ hq
  set d : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N, c (n, N - (n + 1)) with hd
  have hPN : ∀ N : ℕ, Complex.exp (-q * ((N : ℂ) + 1)) * stripPassTerm ν (Ici 0) (Iio 0) β a y φ N =
      Complex.exp (-q * ((N : ℂ) + 1)) * stripPassTerm ν (Icc 0 l) (Iio 0) β a y φ N + d N := by
    intro N
    rw [stripPassTerm_below_decomp ν β a hy hφm hφ N, mul_add, Finset.mul_sum, hd]
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
    have h1 := summable_stripPass ν measurableSet_Ici measurableSet_Iio disjoint_Ici_Iio β a y
      hφ hq
    have : d = fun N : ℕ => Complex.exp (-q * ((N : ℂ) + 1)) *
        stripPassTerm ν (Ici 0) (Iio 0) β a y φ N -
        Complex.exp (-q * ((N : ℂ) + 1)) * stripPassTerm ν (Icc 0 l) (Iio 0) β a y φ N := by
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
  have hmain : stripPass ν (Ici 0) (Iio 0) β a y φ q =
      stripPass ν (Icc 0 l) (Iio 0) β a y φ q + ∑' p, c p := by
    unfold stripPass
    rw [tsum_congr hPN, hlowS.tsum_add hdS, hdsum]
  rw [hmain, hc.tsum_prod' fun n => hc.prod_factor n]
  unfold stripPass
  congr 1
  exact tsum_congr hrow

end

end PGM
