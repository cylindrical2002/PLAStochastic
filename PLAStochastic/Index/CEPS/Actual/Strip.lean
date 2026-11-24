import PLAStochastic.Index.CEPS.Actual.Representation

/-!
# P-CEPS WP8: exact strip identities, telescoping and reflection (S-2 (a), (e))

`research/2026-10-02-lean-ceps/blueprint-CS.md` §3.4 and lemma S-2. The walk
`W_n = kWalk y β a g n = y + nβ - a(X_1 + ⋯ + X_n)` (step `β - aX`, gaps iid `ν`) is killed outside the
closed band `[0, l]`; marks are relative to the start, `e^{s(W_n - y)}`, with `Re s = 0`.

* `cepsStripSeries ν β a l y s q = ∑ₙ e^{-qn} E[e^{s(W_n - y)}; W_0, …, W_n ∈ [0, l]]` (`H`);
* `cepsStripExit ν β a l y E s q = ∑ₙ e^{-q(n+1)} E[e^{s(W_{n+1} - y)}; W_0, …, W_n ∈ [0, l], W_{n+1} ∈ E]`,
  the exit transform through `E = Iio 0` (low) or `E = Ioi l` (high);
* `cepsStepMgf ν β a s = E e^{s(β - aX)}`.

(a) **Telescoping** (`cepsStrip_telescope`): `(1 - e^{-q} E e^{s(β - aX)}) H = 1 - u_low - u_high`.
(e) **Reflection** (`cepsStripSeries_reflect`, `cepsStripExit_reflect`): `(β, a, y, s) ↦ (-β, -a, l - y, -s)`
maps the strip to itself, exchanging the low and high exits; the top-started `Y_μ`-strip of the
blueprint is the outer-walk strip `cepsStripEntrance` of theorem (E) (`cepsStripEntrance_eq`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

/-! ## Definitions -/

/-- `E[e^{s(W_n - y)}; W_0, …, W_n ∈ [0, l]]`. -/
def cepsStripMark (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  ∫ g, (krAlive (Icc 0 l) β a n y g : ℂ) * Complex.exp (s * ((kWalk y β a g n - y : ℝ) : ℂ))
    ∂(iidLaw ν)

/-- The strip entrance series `H = ∑ₙ e^{-qn} E[e^{s(W_n - y)}; W_0, …, W_n ∈ [0, l]]`. -/
def cepsStripSeries (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (s q : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-q * n) * cepsStripMark ν β a l y s n

/-- The `n`-th exit term: `E[e^{s(W_{n+1} - y)}; W_0, …, W_n ∈ [0, l], W_{n+1} ∈ E]`. -/
def cepsStripExitTerm (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (E : Set ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  ∫ g, (krAlive (Icc 0 l) β a n y g : ℂ) * E.indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) *
    Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ)) ∂(iidLaw ν)

/-- The exit transform through `E`: `∑ₙ e^{-q(n+1)} E[e^{s(W_{n+1} - y)}; alive up to n, W_{n+1} ∈ E]`. -/
def cepsStripExit (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (E : Set ℝ) (s q : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-q * ((n : ℂ) + 1)) * cepsStripExitTerm ν β a l y E s n

/-- The step transform `E e^{s(β - aX)}`. -/
def cepsStepMgf (ν : ProbabilityMeasure ℝ) (β a : ℝ) (s : ℂ) : ℂ :=
  ∫ x, Complex.exp (s * ((β - a * x : ℝ) : ℂ)) ∂(ν : Measure ℝ)

/-! ## Basic bounds -/

theorem norm_cexp_mul_ofReal_of_re_eq_zero {s : ℂ} (hs : s.re = 0) (x : ℝ) :
    ‖Complex.exp (s * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, hs]

theorem measurable_kWalk_right (y β a : ℝ) (n : ℕ) : Measurable fun g : ℕ → ℝ => kWalk y β a g n :=
  (measurable_kWalk_prod β a n).comp (measurable_const.prodMk measurable_id)

theorem norm_cepsStripMark_le (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) {s : ℂ} (hs : s.re = 0)
    (n : ℕ) : ‖cepsStripMark ν β a l y s n‖ ≤ krSurv (Icc 0 l) (ν : Measure ℝ) β a n y := by
  unfold cepsStripMark
  rw [krSurv_eq_integral measurableSet_Icc]
  refine norm_integral_le_of_norm_le (kr_integrable_of_bdd
    (measurable_krAlive_right measurableSet_Icc _ _ n y) (abs_krAlive_le_one n y))
    (Eventually.of_forall fun g => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (krAlive_nonneg _ _ _),
    norm_cexp_mul_ofReal_of_re_eq_zero hs, mul_one]

theorem norm_cepsStripExitTerm_le (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (E : Set ℝ)
    {s : ℂ} (hs : s.re = 0) (n : ℕ) :
    ‖cepsStripExitTerm ν β a l y E s n‖ ≤ krSurv (Icc 0 l) (ν : Measure ℝ) β a n y := by
  unfold cepsStripExitTerm
  rw [krSurv_eq_integral measurableSet_Icc]
  refine norm_integral_le_of_norm_le (kr_integrable_of_bdd
    (measurable_krAlive_right measurableSet_Icc _ _ n y) (abs_krAlive_le_one n y))
    (Eventually.of_forall fun g => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (krAlive_nonneg _ _ _),
    norm_cexp_mul_ofReal_of_re_eq_zero hs, mul_one]
  have : ‖E.indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1))‖ ≤ 1 := by
    by_cases h : kWalk y β a g (n + 1) ∈ E <;> simp [h]
  calc _ ≤ krAlive (Icc 0 l) β a n y g * 1 :=
        mul_le_mul_of_nonneg_left this (krAlive_nonneg _ _ _)
    _ = _ := mul_one _

variable {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} {D : ℝ}

theorem CepsGapDensity.summable_cepsStripMark (hf : CepsGapDensity ν f D) (β : ℝ) {a : ℝ}
    (ha : a ≠ 0) (l y : ℝ) {s q : ℂ} (hs : s.re = 0) (hq : 0 ≤ q.re) :
    Summable (fun n : ℕ => ‖Complex.exp (-q * n) * cepsStripMark ν β a l y s n‖) := by
  obtain ⟨C, r, hC, hr0, hr1, hb⟩ := hf.krSurv_geometric l β ha
  refine ((summable_geometric_of_lt_one hr0 hr1).mul_left C).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_
  rw [norm_mul]
  calc ‖Complex.exp (-q * n)‖ * ‖cepsStripMark ν β a l y s n‖ ≤ 1 * (C * r ^ n) :=
        mul_le_mul (norm_cexp_neg_mul_nat_le_one hq n)
          ((norm_cepsStripMark_le ν β a l y hs n).trans (hb n y)) (norm_nonneg _) zero_le_one
    _ = C * r ^ n := one_mul _

theorem CepsGapDensity.summable_cepsStripExitTerm (hf : CepsGapDensity ν f D) (β : ℝ) {a : ℝ}
    (ha : a ≠ 0) (l y : ℝ) (E : Set ℝ) {s q : ℂ} (hs : s.re = 0) (hq : 0 ≤ q.re) :
    Summable (fun n : ℕ =>
      ‖Complex.exp (-q * ((n : ℂ) + 1)) * cepsStripExitTerm ν β a l y E s n‖) := by
  obtain ⟨C, r, hC, hr0, hr1, hb⟩ := hf.krSurv_geometric l β ha
  refine ((summable_geometric_of_lt_one hr0 hr1).mul_left C).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_
  rw [norm_mul]
  calc ‖Complex.exp (-q * ((n : ℂ) + 1))‖ * ‖cepsStripExitTerm ν β a l y E s n‖
      ≤ 1 * (C * r ^ n) :=
        mul_le_mul (norm_cexp_neg_mul_succ_le_one hq n)
          ((norm_cepsStripExitTerm_le ν β a l y E hs n).trans (hb n y)) (norm_nonneg _)
          zero_le_one
    _ = C * r ^ n := one_mul _

/-! ## (a) Telescoping -/

theorem measurable_cepsStrip_integrand (β a l y : ℝ) (s : ℂ) (n m : ℕ) :
    Measurable fun g : ℕ → ℝ => (krAlive (Icc 0 l) β a n y g : ℂ) *
      Complex.exp (s * ((kWalk y β a g m - y : ℝ) : ℂ)) :=
  (Complex.measurable_ofReal.comp (measurable_krAlive_right measurableSet_Icc β a n y)).mul
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_kWalk_right y β a m).sub_const y))))

/-- One unkilled step is independent: `E[e^{s(W_{n+1} - y)}; alive up to n] = E e^{s(β - aX)} · A_n`. -/
theorem cepsStrip_step (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (s : ℂ) (n : ℕ) :
    ∫ g, (krAlive (Icc 0 l) β a n y g : ℂ) *
        Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ)) ∂(iidLaw ν) =
      cepsStripMark ν β a l y s n * cepsStepMgf ν β a s := by
  have hsplit : ∀ g : ℕ → ℝ, (krAlive (Icc 0 l) β a n y g : ℂ) *
      Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ)) =
      ((krAlive (Icc 0 l) β a n y g : ℂ) * Complex.exp (s * ((kWalk y β a g n - y : ℝ) : ℂ))) *
        (fun g' : ℕ → ℝ => Complex.exp (s * ((β - a * g' 0 : ℝ) : ℂ))) (WienerHopf.shift n g) := by
    intro g
    rw [kernel_kWalk_succ_last, mul_assoc, ← Complex.exp_add]
    simp only [WienerHopf.shift, Nat.add_zero]
    congr 2
    push_cast
    ring
  simp_rw [hsplit]
  have hFd : WienerHopf.DependsOnPrefix n fun g : ℕ → ℝ => (krAlive (Icc 0 l) β a n y g : ℂ) *
      Complex.exp (s * ((kWalk y β a g n - y : ℝ) : ℂ)) := by
    intro ω ω' h
    simp only
    rw [krAlive_congr h, surv_kWalk_congr h]
  have hG : Measurable fun g' : ℕ → ℝ => Complex.exp (s * ((β - a * g' 0 : ℝ) : ℂ)) := by
    fun_prop
  change ∫ g, _ ∂(WienerHopf.pathLaw (ν : Measure ℝ)) = _
  rw [WienerHopf.integral_mul_shift (ρ := (ν : Measure ℝ))
    (measurable_cepsStrip_integrand β a l y s n n) hFd hG]
  congr 1
  exact WienerHopf.integral_comp_eval (ρ := (ν : Measure ℝ)) 0
    (g := fun x => Complex.exp (s * ((β - a * x : ℝ) : ℂ)))
    (Measurable.aestronglyMeasurable (by fun_prop))

theorem indicator_Icc_add_Iio_add_Ioi {l : ℝ} (hl : 0 ≤ l) (x : ℝ) :
    (Icc 0 l).indicator (fun _ => (1 : ℂ)) x + (Iio 0).indicator (fun _ => (1 : ℂ)) x +
      (Ioi l).indicator (fun _ => (1 : ℂ)) x = 1 := by
  rcases lt_or_ge x 0 with h0 | h0
  · rw [indicator_of_notMem (fun h : x ∈ Icc 0 l => by linarith [h.1]),
      indicator_of_mem (show x ∈ Iio 0 from h0),
      indicator_of_notMem (fun h : x ∈ Ioi l => by simp at h; linarith)]
    ring
  rcases le_or_gt x l with hl' | hl'
  · rw [indicator_of_mem (show x ∈ Icc 0 l from ⟨h0, hl'⟩),
      indicator_of_notMem (fun h : x ∈ Iio 0 => by simp at h; linarith),
      indicator_of_notMem (fun h : x ∈ Ioi l => by simp at h; linarith)]
    ring
  · rw [indicator_of_notMem (fun h : x ∈ Icc 0 l => by linarith [h.2]),
      indicator_of_notMem (fun h : x ∈ Iio 0 => by simp at h; linarith),
      indicator_of_mem (show x ∈ Ioi l from hl')]
    ring

theorem measurable_cepsStripExit_integrand (β a l y : ℝ) {E : Set ℝ} (hE : MeasurableSet E)
    (s : ℂ) (n : ℕ) :
    Measurable fun g : ℕ → ℝ => (krAlive (Icc 0 l) β a n y g : ℂ) *
      E.indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) *
      Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ)) :=
  ((Complex.measurable_ofReal.comp (measurable_krAlive_right measurableSet_Icc β a n y)).mul
    ((measurable_const.indicator hE).comp (measurable_kWalk_right y β a (n + 1)))).mul
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_kWalk_right y β a (n + 1)).sub_const y))))

theorem integrable_of_norm_le_one {μ : Measure (ℕ → ℝ)} [IsProbabilityMeasure μ]
    {F : (ℕ → ℝ) → ℂ} (hF : Measurable F) (hb : ∀ g, ‖F g‖ ≤ 1) : Integrable F μ :=
  (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable (Eventually.of_forall hb)

theorem norm_cepsStripExit_integrand_le (β a l y : ℝ) (E : Set ℝ) {s : ℂ} (hs : s.re = 0)
    (n : ℕ) (g : ℕ → ℝ) :
    ‖(krAlive (Icc 0 l) β a n y g : ℂ) * E.indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) *
      Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ))‖ ≤ 1 := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (krAlive_nonneg _ _ _),
    norm_cexp_mul_ofReal_of_re_eq_zero hs, mul_one]
  have : ‖E.indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1))‖ ≤ 1 := by
    by_cases h : kWalk y β a g (n + 1) ∈ E <;> simp [h]
  calc _ ≤ 1 * 1 := mul_le_mul (krAlive_le_one _ _ _) this (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Splitting one unkilled step into survival and the two exits. -/
theorem cepsStrip_step_split (ν : ProbabilityMeasure ℝ) (β a : ℝ) {l : ℝ} (hl : 0 ≤ l) (y : ℝ)
    {s : ℂ} (hs : s.re = 0) (n : ℕ) :
    ∫ g, (krAlive (Icc 0 l) β a n y g : ℂ) *
        Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ)) ∂(iidLaw ν) =
      cepsStripMark ν β a l y s (n + 1) + cepsStripExitTerm ν β a l y (Iio 0) s n +
        cepsStripExitTerm ν β a l y (Ioi l) s n := by
  have hpt : ∀ g : ℕ → ℝ, (krAlive (Icc 0 l) β a n y g : ℂ) *
      Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ)) =
      (krAlive (Icc 0 l) β a (n + 1) y g : ℂ) *
          Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ)) +
        (krAlive (Icc 0 l) β a n y g : ℂ) *
          (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) *
          Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ)) +
        (krAlive (Icc 0 l) β a n y g : ℂ) *
          (Ioi l).indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) *
          Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ)) := by
    intro g
    have h1 := indicator_Icc_add_Iio_add_Ioi hl (kWalk y β a g (n + 1))
    rw [krAlive_succ_last, Complex.ofReal_mul, ← indicator_one_ofReal]
    linear_combination (-(↑(krAlive (Icc 0 l) β a n y g) *
      Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ)))) * h1
  have hb1 : ∀ g, ‖(krAlive (Icc 0 l) β a (n + 1) y g : ℂ) *
      Complex.exp (s * ((kWalk y β a g (n + 1) - y : ℝ) : ℂ))‖ ≤ 1 := fun g => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (krAlive_nonneg _ _ _),
      norm_cexp_mul_ofReal_of_re_eq_zero hs, mul_one]
    exact krAlive_le_one _ _ _
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add, integral_add]
  · rfl
  · exact integrable_of_norm_le_one (measurable_cepsStrip_integrand β a l y s (n + 1) (n + 1)) hb1
  · exact integrable_of_norm_le_one (measurable_cepsStripExit_integrand β a l y measurableSet_Iio s n)
      (norm_cepsStripExit_integrand_le β a l y _ hs n)
  · exact (integrable_of_norm_le_one (measurable_cepsStrip_integrand β a l y s (n + 1) (n + 1))
      hb1).add (integrable_of_norm_le_one
        (measurable_cepsStripExit_integrand β a l y measurableSet_Iio s n)
        (norm_cepsStripExit_integrand_le β a l y _ hs n))
  · exact integrable_of_norm_le_one (measurable_cepsStripExit_integrand β a l y measurableSet_Ioi s n)
      (norm_cepsStripExit_integrand_le β a l y _ hs n)

theorem cepsStripMark_zero (ν : ProbabilityMeasure ℝ) (β a : ℝ) {l y : ℝ} (hy : y ∈ Icc 0 l)
    (s : ℂ) : cepsStripMark ν β a l y s 0 = 1 := by
  simp [cepsStripMark, krAlive_zero, kWalk_zero, indicator_of_mem hy]

/-- **S-2 (a): the strip telescoping identity** `d H = 1 - u_low - u_high`,
`d = 1 - e^{-q} E e^{s(β - aX)}`. -/
theorem CepsGapDensity.cepsStrip_telescope (hf : CepsGapDensity ν f D) (β : ℝ) {a : ℝ}
    (ha : a ≠ 0) {l y : ℝ} (hy : y ∈ Icc 0 l) {s q : ℂ} (hs : s.re = 0) (hq : 0 ≤ q.re) :
    (1 - Complex.exp (-q) * cepsStepMgf ν β a s) * cepsStripSeries ν β a l y s q =
      1 - cepsStripExit ν β a l y (Iio 0) s q - cepsStripExit ν β a l y (Ioi l) s q := by
  have hl : 0 ≤ l := hy.1.trans hy.2
  set M := cepsStepMgf ν β a s
  have hA := (hf.summable_cepsStripMark β ha l y hs hq).of_norm
  have hlow := (hf.summable_cepsStripExitTerm β ha l y (Iio 0) hs hq).of_norm
  have hhigh := (hf.summable_cepsStripExitTerm β ha l y (Ioi l) hs hq).of_norm
  have hterm : ∀ n : ℕ, Complex.exp (-q) * M * (Complex.exp (-q * n) * cepsStripMark ν β a l y s n) =
      Complex.exp (-q * ((n + 1 : ℕ) : ℂ)) * cepsStripMark ν β a l y s (n + 1) +
        Complex.exp (-q * ((n : ℂ) + 1)) * cepsStripExitTerm ν β a l y (Iio 0) s n +
        Complex.exp (-q * ((n : ℂ) + 1)) * cepsStripExitTerm ν β a l y (Ioi l) s n := by
    intro n
    have h1 := cepsStrip_step ν β a l y s n
    have h2 := cepsStrip_step_split ν β a hl y hs n
    rw [h1] at h2
    have he : Complex.exp (-q * ((n + 1 : ℕ) : ℂ)) = Complex.exp (-q) * Complex.exp (-q * n) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have he' : Complex.exp (-q * ((n : ℂ) + 1)) = Complex.exp (-q) * Complex.exp (-q * n) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [he, he']
    linear_combination (Complex.exp (-q) * Complex.exp (-q * n)) * h2
  have hs1 : HasSum (fun n : ℕ => Complex.exp (-q) * M *
      (Complex.exp (-q * n) * cepsStripMark ν β a l y s n))
      (Complex.exp (-q) * M * cepsStripSeries ν β a l y s q) := hA.hasSum.mul_left _
  have hs2 : HasSum (fun n : ℕ => Complex.exp (-q * ((n + 1 : ℕ) : ℂ)) *
      cepsStripMark ν β a l y s (n + 1)) (cepsStripSeries ν β a l y s q - 1) := by
    have := (hasSum_nat_add_iff' 1).2 hA.hasSum
    rw [Finset.sum_range_one] at this
    have h0 : Complex.exp (-q * ((0 : ℕ) : ℂ)) * cepsStripMark ν β a l y s 0 = 1 := by
      simp [cepsStripMark_zero ν β a hy s]
    rw [h0] at this
    exact this
  have hs3 := (hs2.add hlow.hasSum).add hhigh.hasSum
  simp only [← hterm] at hs3
  have heq := hs1.unique hs3
  unfold cepsStripExit
  linear_combination (-1 : ℂ) * heq

/-! ## (e) Reflection -/

theorem cepsStripMark_reflect (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (s : ℂ) (n : ℕ) :
    cepsStripMark ν (-β) (-a) l (l - y) (-s) n = cepsStripMark ν β a l y s n := by
  unfold cepsStripMark
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [krAlive_reflect, kWalk_reflect]
  congr 2
  push_cast
  ring

theorem cepsStripSeries_reflect (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (s q : ℂ) :
    cepsStripSeries ν (-β) (-a) l (l - y) (-s) q = cepsStripSeries ν β a l y s q := by
  unfold cepsStripSeries
  simp_rw [cepsStripMark_reflect]

theorem cepsStripExitTerm_reflect (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (E : Set ℝ) (s : ℂ)
    (n : ℕ) :
    cepsStripExitTerm ν (-β) (-a) l (l - y) E (-s) n =
      cepsStripExitTerm ν β a l y ((fun x => l - x) ⁻¹' E) s n := by
  unfold cepsStripExitTerm
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [krAlive_reflect, kWalk_reflect]
  have hind : E.indicator (fun _ => (1 : ℂ)) (l - kWalk y β a g (n + 1)) =
      ((fun x => l - x) ⁻¹' E).indicator (fun _ => (1 : ℂ)) (kWalk y β a g (n + 1)) := by
    by_cases h : l - kWalk y β a g (n + 1) ∈ E
    · rw [indicator_of_mem h, indicator_of_mem (show kWalk y β a g (n + 1) ∈
        (fun x => l - x) ⁻¹' E from h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (show kWalk y β a g (n + 1) ∉
        (fun x => l - x) ⁻¹' E from h)]
  rw [hind]
  congr 2
  push_cast
  ring

theorem preimage_reflect_Ioi (l : ℝ) : (fun x : ℝ => l - x) ⁻¹' Ioi l = Iio 0 := by
  ext x; simp

theorem preimage_reflect_Iio (l : ℝ) : (fun x : ℝ => l - x) ⁻¹' Iio 0 = Ioi l := by
  ext x; simp

/-- **S-2 (e): reflection.** The high exit of the reflected strip is the low exit. -/
theorem cepsStripExit_reflect_high (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (s q : ℂ) :
    cepsStripExit ν (-β) (-a) l (l - y) (Ioi l) (-s) q = cepsStripExit ν β a l y (Iio 0) s q := by
  unfold cepsStripExit
  simp_rw [cepsStripExitTerm_reflect, preimage_reflect_Ioi]

/-- **S-2 (e): reflection.** The low exit of the reflected strip is the high exit. -/
theorem cepsStripExit_reflect_low (ν : ProbabilityMeasure ℝ) (β a l y : ℝ) (s q : ℂ) :
    cepsStripExit ν (-β) (-a) l (l - y) (Iio 0) (-s) q = cepsStripExit ν β a l y (Ioi l) s q := by
  unfold cepsStripExit
  simp_rw [cepsStripExitTerm_reflect, preimage_reflect_Iio]

theorem cepsStepMgf_reflect (ν : ProbabilityMeasure ℝ) (β a : ℝ) (s : ℂ) :
    cepsStepMgf ν (-β) (-a) (-s) = cepsStepMgf ν β a s := by
  unfold cepsStepMgf
  congr 1
  funext x
  congr 1
  push_cast
  ring

/-! ## The strip of theorem (E) -/

/-- The strip entrance `H_t` of theorem (E) is the top-started `Y_μ`-strip: the outer walk
`V = S_n - n(1+μ)` from `0` in `[0, l]` with mark `e^{-tV}`. -/
theorem cepsStripEntrance_eq (ν : ProbabilityMeasure ℝ) (t : ℂ) (μ : ℝ) (q : ℂ) (l : ℝ) :
    cepsStripEntrance ν t μ q l = cepsStripSeries ν (-(1 + μ)) (-1) l 0 (-t) q := by
  unfold cepsStripEntrance cepsStripSeries cepsStripMark cepsStripTerm
  congr 1
  funext n
  congr 2
  funext g
  rw [sub_zero, neg_mul]

/-- The bottom-started `Y_μ`-strip (step `1 + μ - X` from `0`) is the reflection of the top-started
one: `H^{bot}_t = H^{top}_{-t}` with the high and low exits exchanged. -/
theorem cepsStrip_bottom_eq_reflect (ν : ProbabilityMeasure ℝ) (μ l : ℝ) (s q : ℂ) :
    cepsStripSeries ν (1 + μ) 1 l 0 s q = cepsStripSeries ν (-(1 + μ)) (-1) l l (-s) q := by
  have := cepsStripSeries_reflect ν (1 + μ) 1 l 0 s q
  rw [sub_zero] at this
  exact this.symm

end

end PGM
