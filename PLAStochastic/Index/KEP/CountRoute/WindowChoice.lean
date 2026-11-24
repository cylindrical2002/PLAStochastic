import PLAStochastic.Index.KEP.CountRoute.WindowBridge
import PLAStochastic.Index.KEP.ReferenceScale.GammaWeighted

/-!
# Choosing the window: exponential Poisson block tails and span quantiles

Source: `pgm-analysis/research/2026-09-28-kep-additive/poisson-bridge.md`, §5–§6
(formulas (11)–(14)).

The bridge `WindowBridge` leaves two Poisson window conditions.  This file reduces them to
statements about the first layer-`L` block of the Poisson window model alone:

* **Tail (PT).**  If the probability that the block is not completed inside a window of
  integrated intensity `M p ≥ m_L` decays like `A exp (-c · M p / m_L)`
  (`KepPoissonExpTail`), then the window mass `p = √(m_L / M)` gives
  `(√τ + p)² ≤ K m_L / (M + 1)` (`kepPoissonTail_of_expTail`).  The note's choice (11) with
  `p = K₀ (1 + log r) / r` yields the sharper `(1 + log r)² / r²`; since `KepWindowTail` only
  asks for `K m_L / n`, the square-root window is used here to avoid logarithms.
* **Quantile (14).**  If the block is not completed inside the window of mass `c m_L` with
  probability at least `p₀` (`KepPoissonSpanQuantile`), then the base-rank span exceeds
  `⌊a m_L⌋` for every `a < c` with probability at least `p₀ - exp (-gap(a, c) m_L)`
  (`poissonWindow_real_tailEvent_le` and the Poisson Chernoff bound
  `poissonMeasure_real_lt_le`).  This gives `KepPoissonQuantile` once the constants satisfy
  `(√p + c / Bc)² + exp (-4 gap(a, c)) ≤ p₀` (`kepPoissonQuantile_of_spanQuantile`), using
  `m_L ≥ 4` from the reference scale.

Both reductions only use event inclusions inside the Poisson window; the Poisson block tail
and span quantile remain the open inputs.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Renyi
open scoped ENNReal unitInterval NNReal Nat

/-! ## Poisson lower tail -/

/-- Exponential Chernoff bound for the lower tail of a Poisson variable. -/
theorem poissonMeasure_real_lt_le (r : ℝ≥0) (g : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    (poissonMeasure r).real {k | k < g} ≤
      Real.exp (θ * g - r + r * Real.exp (-θ)) := by
  set f : ℕ → ℝ := fun k => Real.exp (θ * g - r) * (((r : ℝ) * Real.exp (-θ)) ^ k / k !)
  have hf : ∀ k : ℕ, f k = Real.exp (-r) * (r : ℝ) ^ k / k ! * Real.exp (θ * (g - k)) := by
    intro k
    simp only [f]
    rw [mul_pow, ← Real.exp_nat_mul]
    have h1 : Real.exp (θ * g - r) * Real.exp ((k : ℝ) * -θ) =
        Real.exp (-r) * Real.exp (θ * (g - k)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc Real.exp (θ * g - r) * ((r : ℝ) ^ k * Real.exp ((k : ℝ) * -θ) / k !)
        = (Real.exp (θ * g - r) * Real.exp ((k : ℝ) * -θ)) * ((r : ℝ) ^ k / k !) := by ring
      _ = _ := by rw [h1]; ring
  have hsum : HasSum f (Real.exp (θ * g - r + r * Real.exp (-θ))) := by
    rw [Real.exp_add]
    have := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp (-θ))).mul_left
      (Real.exp (θ * g - r))
    rwa [← Real.exp_eq_exp_ℝ] at this
  have hnn : ∀ k, 0 ≤ f k := fun k => by rw [hf]; positivity
  have hset : {k : ℕ | k < g} = ⋃ k ∈ Finset.range g, {k} := by
    ext k
    simp
  rw [hset, measureReal_biUnion_finset (fun i _ j _ hij => Set.disjoint_singleton.2 hij)
    (fun _ _ => measurableSet_singleton _)]
  simp_rw [poissonMeasure_real_singleton]
  calc ∑ k ∈ Finset.range g, Real.exp (-r) * (r : ℝ) ^ k / k !
      ≤ ∑ k ∈ Finset.range g, f k := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [hf]
        have hk' : (k : ℝ) ≤ g := by exact_mod_cast (Finset.mem_range.1 hk).le
        have : 1 ≤ Real.exp (θ * (g - k)) := by
          have := Real.add_one_le_exp (θ * (g - k))
          nlinarith [mul_nonneg hθ (sub_nonneg.2 hk')]
        exact le_mul_of_one_le_right (by positivity) this
    _ ≤ _ := sum_le_hasSum _ (fun k _ => hnn k) hsum

/-- The large-deviation rate of a Poisson variable of mean `c m` falling below `a m`. -/
def poissonRateGap (a c : ℝ) : ℝ := c - a - a * Real.log (c / a)

theorem poissonRateGap_pos {a c : ℝ} (ha : 0 < a) (hac : a < c) : 0 < poissonRateGap a c := by
  have hc : 0 < c := ha.trans hac
  have h1 : 1 < c / a := (one_lt_div ha).2 hac
  have hlog := Real.log_lt_sub_one_of_pos (by positivity) h1.ne'
  have : a * Real.log (c / a) < a * (c / a - 1) := mul_lt_mul_of_pos_left hlog ha
  rw [mul_sub, mul_div_cancel₀ _ ha.ne', mul_one] at this
  unfold poissonRateGap
  linarith

/-- Optimized Chernoff bound: a Poisson variable of mean `c m` is below `a m` with probability
    at most `exp (-gap(a, c) m)`. -/
theorem poissonMeasure_real_lt_le_exp_neg {r : ℝ≥0} {a c : ℝ} (ha : 0 < a) (hac : a < c)
    {m : ℝ} (hr : (r : ℝ) = c * m) {g : ℕ} (hg : (g : ℝ) ≤ a * m) :
    (poissonMeasure r).real {k | k < g} ≤ Real.exp (-(poissonRateGap a c * m)) := by
  have hc : 0 < c := ha.trans hac
  have h1 : 1 < c / a := (one_lt_div ha).2 hac
  set θ := Real.log (c / a) with hθ
  have hθ0 : 0 ≤ θ := (Real.log_pos h1).le
  refine (poissonMeasure_real_lt_le r g hθ0).trans (Real.exp_le_exp.2 ?_)
  rw [hr, Real.exp_neg, hθ, Real.exp_log (by positivity), inv_div]
  have : c * m * (a / c) = a * m := by field_simp
  rw [this]
  have := mul_le_mul_of_nonneg_left hg hθ0
  unfold poissonRateGap
  nlinarith

/-! ## From the censored block event to the base-rank span (14) -/

section Span

variable {Q : ℝ → ℝ} {u eps : ℝ}

/-- The window keys are the anchored keys of the window configuration truncated at `N`. -/
theorem winKeys_eq_add_pairKeys (Q : ℝ → ℝ) (u : ℝ) (x : ℕ → ℝ) (N : ℕ) {t : ℕ} (ht : t ≤ N) :
    winKeys Q u x t = Q u + pairKeys (anchPairsW Q u (fun i : Fin N => x i)) t := by
  rw [pairKeys_anchPairsW' Q u _ t ht, add_sub_cancel]
  unfold winKeys padPos anchPos
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · simp
  · rw [if_neg ht0.ne', dif_pos ⟨ht0, ht⟩]

theorem epHeight_winKeys_le_iff (heps : 1 / 2 ≤ eps) {L : ℕ} (hL : 1 ≤ L) (x : ℕ → ℝ) (N : ℕ)
    {n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N + 1) :
    epHeight eps (winKeys Q u x) n ≤ L ↔
      n ≤ layerPivot eps (anchPairsW Q u (fun i : Fin N => x i)) L 1 := by
  rw [epHeight_congr (p' := fun t => Q u + pairKeys (anchPairsW Q u (fun i : Fin N => x i)) t)
    fun i hi => winKeys_eq_add_pairKeys Q u x N (by omega)]
  exact epHeight_le_iff_layerPivot heps (fun _ => rfl) (allLayersFinite_anchPairsW eps Q u _)
    (Q u) hn1 hL

/-- Not completing the block inside the window, with at least `g` window points, puts the
    second layer-`L` pivot beyond base rank `g`. -/
theorem tailEvent_inter_subset_quantEvent (heps : 1 / 2 ≤ eps) {L : ℕ} (hL : 1 ≤ L) (g : ℕ) :
    tailEvent eps Q u L ∩ {c | g ≤ c.1} ⊆ quantEvent eps Q u L g := by
  rintro ⟨N, x⟩ ⟨hT, hg⟩
  change g ≤ N at hg
  refine ⟨hg, ?_⟩
  change epHeight eps (winKeys Q u x) (N + 1) ≤ L at hT
  change epHeight eps (winKeys Q u x) (g + 1) ≤ L
  rw [epHeight_winKeys_le_iff heps hL x N (by omega) le_rfl] at hT
  rw [epHeight_winKeys_le_iff heps hL x N (by omega) (by omega)]
  omega

theorem poissonWindow_real_fst_lt (M : ℕ) (p : I) (g : ℕ) :
    (poissonWindow M p).real {c | c.1 < g} =
      (poissonMeasure (binomialPoissonRate M p)).real {k | k < g} := by
  have : {c : ℕ × (ℕ → ℝ) | c.1 < g} = Prod.fst ⁻¹' Iio g := rfl
  rw [measureReal_def, measureReal_def, this, ← Measure.fst_apply measurableSet_Iio,
    poissonWindow, Measure.fst_compProd]
  rfl

/-- **(14).**  The censored block probability is at most the span-quantile probability plus the
    Poisson lower tail of the window count. -/
theorem poissonWindow_real_tailEvent_le (heps : 1 / 2 ≤ eps) {L : ℕ} (hL : 1 ≤ L) (M : ℕ)
    (p : I) (g : ℕ) :
    (poissonWindow M p).real (tailEvent eps Q u L) ≤
      (poissonWindow M p).real (quantEvent eps Q u L g) +
        (poissonMeasure (binomialPoissonRate M p)).real {k | k < g} := by
  rw [← poissonWindow_real_fst_lt]
  calc (poissonWindow M p).real (tailEvent eps Q u L)
      ≤ (poissonWindow M p).real (quantEvent eps Q u L g ∪ {c | c.1 < g}) := by
        apply measureReal_mono ?_ (measure_ne_top _ _)
        intro c hc
        by_cases hg : g ≤ c.1
        · exact Or.inl (tailEvent_inter_subset_quantEvent heps hL g ⟨hc, hg⟩)
        · exact Or.inr (not_le.1 hg)
    _ ≤ _ := measureReal_union_le _ _

end Span

/-! ## The tail condition from an exponential block tail (PT), (11)–(12) -/

/-- **(PT) in window form.**  In the Poisson window of integrated intensity `M p ≥ m_L`, the
    first layer-`L` block is not completed inside the window with probability at most
    `A exp (-c · M p / m_L)`. -/
def KepPoissonExpTail (Q : ℝ → ℝ) (eps0 A c : ℝ) : Prop :=
  ∀ eps, eps0 ≤ eps → ∀ L, 1 ≤ L → ∀ M : ℕ, ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ p : I, 0 < (p : ℝ) → (p : ℝ) ≤ 1 / 2 → kepReferenceSpan eps L ≤ M * p →
      (poissonWindow M p).real (tailEvent eps Q u L) ≤
        A * Real.exp (-(c * (M * p / kepReferenceSpan eps L)))

theorem kepPoissonTail_of_expTail {Q : ℝ → ℝ} {eps0 A c : ℝ}
    (heps0 : kepReferenceClassicalThreshold ≤ eps0) (hA : 0 ≤ A) (hc : 0 < c)
    (hT : KepPoissonExpTail Q eps0 A c) :
    KepPoissonTail Q eps0 8 0 (8 * A / c ^ 2 + 4) := by
  intro eps heps L hL M hlt u hu0 hu1
  have hm4 : 4 ≤ kepReferenceSpan eps L := kepReferenceSpan_ge_four (heps0.trans heps) hL
  set m := kepReferenceSpan eps L with hm
  have hm0 : 0 < m := by linarith
  rw [Real.rpow_zero, mul_one] at hlt
  push_cast at hlt
  have hM : 4 * m ≤ M := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hdiv : 0 < m / M := div_pos hm0 hMpos
  set q : ℝ := Real.sqrt (m / M) with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hdiv
  have hq_sq : q ^ 2 = m / M := Real.sq_sqrt hdiv.le
  have hq_le : q ≤ 1 / 2 := by
    rw [hq, show (1 / 2 : ℝ) = Real.sqrt ((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by rw [div_le_iff₀ hMpos]; linarith)
  have hq1 : q ≤ 1 := hq_le.trans (by norm_num)
  refine ⟨⟨q, hq0.le, hq1⟩, hq0, hq_le, ?_⟩
  set s : ℝ := M * q / m with hs
  have hs_sq : s ^ 2 = M / m := by
    rw [hs, div_pow, mul_pow, hq_sq]
    field_simp
  have hs0 : 0 ≤ s := by positivity
  have hs_pos : 0 < s := by
    rcases hs0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, zero_pow two_ne_zero] at hs_sq
      exact absurd hs_sq.symm (div_pos hMpos hm0).ne'
  have hmass : m ≤ M * q := by
    have h1 : 1 ≤ s := by
      rw [← Real.sqrt_sq hs0, ← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by rw [hs_sq, le_div_iff₀ hm0]; linarith)
    rw [hs, le_div_iff₀ hm0] at h1
    linarith
  have hτ := hT eps heps L hL M u hu0 hu1 ⟨q, hq0.le, hq1⟩ hq0 hq_le hmass
  simp only at hτ
  have hexp : Real.exp (-(c * s)) ≤ 2 * m / (c ^ 2 * M) := by
    have h1 := Real.quadratic_le_exp_of_nonneg (mul_nonneg hc.le hs0)
    have h2 : (c * s) ^ 2 / 2 ≤ Real.exp (c * s) := by nlinarith [mul_nonneg hc.le hs0]
    have h3 : 0 < (c * s) ^ 2 / 2 := by positivity
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    calc (2 * m / (c ^ 2 * M))⁻¹ = (c * s) ^ 2 / 2 := by
          rw [mul_pow, hs_sq]
          field_simp
      _ ≤ Real.exp (c * s) := h2
  set τ := (poissonWindow M ⟨q, hq0.le, hq1⟩).real (tailEvent eps Q u L) with hτdef
  have hτ' : τ ≤ A * (2 * m / (c ^ 2 * M)) :=
    hτ.trans (mul_le_mul_of_nonneg_left hexp hA)
  have hτnn : 0 ≤ τ := measureReal_nonneg
  have hsq : (Real.sqrt τ + q) ^ 2 ≤ 2 * τ + 2 * q ^ 2 := by
    have := Real.sq_sqrt hτnn
    nlinarith [sq_nonneg (Real.sqrt τ - q)]
  have hM1 : (M : ℝ) + 1 ≤ 2 * M := by linarith
  have hpos : 0 ≤ (4 * A / c ^ 2 + 2) * m := by positivity
  calc (Real.sqrt τ + q) ^ 2 ≤ 2 * τ + 2 * q ^ 2 := hsq
    _ ≤ 2 * (A * (2 * m / (c ^ 2 * M))) + 2 * (m / M) := by rw [hq_sq]; gcongr
    _ = (4 * A / c ^ 2 + 2) * m / M := by field_simp; ring
    _ ≤ (8 * A / c ^ 2 + 4) * m / ((M + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_le_div_iff₀ hMpos (by positivity),
        show (8 * A / c ^ 2 + 4) = 2 * (4 * A / c ^ 2 + 2) by ring]
      calc (4 * A / c ^ 2 + 2) * m * (M + 1)
          ≤ (4 * A / c ^ 2 + 2) * m * (2 * M) := mul_le_mul_of_nonneg_left hM1 hpos
        _ = 2 * (4 * A / c ^ 2 + 2) * m * M := by ring

/-! ## The quantile condition from a span quantile, (14) -/

/-- **Poisson span quantile.**  In the Poisson window of integrated intensity `c m_L`, for
    `m ≥ ⌈Bc eps^γ m_L⌉` remaining keys and every anchor, the first layer-`L` block is not
    completed inside the window with probability at least `p₀`. -/
def KepPoissonSpanQuantile (Q : ℝ → ℝ) (eps0 c p0 Bc γ : ℝ) : Prop :=
  ∀ eps, eps0 ≤ eps → ∀ L, 1 ≤ L → ∀ m : ℕ, ⌈Bc * eps ^ γ * kepReferenceSpan eps L⌉₊ ≤ m →
    ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ q : I, (q : ℝ) = c * kepReferenceSpan eps L / m →
      p0 ≤ (poissonWindow m q).real (tailEvent eps Q u L)

theorem kepPoissonQuantile_of_spanQuantile {Q : ℝ → ℝ} {eps0 a c p0 p Bc γ : ℝ}
    (heps0 : kepReferenceClassicalThreshold ≤ eps0) (ha : 0 < a) (hac : a < c) (hγ : 0 ≤ γ)
    (hBc : 2 * c ≤ Bc)
    (hpar : (Real.sqrt p + c / Bc) ^ 2 + Real.exp (-(poissonRateGap a c * 4)) ≤ p0)
    (hS : KepPoissonSpanQuantile Q eps0 c p0 Bc γ) :
    KepPoissonQuantile Q eps0 a p Bc γ := by
  intro eps heps L hL m hm u hu0 hu1
  have hthr : kepReferenceClassicalThreshold ≤ eps := heps0.trans heps
  have heps2 : 2 ≤ eps := (le_max_left _ _).trans hthr
  have heps' : 1 / 2 ≤ eps := by linarith
  have hm4 : 4 ≤ kepReferenceSpan eps L := kepReferenceSpan_ge_four hthr hL
  set mL := kepReferenceSpan eps L with hmL
  have hmL0 : 0 < mL := by linarith
  have hc : 0 < c := ha.trans hac
  have hBc0 : 0 < Bc := by linarith
  have hpow : 1 ≤ eps ^ γ := Real.one_le_rpow (by linarith) hγ
  have hmR : Bc * eps ^ γ * mL ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have hm_ge : Bc * mL ≤ m := by
    have : Bc * mL ≤ Bc * eps ^ γ * mL := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hmL0.le hpow) hBc0.le
    linarith
  have hmpos : (0 : ℝ) < m := by nlinarith
  set q : ℝ := c * mL / m with hq
  have hq0 : 0 < q := by positivity
  have hq_le : q ≤ c / Bc := by
    rw [hq, div_le_div_iff₀ hmpos hBc0]
    nlinarith
  have hq_half : q ≤ 1 / 2 := hq_le.trans (by rw [div_le_iff₀ hBc0]; linarith)
  have hq1 : q ≤ 1 := hq_half.trans (by norm_num)
  refine ⟨⟨q, hq0.le, hq1⟩, hq0, hq_half, ?_⟩
  set g := ⌊a * mL⌋₊ with hg
  have hS' := hS eps heps L hL m hm u hu0 hu1 ⟨q, hq0.le, hq1⟩ rfl
  have hlow := poissonWindow_real_tailEvent_le (Q := Q) (u := u) heps' hL m ⟨q, hq0.le, hq1⟩ g
  have hrate : ((binomialPoissonRate m ⟨q, hq0.le, hq1⟩ : ℝ≥0) : ℝ) = c * mL := by
    change (m : ℝ) * q = c * mL
    rw [hq]
    field_simp
  have hcher := poissonMeasure_real_lt_le_exp_neg ha hac hrate
    (Nat.floor_le (by positivity) : (g : ℝ) ≤ a * mL)
  have hgap := poissonRateGap_pos ha hac
  have hexp : Real.exp (-(poissonRateGap a c * mL)) ≤ Real.exp (-(poissonRateGap a c * 4)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hfinal : (Real.sqrt p + q) ^ 2 ≤
      (poissonWindow m ⟨q, hq0.le, hq1⟩).real (quantEvent eps Q u L g) := by
    calc (Real.sqrt p + q) ^ 2 ≤ (Real.sqrt p + c / Bc) ^ 2 := by
          gcongr
      _ ≤ _ := by linarith
  exact (Real.le_sqrt (by positivity) measureReal_nonneg).2 hfinal

/-! ## The additive height from Poisson block statements alone -/

/-- **Additive height for general Model K from (PT) and the Poisson span quantile.**  Both
    inputs are statements about the first layer-`L` block of the Poisson window model at the
    quantile keys; the finite-sample side is entirely bridged. -/
theorem H_EP_additive_kKeys_of_poissonBlock {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ} (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {eps0 a c p0 p Bc γ : ℝ} (heps0 : kepReferenceClassicalThreshold ≤ eps0) (ha : 0 < a)
    (hac : a < c) (hp : 0 < p) (hBc : 2 * c ≤ Bc) (hγ : 0 ≤ γ)
    (hpar : (Real.sqrt p + c / Bc) ^ 2 + Real.exp (-(poissonRateGap a c * 4)) ≤ p0)
    (hS : KepPoissonSpanQuantile (quantK f A B) eps0 c p0 Bc γ)
    {A0 c0 : ℝ} (hA0 : 0 ≤ A0) (hc0 : 0 < c0) (hT : KepPoissonExpTail (quantK f A B) eps0 A0 c0) :
    ∃ eps1 C : ℝ, ∀ eps, eps1 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |(∫ ω, (epHeight eps (kKeys X n ω) n : ℝ) ∂P) -
        Real.log n / Real.log (gepC eps)| ≤ C := by
  have heps2 : 2 ≤ eps0 := (le_max_left _ _).trans heps0
  have hc : 0 < c := ha.trans hac
  exact H_EP_additive_kKeys_of_poissonWindow hf hXm hX hind (by linarith) ha hp (by linarith) hγ
    (kepPoissonQuantile_of_spanQuantile heps0 ha hac hγ hBc hpar hS) (by norm_num) le_rfl
    (by positivity) (kepPoissonTail_of_expTail heps0 hA0 hc0 hT)

end

end PGM
