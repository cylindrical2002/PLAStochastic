import PLAStochastic.Index.KEP.OrderStatisticReset
import PLAStochastic.Index.Model.ExpConcentration
import PLAStochastic.ForMathlib.Probability.OrderStatistics.Renyi
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Good anchors: the uniform `N⁻¹` reset coefficient

Source: `proofs/proofK_reset.tex`, `lem:Kresetcoef`.  Throughout `c = 1/6`.

* **Binomial Chernoff** (`countIn_upper_tail`, `countIn_lower_tail`).  For `N` iid coordinates
  with law `ν` and `q = ν(A)`, the count `#{i : uᵢ ∈ A}` has mgf `(1 + q (eᵗ - 1))ᴺ`
  (`mgf_countIn`), bounded by `exp(N q (eᵗ - 1))`.
* **Order-statistic window** (`orderLaw_upper_window`, `orderLaw_lower_window`).  Under
  `Renyi.orderLaw N`, for `r < N` and `d = N - r`:
  `P(1 - V_r > 2d/N) ≤ exp(-d/6)` and `P(1 - V_r < d/(2N)) ≤ exp(-d/6)`.  Via the sorted uniform
  representation (`orderLaw_eq_map_sortVec`), `1 - V_r > x` forces at most `d - 1` uniforms into
  `[1 - x, 1]` (Binomial `(N, 2d/N)`, mean `2d`; the event is null when `2d/N ≥ 1`), and
  `1 - V_r < x` forces at least `d` of them there (Binomial `(N, d/(2N))`, mean `d/2`).
  Chernoff at `t = ∓1/2` with `e^{-1/2} ≤ 2/3`, `e^{1/2} ≤ 5/3`.
* **Good-anchor event** (`goodAnchors`, `orderLaw_compl_goodAnchors_le`).
  `P((goodAnchors N D)ᶜ) ≤ 2 N exp(-D/6)`; for `D = ⌈K log N⌉₊` with `K ≥ 6 (p + 1)` this is
  `≤ 2 N^{-p}` (`orderLaw_real_compl_goodAnchors_log_le`).
* **Gamma total** (`sum_exp_lower_tail`, `sum_exp_upper_tail`, `sum_exp_window`; block form
  `expSum_window`).  For `d` independent `Exp(1)` variables with sum `Σ`,
  `P(Σ ≤ d/2) ≤ exp(-d/6)` (Chernoff at `θ = -1`, `e^{2/3} ≤ 2`) and
  `P(Σ ≥ 2d) ≤ exp(-d/6)` (`θ = 1/2`, `2 ≤ e^{5/6}`).
* **Reset coefficient** (`reset_coef_le`, `reset_coef_le_of_mem_goodAnchors`).  Deterministically,
  `d/(2N) ≤ 1 - u ≤ 2d/N` and `d/2 ≤ Σ` give `(1 - u)/Σ ≤ 4/N`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace PGM

/-! ## Numerical constants -/

theorem exp_half_le_five_thirds : exp (1 / 2 : ℝ) ≤ 5 / 3 := by
  have h := Real.exp_one_lt_d9
  have h2 : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2 : ℝ)]

theorem exp_neg_half_le_two_thirds : exp (-(1 / 2) : ℝ) ≤ 2 / 3 := by
  rw [Real.exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
  have h := Real.add_one_le_exp (1 / 2 : ℝ)
  norm_num at h ⊢
  linarith

theorem exp_two_thirds_le_two : exp (2 / 3 : ℝ) ≤ 2 := by
  have h := Real.log_two_gt_d9
  calc exp (2 / 3) ≤ exp (log 2) := exp_le_exp.2 (by norm_num at h ⊢; linarith)
    _ = 2 := exp_log (by norm_num)

theorem two_le_exp_five_sixths : 2 ≤ exp (5 / 6 : ℝ) := by
  have h := Real.log_two_lt_d9
  calc (2 : ℝ) = exp (log 2) := (exp_log (by norm_num)).symm
    _ ≤ exp (5 / 6) := exp_le_exp.2 (by norm_num at h ⊢; linarith)

/-! ## Chernoff bounds for counts of iid coordinates -/

section Count

variable {n : ℕ} {ν : Measure ℝ} [IsProbabilityMeasure ν] {A : Set ℝ}

/-- The number of coordinates of `u` that lie in `A`. -/
def countIn (A : Set ℝ) (u : Fin n → ℝ) : ℝ := ∑ i, A.indicator 1 (u i)

theorem measurable_countIn (hA : MeasurableSet A) : Measurable (countIn (n := n) A) := by
  unfold countIn
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_one.indicator hA).comp (measurable_pi_apply i)

theorem countIn_nonneg (A : Set ℝ) (u : Fin n → ℝ) : 0 ≤ countIn A u :=
  Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem countIn_le (A : Set ℝ) (u : Fin n → ℝ) : countIn A u ≤ n := by
  unfold countIn
  calc ∑ i, A.indicator 1 (u i) ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => Set.indicator_le_self' (fun _ _ => zero_le_one) _
    _ = n := by simp

theorem exp_mul_indicator_one (t x : ℝ) :
    exp (t * A.indicator 1 x) = 1 + (exp t - 1) * A.indicator 1 x := by
  by_cases hx : x ∈ A <;> simp [hx]

theorem integral_exp_mul_indicator (hA : MeasurableSet A) (t : ℝ) :
    ∫ x, exp (t * A.indicator 1 x) ∂ν = 1 + ν.real A * (exp t - 1) := by
  simp_rw [exp_mul_indicator_one]
  have hint : Integrable (A.indicator (1 : ℝ → ℝ)) ν := (integrable_const (1 : ℝ)).indicator hA
  rw [integral_add (integrable_const _) (hint.const_mul _), integral_const_mul,
    integral_indicator_one hA]
  simp [mul_comm]

/-- The moment generating function of a Binomial count:
`E[exp(t · #{i : uᵢ ∈ A})] = (1 + ν(A) (eᵗ - 1))ⁿ`. -/
theorem mgf_countIn (hA : MeasurableSet A) (t : ℝ) :
    mgf (countIn A) (Measure.pi fun _ : Fin n => ν) t = (1 + ν.real A * (exp t - 1)) ^ n := by
  have hind : iIndepFun (fun (i : Fin n) (u : Fin n → ℝ) => A.indicator 1 (u i))
      (Measure.pi fun _ : Fin n => ν) :=
    iIndepFun_pi (X := fun _ => A.indicator (1 : ℝ → ℝ)) fun _ =>
      (measurable_one.indicator hA).aemeasurable
  have hsum : countIn (n := n) A = ∑ i, fun u : Fin n → ℝ => A.indicator 1 (u i) := by
    funext u
    simp [countIn, Finset.sum_apply]
  rw [hsum, hind.mgf_sum₀ (fun i => ((measurable_one.indicator hA).comp
    (measurable_pi_apply i)).aemeasurable)]
  have hi : ∀ i : Fin n, mgf (fun u : Fin n → ℝ => A.indicator 1 (u i))
      (Measure.pi fun _ : Fin n => ν) t = 1 + ν.real A * (exp t - 1) := by
    intro i
    have hX : HasLaw (fun u : Fin n → ℝ => u i) ν (Measure.pi fun _ : Fin n => ν) :=
      (measurePreserving_eval (μ := fun _ : Fin n => ν) i).hasLaw
    rw [mgf, ← integral_exp_mul_indicator hA t]
    exact hX.integral_comp (f := fun x => exp (t * A.indicator 1 x))
      (((measurable_one.indicator hA).const_mul t).exp).aestronglyMeasurable
  simp [hi]

theorem integrable_exp_mul_countIn (hA : MeasurableSet A) (t : ℝ) :
    Integrable (fun u => exp (t * countIn A u)) (Measure.pi fun _ : Fin n => ν) := by
  refine Integrable.of_bound (((measurable_countIn hA).const_mul t).exp).aestronglyMeasurable
    (exp (|t| * n)) (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  refine exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul, abs_of_nonneg (countIn_nonneg A u)]
  exact mul_le_mul_of_nonneg_left (countIn_le A u) (abs_nonneg t)

theorem mgf_countIn_le (hA : MeasurableSet A) (t : ℝ) :
    mgf (countIn A) (Measure.pi fun _ : Fin n => ν) t ≤ exp (n * ν.real A * (exp t - 1)) := by
  rw [mgf_countIn hA]
  have hq0 : 0 ≤ ν.real A := measureReal_nonneg
  have hq1 : ν.real A ≤ 1 := measureReal_le_one
  have h0 : 0 ≤ 1 + ν.real A * (exp t - 1) := by nlinarith [exp_pos t]
  calc (1 + ν.real A * (exp t - 1)) ^ n ≤ exp (ν.real A * (exp t - 1)) ^ n := by
        gcongr
        linarith [Real.add_one_le_exp (ν.real A * (exp t - 1))]
    _ = exp (n * ν.real A * (exp t - 1)) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- Chernoff upper tail for a Binomial count. -/
theorem countIn_upper_tail (hA : MeasurableSet A) (k : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => ν).real {u | k ≤ countIn A u} ≤
      exp (-t * k + n * ν.real A * (exp t - 1)) := by
  refine (measure_ge_le_exp_mul_mgf k ht (integrable_exp_mul_countIn hA t)).trans ?_
  rw [Real.exp_add]
  exact mul_le_mul_of_nonneg_left (mgf_countIn_le hA t) (exp_pos _).le

/-- Chernoff lower tail for a Binomial count. -/
theorem countIn_lower_tail (hA : MeasurableSet A) (k : ℝ) {t : ℝ} (ht : t ≤ 0) :
    (Measure.pi fun _ : Fin n => ν).real {u | countIn A u ≤ k} ≤
      exp (-t * k + n * ν.real A * (exp t - 1)) := by
  refine (measure_le_le_exp_mul_mgf k ht (integrable_exp_mul_countIn hA t)).trans ?_
  rw [Real.exp_add]
  exact mul_le_mul_of_nonneg_left (mgf_countIn_le hA t) (exp_pos _).le

end Count

/-! ## The order-statistic window -/

section Order

open Renyi

variable {n : ℕ}

instance isProbabilityMeasure_restrict_Icc_zero_one :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- `orderLaw N` is the image of the product of `N` uniform `[0, 1]` laws under sorting. -/
theorem orderLaw_eq_map_sortVec (N : ℕ) :
    orderLaw N = (Measure.pi fun _ : Fin N => volume.restrict (Icc (0 : ℝ) 1)).map sortVec :=
  (map_sortVec_uniform_eq_orderLaw (U := fun i (u : Fin N → ℝ) => u i)
    (fun i => (measurePreserving_eval (μ := fun _ : Fin N => volume.restrict (Icc (0 : ℝ) 1))
      i).hasLaw)
    (iIndepFun_pi (X := fun _ => (id : ℝ → ℝ)) fun _ => aemeasurable_id)).symm

/-- Sorting does not change a count. -/
theorem countIn_sortVec (A : Set ℝ) (u : Fin n → ℝ) : countIn A (sortVec u) = countIn A u :=
  Equiv.sum_comp (Tuple.sort u) (fun i => A.indicator 1 (u i))

/-- If the `r`-th entry of a monotone tuple is `< t`, at most `n - 1 - r` entries are `≥ t`. -/
theorem countIn_Ici_le_of_lt {w : Fin n → ℝ} (hw : Monotone w) {r : Fin n} {t : ℝ}
    (hr : w r < t) : countIn (Ici t) w ≤ ((n - 1 - r : ℕ) : ℝ) := by
  unfold countIn
  calc ∑ j, (Ici t).indicator 1 (w j) ≤ ∑ j, if r < j then (1 : ℝ) else 0 := by
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs with hj
        · exact Set.indicator_le_self' (fun _ _ => zero_le_one) _
        · have hlt : w j < t := lt_of_le_of_lt (hw (not_lt.1 hj)) hr
          rw [Set.indicator_of_notMem (by simpa using hlt)]
    _ = ((n - 1 - r : ℕ) : ℝ) := by
        rw [Finset.sum_boole, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]

/-- If the `r`-th entry of a monotone tuple is `> t`, at least `n - r` entries are `≥ t`. -/
theorem countIn_Ici_ge_of_lt {w : Fin n → ℝ} (hw : Monotone w) {r : Fin n} {t : ℝ}
    (hr : t < w r) : ((n - r : ℕ) : ℝ) ≤ countIn (Ici t) w := by
  unfold countIn
  calc ((n - r : ℕ) : ℝ) = ∑ j, if r ≤ j then (1 : ℝ) else 0 := by
        rw [Finset.sum_boole, Finset.filter_le_eq_Ici, Fin.card_Ici]
    _ ≤ ∑ j, (Ici t).indicator 1 (w j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs with hj
        · rw [Set.indicator_of_mem (show w j ∈ Ici t from (hr.trans_le (hw hj)).le)]
          rfl
        · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem uniform_real_Ici {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (Ici (1 - x)) = x := by
  have hset : Ici (1 - x) ∩ Icc 0 1 = Icc (1 - x) 1 := by
    ext y
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨h, -, h'⟩
      exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, by linarith, h'⟩
  rw [measureReal_def, Measure.restrict_apply measurableSet_Ici, hset, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

/-- **Upper window.**  With `d = N - r`, `P(1 - V_(r) > 2d/N) ≤ exp(-d/6)`.  If `2d/N ≥ 1` the
event is null; otherwise it forces at most `d - 1` of the `N` uniforms into `[1 - 2d/N, 1]`,
a Binomial `(N, 2d/N)` count of mean `2d`. -/
theorem orderLaw_upper_window {N : ℕ} (r : Fin N) :
    orderLaw N {v | 2 * ((N - r : ℕ) : ℝ) / N < 1 - v r} ≤
      ENNReal.ofReal (exp (-(((N - r : ℕ) : ℝ) / 6))) := by
  set d : ℝ := ((N - r : ℕ) : ℝ) with hd
  have hN : (0 : ℝ) < N := by exact_mod_cast r.pos
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  by_cases hx : 1 ≤ 2 * d / N
  · have hempty : {v : Fin N → ℝ | 2 * d / N < 1 - v r} ∩ simplex N = ∅ := by
      ext v
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h hv
      have := hv.2.1 r
      linarith
    rw [orderLaw_apply, hempty, measure_empty, mul_zero]
    exact zero_le
  · push Not at hx
    set x : ℝ := 2 * d / N with hxdef
    have hx0 : 0 ≤ x := by positivity
    have hmeas : MeasurableSet {v : Fin N → ℝ | x < 1 - v r} :=
      measurableSet_lt measurable_const (measurable_const.sub (measurable_pi_apply r))
    rw [orderLaw_eq_map_sortVec, Measure.map_apply measurable_sortVec hmeas]
    have hsub : sortVec ⁻¹' {v : Fin N → ℝ | x < 1 - v r} ⊆
        {u | countIn (Ici (1 - x)) u ≤ d} := by
      intro u hu
      simp only [mem_preimage, mem_ofPred_eq] at hu ⊢
      rw [← countIn_sortVec]
      refine (countIn_Ici_le_of_lt (monotone_sortVec u)
        (by linarith : sortVec u r < 1 - x)).trans ?_
      rw [hd]
      exact_mod_cast (by omega : N - 1 - r ≤ N - r)
    refine (measure_mono hsub).trans ?_
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((countIn_lower_tail measurableSet_Ici d
      (by norm_num : (-(1 / 2) : ℝ) ≤ 0)).trans ?_)
    rw [uniform_real_Ici hx0 hx.le]
    have hNx : (N : ℝ) * x = 2 * d := by rw [hxdef]; field_simp
    rw [hNx]
    have := exp_neg_half_le_two_thirds
    exact exp_le_exp.2 (by nlinarith)

/-- **Lower window.**  With `d = N - r`, `P(1 - V_(r) < d/(2N)) ≤ exp(-d/6)`: the event forces at
least `d` of the `N` uniforms into `[1 - d/(2N), 1]`, a Binomial `(N, d/(2N))` count of mean
`d/2`. -/
theorem orderLaw_lower_window {N : ℕ} (r : Fin N) :
    orderLaw N {v | 1 - v r < ((N - r : ℕ) : ℝ) / (2 * N)} ≤
      ENNReal.ofReal (exp (-(((N - r : ℕ) : ℝ) / 6))) := by
  set d : ℝ := ((N - r : ℕ) : ℝ) with hd
  have hN : (0 : ℝ) < N := by exact_mod_cast r.pos
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hdN : d ≤ N := by rw [hd]; exact_mod_cast Nat.sub_le N r
  set x : ℝ := d / (2 * N) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_one (by positivity)]
    linarith
  have hmeas : MeasurableSet {v : Fin N → ℝ | 1 - v r < x} :=
    measurableSet_lt (measurable_const.sub (measurable_pi_apply r)) measurable_const
  rw [orderLaw_eq_map_sortVec, Measure.map_apply measurable_sortVec hmeas]
  have hsub : sortVec ⁻¹' {v : Fin N → ℝ | 1 - v r < x} ⊆
      {u | d ≤ countIn (Ici (1 - x)) u} := by
    intro u hu
    simp only [mem_preimage, mem_ofPred_eq] at hu ⊢
    rw [← countIn_sortVec]
    exact countIn_Ici_ge_of_lt (monotone_sortVec u) (by linarith : 1 - x < sortVec u r)
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ((countIn_upper_tail measurableSet_Ici d
    (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_)
  rw [uniform_real_Ici hx0 hx1]
  have hNx : (N : ℝ) * x = d / 2 := by rw [hxdef]; field_simp
  rw [hNx]
  have := exp_half_le_five_thirds
  exact exp_le_exp.2 (by nlinarith)

theorem orderLaw_real_upper_window {N : ℕ} (r : Fin N) :
    (orderLaw N).real {v | 2 * ((N - r : ℕ) : ℝ) / N < 1 - v r} ≤
      exp (-(((N - r : ℕ) : ℝ) / 6)) :=
  ENNReal.toReal_le_of_le_ofReal (exp_pos _).le (orderLaw_upper_window r)

theorem orderLaw_real_lower_window {N : ℕ} (r : Fin N) :
    (orderLaw N).real {v | 1 - v r < ((N - r : ℕ) : ℝ) / (2 * N)} ≤
      exp (-(((N - r : ℕ) : ℝ) / 6)) :=
  ENNReal.toReal_le_of_le_ofReal (exp_pos _).le (orderLaw_lower_window r)

end Order

/-! ## The uniform good-anchor event -/

section Anchors

open Renyi

/-- Every anchor `r` with `d = N - r ≥ D` has `d/(2N) ≤ 1 - v r ≤ 2d/N`. -/
def goodAnchors (N D : ℕ) : Set (Fin N → ℝ) :=
  {v | ∀ r : Fin N, D ≤ N - (r : ℕ) →
    ((N - r : ℕ) : ℝ) / (2 * N) ≤ 1 - v r ∧ 1 - v r ≤ 2 * ((N - r : ℕ) : ℝ) / N}

/-- The failure of one anchor `r` with `N - r ≥ D`. -/
def badAnchor (N D : ℕ) (r : Fin N) : Set (Fin N → ℝ) :=
  {v | D ≤ N - (r : ℕ) ∧
    (1 - v r < ((N - r : ℕ) : ℝ) / (2 * N) ∨ 2 * ((N - r : ℕ) : ℝ) / N < 1 - v r)}

theorem compl_goodAnchors_subset (N D : ℕ) :
    (goodAnchors N D)ᶜ ⊆ ⋃ r : Fin N, badAnchor N D r := by
  intro v hv
  simp only [goodAnchors, mem_compl_iff, mem_ofPred_eq, not_forall] at hv
  obtain ⟨r, hr, h⟩ := hv
  refine mem_iUnion.2 ⟨r, hr, ?_⟩
  by_contra h'
  push Not at h'
  exact h ⟨h'.1, h'.2⟩

theorem orderLaw_badAnchor_le (N D : ℕ) (r : Fin N) :
    orderLaw N (badAnchor N D r) ≤ ENNReal.ofReal (2 * exp (-((D : ℝ) / 6))) := by
  by_cases hr : D ≤ N - (r : ℕ)
  · have hsub : badAnchor N D r ⊆ {v | 1 - v r < ((N - r : ℕ) : ℝ) / (2 * N)} ∪
        {v | 2 * ((N - r : ℕ) : ℝ) / N < 1 - v r} := fun v hv => hv.2
    have hexp : exp (-(((N - r : ℕ) : ℝ) / 6)) ≤ exp (-((D : ℝ) / 6)) := by
      have : (D : ℝ) ≤ ((N - r : ℕ) : ℝ) := by exact_mod_cast hr
      exact exp_le_exp.2 (by linarith)
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    calc orderLaw N {v | 1 - v r < ((N - r : ℕ) : ℝ) / (2 * N)} +
          orderLaw N {v | 2 * ((N - r : ℕ) : ℝ) / N < 1 - v r}
        ≤ ENNReal.ofReal (exp (-((D : ℝ) / 6))) + ENNReal.ofReal (exp (-((D : ℝ) / 6))) :=
          add_le_add ((orderLaw_lower_window r).trans (ENNReal.ofReal_le_ofReal hexp))
            ((orderLaw_upper_window r).trans (ENNReal.ofReal_le_ofReal hexp))
      _ = ENNReal.ofReal (2 * exp (-((D : ℝ) / 6))) := by
          rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le, two_mul]
  · rw [measure_mono_null (fun v hv => absurd hv.1 hr) measure_empty]
    exact zero_le

/-- **Uniform good-anchor event.**  `P((goodAnchors N D)ᶜ) ≤ 2 N exp(-D/6)`. -/
theorem orderLaw_compl_goodAnchors_le (N D : ℕ) :
    orderLaw N (goodAnchors N D)ᶜ ≤ ENNReal.ofReal (2 * N * exp (-((D : ℝ) / 6))) := by
  refine (measure_mono (compl_goodAnchors_subset N D)).trans
    ((measure_iUnion_fintype_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun r _ => orderLaw_badAnchor_le N D r).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_left_comm,
    mul_assoc]

theorem orderLaw_real_compl_goodAnchors_le (N D : ℕ) :
    (orderLaw N).real (goodAnchors N D)ᶜ ≤ 2 * N * exp (-((D : ℝ) / 6)) :=
  ENNReal.toReal_le_of_le_ofReal (by positivity) (orderLaw_compl_goodAnchors_le N D)

/-- **Polynomial failure probability.**  For `D = ⌈K log N⌉` with `K ≥ 6 (p + 1)`,
`P((goodAnchors N D)ᶜ) ≤ 2 N^{-p}`. -/
theorem orderLaw_real_compl_goodAnchors_log_le {N : ℕ} (hN : 1 ≤ N) {p K : ℝ}
    (hK : 6 * (p + 1) ≤ K) :
    (orderLaw N).real (goodAnchors N ⌈K * log N⌉₊)ᶜ ≤ 2 * (N : ℝ) ^ (-p) := by
  refine (orderLaw_real_compl_goodAnchors_le N _).trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ log N := log_nonneg (by exact_mod_cast hN)
  have hD : K * log N ≤ (⌈K * log N⌉₊ : ℝ) := Nat.le_ceil _
  have hNp : (N : ℝ) * exp (-((p + 1) * log N)) = (N : ℝ) ^ (-p) := by
    rw [rpow_def_of_pos hNpos]
    calc (N : ℝ) * exp (-((p + 1) * log N)) = exp (log N) * exp (-((p + 1) * log N)) := by
          rw [exp_log hNpos]
      _ = exp (log N * -p) := by rw [← exp_add]; ring_nf
  calc 2 * N * exp (-((⌈K * log N⌉₊ : ℝ) / 6)) ≤ 2 * N * exp (-((p + 1) * log N)) := by
        gcongr
        nlinarith
    _ = 2 * (N : ℝ) ^ (-p) := by rw [mul_assoc, hNp]

theorem orderLaw_compl_goodAnchors_log_le {N : ℕ} (hN : 1 ≤ N) {p K : ℝ}
    (hK : 6 * (p + 1) ≤ K) :
    orderLaw N (goodAnchors N ⌈K * log N⌉₊)ᶜ ≤ ENNReal.ofReal (2 * (N : ℝ) ^ (-p)) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (orderLaw_real_compl_goodAnchors_log_le hN hK)

end Anchors

/-! ## Concentration of a Gamma total -/

section Gamma

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Gamma lower tail.**  For independent `Exp(1)` variables `E i`, `i ∈ s`, with `d = #s`,
`P(∑ E i ≤ d/2) ≤ exp(-d/6)` (Chernoff at `θ = -1`, using `e^{2/3} ≤ 2`). -/
theorem sum_exp_lower_tail {E : ι → Ω → ℝ} (hmeas : ∀ i, Measurable (E i))
    (hind : iIndepFun E P) (hlaw : ∀ i, HasLaw (E i) (expMeasure 1) P) (s : Finset ι) :
    P.real {ω | ∑ i ∈ s, E i ω ≤ (s.card : ℝ) / 2} ≤ exp (-((s.card : ℝ) / 6)) := by
  have hset : {ω | ∑ i ∈ s, E i ω ≤ (s.card : ℝ) / 2} =
      {ω | (∑ i ∈ s, E i) ω ≤ (s.card : ℝ) / 2} := by
    simp only [Finset.sum_apply]
  have hint := hind.integrable_exp_mul_sum hmeas (s := s) (t := -1)
    fun i _ => integrable_exp_mul_of_hasLaw (hlaw i) (by norm_num)
  rw [hset]
  refine (measure_le_le_exp_mul_mgf _ (by norm_num : (-1 : ℝ) ≤ 0) hint).trans ?_
  rw [hind.mgf_sum hmeas, Finset.prod_congr rfl fun i _ =>
    mgf_of_hasLaw_expMeasure (hlaw i) (by norm_num : (-1 : ℝ) < 1), Finset.prod_const]
  have key : exp (1 / 2) * (1 - -1 : ℝ)⁻¹ ≤ exp (-(1 / 6)) := by
    have h1 : exp (1 / 2 : ℝ) = exp (2 / 3) * exp (-(1 / 6)) := by rw [← exp_add]; norm_num
    rw [h1]
    have := exp_two_thirds_le_two
    have := exp_pos (-(1 / 6) : ℝ)
    norm_num
    nlinarith
  calc exp (-(-1) * ((s.card : ℝ) / 2)) * (1 - -1 : ℝ)⁻¹ ^ s.card
      = (exp (1 / 2) * (1 - -1 : ℝ)⁻¹) ^ s.card := by
        rw [mul_pow, ← exp_nat_mul]
        congr 2
        ring
    _ ≤ exp (-(1 / 6)) ^ s.card := by gcongr
    _ = exp (-((s.card : ℝ) / 6)) := by
        rw [← exp_nat_mul]
        ring_nf

/-- **Gamma upper tail.**  For independent `Exp(1)` variables `E i`, `i ∈ s`, with `d = #s`,
`P(∑ E i ≥ 2d) ≤ exp(-d/6)` (Chernoff at `θ = 1/2`, using `2 ≤ e^{5/6}`). -/
theorem sum_exp_upper_tail {E : ι → Ω → ℝ} (hmeas : ∀ i, Measurable (E i))
    (hind : iIndepFun E P) (hlaw : ∀ i, HasLaw (E i) (expMeasure 1) P) (s : Finset ι) :
    P.real {ω | 2 * (s.card : ℝ) ≤ ∑ i ∈ s, E i ω} ≤ exp (-((s.card : ℝ) / 6)) := by
  have hset : {ω | 2 * (s.card : ℝ) ≤ ∑ i ∈ s, E i ω} =
      {ω | 2 * (s.card : ℝ) ≤ (∑ i ∈ s, E i) ω} := by
    simp only [Finset.sum_apply]
  have hint := hind.integrable_exp_mul_sum hmeas (s := s) (t := 1 / 2)
    fun i _ => integrable_exp_mul_of_hasLaw (hlaw i) (by norm_num)
  rw [hset]
  refine (measure_ge_le_exp_mul_mgf _ (by norm_num : (0 : ℝ) ≤ 1 / 2) hint).trans ?_
  rw [hind.mgf_sum hmeas, Finset.prod_congr rfl fun i _ =>
    mgf_of_hasLaw_expMeasure (hlaw i) (by norm_num : (1 / 2 : ℝ) < 1), Finset.prod_const]
  have key : exp (-1) * (1 - 1 / 2 : ℝ)⁻¹ ≤ exp (-(1 / 6)) := by
    have h1 : exp (-(1 / 6) : ℝ) = exp (5 / 6) * exp (-1) := by rw [← exp_add]; norm_num
    rw [h1]
    have := two_le_exp_five_sixths
    have := exp_pos (-1 : ℝ)
    norm_num
    nlinarith
  calc exp (-(1 / 2) * (2 * (s.card : ℝ))) * (1 - 1 / 2 : ℝ)⁻¹ ^ s.card
      = (exp (-1) * (1 - 1 / 2 : ℝ)⁻¹) ^ s.card := by
        rw [mul_pow, ← exp_nat_mul]
        congr 2
        ring
    _ ≤ exp (-(1 / 6)) ^ s.card := by gcongr
    _ = exp (-((s.card : ℝ) / 6)) := by
        rw [← exp_nat_mul]
        ring_nf

/-- **Gamma window.**  `P(∑ E i ∉ [d/2, 2d]) ≤ 2 exp(-d/6)`, `d = #s`. -/
theorem sum_exp_window {E : ι → Ω → ℝ} (hmeas : ∀ i, Measurable (E i))
    (hind : iIndepFun E P) (hlaw : ∀ i, HasLaw (E i) (expMeasure 1) P) (s : Finset ι) :
    P.real {ω | ¬((s.card : ℝ) / 2 ≤ ∑ i ∈ s, E i ω ∧ ∑ i ∈ s, E i ω ≤ 2 * (s.card : ℝ))} ≤
      2 * exp (-((s.card : ℝ) / 6)) := by
  have hsub : {ω | ¬((s.card : ℝ) / 2 ≤ ∑ i ∈ s, E i ω ∧ ∑ i ∈ s, E i ω ≤ 2 * (s.card : ℝ))} ⊆
      {ω | ∑ i ∈ s, E i ω ≤ (s.card : ℝ) / 2} ∪ {ω | 2 * (s.card : ℝ) ≤ ∑ i ∈ s, E i ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_and_or, not_le] at hω
    rcases hω with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  linarith [sum_exp_lower_tail hmeas hind hlaw s, sum_exp_upper_tail hmeas hind hlaw s]

/-! ### Blocks of an iid `Exp(1)` sequence -/

variable {X : ℕ → Ω → ℝ}

theorem expSum_lower_half_tail (hX : IIDSeq P X) (hlaw : HasLaw (X 0) (expMeasure 1) P)
    (a b : ℕ) :
    P.real {ω | expSum X a b ω ≤ ((b - a : ℕ) : ℝ) / 2} ≤ exp (-(((b - a : ℕ) : ℝ) / 6)) := by
  have h := sum_exp_lower_tail hX.measurable hX.indep (hX.hasLaw_expMeasure hlaw)
    (Finset.Ico a b)
  rw [Nat.card_Ico] at h
  exact h

theorem expSum_upper_two_tail (hX : IIDSeq P X) (hlaw : HasLaw (X 0) (expMeasure 1) P)
    (a b : ℕ) :
    P.real {ω | 2 * ((b - a : ℕ) : ℝ) ≤ expSum X a b ω} ≤ exp (-(((b - a : ℕ) : ℝ) / 6)) := by
  have h := sum_exp_upper_tail hX.measurable hX.indep (hX.hasLaw_expMeasure hlaw)
    (Finset.Ico a b)
  rw [Nat.card_Ico] at h
  exact h

theorem expSum_window (hX : IIDSeq P X) (hlaw : HasLaw (X 0) (expMeasure 1) P) (a b : ℕ) :
    P.real {ω | ¬(((b - a : ℕ) : ℝ) / 2 ≤ expSum X a b ω ∧
        expSum X a b ω ≤ 2 * ((b - a : ℕ) : ℝ))} ≤ 2 * exp (-(((b - a : ℕ) : ℝ) / 6)) := by
  have h := sum_exp_window hX.measurable hX.indep (hX.hasLaw_expMeasure hlaw) (Finset.Ico a b)
  rw [Nat.card_Ico] at h
  exact h

end Gamma

/-! ## The reset coefficient -/

/-- **Reset coefficient.**  If `d/(2N) ≤ 1 - u ≤ 2d/N` and `d/2 ≤ S`, then `(1 - u)/S ≤ 4/N`. -/
theorem reset_coef_le {N d u S : ℝ} (hN : 0 < N) (hd : 0 < d)
    (hu : d / (2 * N) ≤ 1 - u ∧ 1 - u ≤ 2 * d / N) (hS : d / 2 ≤ S) : (1 - u) / S ≤ 4 / N := by
  have hSpos : 0 < S := by linarith
  rw [div_le_div_iff₀ hSpos hN]
  have h := (le_div_iff₀ hN).1 hu.2
  linarith

/-- On `goodAnchors N D`, every anchor `r` with `d = N - r ≥ D` and a Gamma total `S ≥ d/2`
has reset coefficient `(1 - v r)/S ≤ 4/N`. -/
theorem reset_coef_le_of_mem_goodAnchors {N D : ℕ} {v : Fin N → ℝ} (hv : v ∈ goodAnchors N D)
    {r : Fin N} (hr : D ≤ N - (r : ℕ)) {S : ℝ} (hS : ((N - r : ℕ) : ℝ) / 2 ≤ S) :
    (1 - v r) / S ≤ 4 / N :=
  reset_coef_le (by exact_mod_cast r.pos) (by exact_mod_cast (by omega : 0 < N - (r : ℕ)))
    (hv r hr) hS

end PGM
