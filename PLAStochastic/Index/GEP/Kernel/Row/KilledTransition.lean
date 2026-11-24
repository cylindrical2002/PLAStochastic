import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.WordExpansion

/-!
# WP4 kernel rows: the real killed transition, its density representatives, block identities

Source: `research/2026-09-28-gep-closure/influence-lipschitz.md` §2–3 (the kernels `Q_a^±`,
`K_{n,a}(b,c) = (Q_a^+)^n(b,c)`, rows `q_n = K_{n,a}(b,·)` and pins).  Companion note:
`research/2026-09-30-lean-gep-direct-term/progress-kernel-row.md`.

The *real* backward killed step of the step law `ρ`, slope `a` and shift `β` on the interval `J`
is `krStep J ρ β a u y = 1_J(y) ∫ u(y + β - a x) dρ(x)`; `krRow J ρ β a n φ = krStep^[n] (1_J φ)`
is the `n`-step killed row and `krSurv J ρ β a n y₀ = krRow … n 1 y₀` the survival probability
`s_n(y₀)` of the walk `y_l = y₀ + l β - a (g₀ + ⋯ + g_{l-1})` started at `y₀` and killed when it
leaves `J`.  For `(β, a) = (1, a)` this is `Q_a^+` (step `1 - a X`), for `(β, a) = (-1, -a)` it is
`Q_a^-` (step `a X - 1`).

For a law `ν = f dx` the one-step kernel has the pointwise density representative
`krKer J f β a y z = 1_J(y) 1_J(z) f((y + β - z)/a) / |a|`, and the `(n+1)`-step kernel the
**pointwise** representative

`krDens J ν f β a (n+1) y₀ z = ∫ (∏_{l ≤ n} 1_J(y_l)) krKer(y_n, z) d iidLaw ν`.

Main statements (all pointwise in `y₀`, `z`, no a.e. classes):

* `krRow_eq_integral`: `krRow … n φ y₀ = ∫ (∏_{l ≤ n} 1_J(y_l)) φ(y_n) d iidLaw ν` (path form);
* `kr_integral_markov`: the Markov splitting of a path integral at time `m`;
* `krRow_succ_eq_integral_krDens`: `krRow … (n+1) φ y₀ = ∫ krDens (n+1) y₀ z φ(z) dz`
  (the density represents the row; `integral_krDens` is the mass identity
  `∫ krDens (n+1) y₀ z dz = krSurv (n+1) y₀`);
* `krDens_add`: the pointwise Chapman–Kolmogorov identity
  `krDens (m+1+(n+1)) y₀ z = ∫ krDens (m+1) y₀ y · krDens (n+1) y z dy`;
* `krDens_symm`: forward/reverse symmetry `krDens β a (n+1) y₀ z = krDens (-β) (-a) (n+1) z y₀`,
  so pins and reverse rows are literally the same numbers;
* `krDens_le_div_mul_krSurv`: `krDens (n+1) y₀ z ≤ (D/|a|) krSurv n y₀` for `f ≤ D`;
* `kRow_zero_eq_krRow`: the complex row `kRow J ν ν 0 β a n` of `GEPKillDefs` is the coercion of
  the real row, which connects the real objects to the killed `L²` gap (`GEPKillGap`) and the
  class-uniform exponential row bound (`GEPKillClass`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ## The survival indicator of a killed path -/

/-- `∏_{l ≤ n} 1_J(y_l)` along the walk `y_l = kWalk y₀ β a g l`. -/
def krAlive (J : Set ℝ) (β a : ℝ) (n : ℕ) (y₀ : ℝ) (g : ℕ → ℝ) : ℝ :=
  ∏ l ∈ Finset.range (n + 1), J.indicator (fun _ => (1 : ℝ)) (kWalk y₀ β a g l)

variable {J : Set ℝ} {β a : ℝ}

theorem kr_indicator_one_mul_self (y : ℝ) :
    J.indicator (fun _ => (1 : ℝ)) y * J.indicator (fun _ => (1 : ℝ)) y =
      J.indicator (fun _ => (1 : ℝ)) y := by
  by_cases hy : y ∈ J <;> simp [hy]

theorem kr_indicator_one_nonneg (y : ℝ) : 0 ≤ J.indicator (fun _ => (1 : ℝ)) y :=
  indicator_nonneg (fun _ _ => zero_le_one) _

theorem kr_indicator_one_le_one (y : ℝ) : J.indicator (fun _ => (1 : ℝ)) y ≤ 1 := by
  by_cases hy : y ∈ J <;> simp [hy]

theorem krAlive_zero (y₀ : ℝ) (g : ℕ → ℝ) :
    krAlive J β a 0 y₀ g = J.indicator (fun _ => (1 : ℝ)) y₀ := by
  simp [krAlive, kWalk_zero]

/-- Peeling the first step. -/
theorem krAlive_succ (n : ℕ) (y₀ : ℝ) (g : ℕ → ℝ) :
    krAlive J β a (n + 1) y₀ g =
      J.indicator (fun _ => (1 : ℝ)) y₀ *
        krAlive J β a n (y₀ + β - a * g 0) (fun i => g (i + 1)) := by
  unfold krAlive
  rw [Finset.prod_range_succ' _ (n + 1), kWalk_zero]
  simp only [kWalk_succ]
  ring

/-- Peeling the last step. -/
theorem krAlive_succ_last (n : ℕ) (y₀ : ℝ) (g : ℕ → ℝ) :
    krAlive J β a (n + 1) y₀ g =
      krAlive J β a n y₀ g * J.indicator (fun _ => (1 : ℝ)) (kWalk y₀ β a g (n + 1)) := by
  unfold krAlive
  rw [Finset.prod_range_succ]

theorem krAlive_mul_indicator (n : ℕ) (y₀ : ℝ) (g : ℕ → ℝ) :
    krAlive J β a n y₀ g * J.indicator (fun _ => (1 : ℝ)) (kWalk y₀ β a g n) =
      krAlive J β a n y₀ g := by
  unfold krAlive
  rw [Finset.prod_range_succ, mul_assoc, kr_indicator_one_mul_self]

theorem krAlive_nonneg (n : ℕ) (y₀ : ℝ) (g : ℕ → ℝ) : 0 ≤ krAlive J β a n y₀ g :=
  Finset.prod_nonneg fun _ _ => kr_indicator_one_nonneg _

theorem krAlive_le_one (n : ℕ) (y₀ : ℝ) (g : ℕ → ℝ) : krAlive J β a n y₀ g ≤ 1 :=
  Finset.prod_le_one (fun _ _ => kr_indicator_one_nonneg _) fun _ _ => kr_indicator_one_le_one _

theorem abs_krAlive_le_one (n : ℕ) (y₀ : ℝ) (g : ℕ → ℝ) : |krAlive J β a n y₀ g| ≤ 1 := by
  rw [abs_of_nonneg (krAlive_nonneg _ _ _)]
  exact krAlive_le_one _ _ _

theorem krAlive_eq_zero_of_notMem {y₀ : ℝ} (hy : y₀ ∉ J) (n : ℕ) (g : ℕ → ℝ) :
    krAlive J β a n y₀ g = 0 := by
  unfold krAlive
  apply Finset.prod_eq_zero (Finset.mem_range.2 (Nat.succ_pos n))
  simp [kWalk_zero, hy]

theorem krAlive_le_of_le (m n : ℕ) (hmn : m ≤ n) (y₀ : ℝ) (g : ℕ → ℝ) :
    krAlive J β a n y₀ g ≤ krAlive J β a m y₀ g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [← Nat.add_assoc, krAlive_succ_last]
    calc krAlive J β a (m + k) y₀ g * J.indicator (fun _ => (1 : ℝ)) _
        ≤ krAlive J β a (m + k) y₀ g * 1 :=
          mul_le_mul_of_nonneg_left (kr_indicator_one_le_one _) (krAlive_nonneg _ _ _)
      _ = krAlive J β a (m + k) y₀ g := mul_one _
      _ ≤ _ := ih

theorem measurable_krAlive_prod (hJ : MeasurableSet J) (β a : ℝ) (n : ℕ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => krAlive J β a n p.1 p.2) := by
  unfold krAlive
  refine Finset.measurable_prod _ fun l _ => ?_
  exact (measurable_const.indicator hJ).comp (measurable_kWalk_prod β a l)

theorem measurable_krAlive_left (hJ : MeasurableSet J) (β a : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    Measurable (fun y₀ : ℝ => krAlive J β a n y₀ g) :=
  (measurable_krAlive_prod hJ β a n).comp (measurable_id.prodMk measurable_const)

theorem measurable_krAlive_right (hJ : MeasurableSet J) (β a : ℝ) (n : ℕ) (y₀ : ℝ) :
    Measurable (fun g : ℕ → ℝ => krAlive J β a n y₀ g) :=
  (measurable_krAlive_prod hJ β a n).comp (measurable_const.prodMk measurable_id)

/-- The walk restarted at time `m`. -/
theorem kWalk_add (y₀ β a : ℝ) (g : ℕ → ℝ) (m l : ℕ) :
    kWalk y₀ β a g (m + l) = kWalk (kWalk y₀ β a g m) β a (fun i => g (i + m)) l := by
  simp only [kWalk, gapKeys]
  rw [Finset.sum_range_add]
  have : ∑ x ∈ Finset.range l, g (m + x) = ∑ x ∈ Finset.range l, g (x + m) :=
    Finset.sum_congr rfl fun x _ => by rw [Nat.add_comm]
  rw [this]
  push_cast
  ring

/-- The survival indicator splits at time `m` (the common point `y_m` is counted once). -/
theorem krAlive_add (m n : ℕ) (y₀ : ℝ) (g : ℕ → ℝ) :
    krAlive J β a (m + n) y₀ g =
      krAlive J β a m y₀ g * krAlive J β a n (kWalk y₀ β a g m) (fun i => g (i + m)) := by
  induction n with
  | zero => rw [Nat.add_zero, krAlive_zero, krAlive_mul_indicator]
  | succ n ih =>
    rw [← Nat.add_assoc, krAlive_succ_last, ih, krAlive_succ_last, Nat.add_assoc, kWalk_add,
      mul_assoc]

/-! ## The real killed step and row -/

/-- One real backward killed step: `u ↦ 1_J(y) ∫ u(y + β - a x) dρ(x)`. -/
def krStep (J : Set ℝ) (ρ : Measure ℝ) (β a : ℝ) (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  J.indicator (fun y => ∫ x, u (y + β - a * x) ∂ρ) y

/-- The real killed row of length `n`: `n` steps, all points `y₀, …, y_n` in `J`, test `φ(y_n)`. -/
def krRow (J : Set ℝ) (ρ : Measure ℝ) (β a : ℝ) (n : ℕ) (φ : ℝ → ℝ) : ℝ → ℝ :=
  (krStep J ρ β a)^[n] (J.indicator φ)

/-- The survival probability `s_n(y₀)` of the killed walk. -/
def krSurv (J : Set ℝ) (ρ : Measure ℝ) (β a : ℝ) (n : ℕ) : ℝ → ℝ :=
  krRow J ρ β a n (fun _ => 1)

variable {ρ : Measure ℝ}

theorem krRow_zero (φ : ℝ → ℝ) : krRow J ρ β a 0 φ = J.indicator φ := rfl

theorem krRow_succ (n : ℕ) (φ : ℝ → ℝ) :
    krRow J ρ β a (n + 1) φ = krStep J ρ β a (krRow J ρ β a n φ) :=
  Function.iterate_succ_apply' _ _ _

theorem krStep_eq_zero_of_notMem {u : ℝ → ℝ} {y : ℝ} (hy : y ∉ J) : krStep J ρ β a u y = 0 :=
  indicator_of_notMem hy _

theorem krStep_of_mem {u : ℝ → ℝ} {y : ℝ} (hy : y ∈ J) :
    krStep J ρ β a u y = ∫ x, u (y + β - a * x) ∂ρ :=
  indicator_of_mem hy _

theorem indicator_krStep (u : ℝ → ℝ) : J.indicator (krStep J ρ β a u) = krStep J ρ β a u := by
  unfold krStep
  rw [indicator_indicator, inter_self]

theorem krRow_eq_zero_of_notMem {n : ℕ} {φ : ℝ → ℝ} {y : ℝ} (hy : y ∉ J) :
    krRow J ρ β a n φ y = 0 := by
  cases n with
  | zero => exact indicator_of_notMem hy _
  | succ n => rw [krRow_succ]; exact krStep_eq_zero_of_notMem hy

theorem indicator_krRow (n : ℕ) (φ : ℝ → ℝ) :
    J.indicator (krRow J ρ β a n φ) = krRow J ρ β a n φ := by
  funext y
  by_cases hy : y ∈ J
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy, krRow_eq_zero_of_notMem hy]

/-- The block identity of rows: `krRow (m + n) φ = krRow m (krRow n φ)`. -/
theorem krRow_add (m n : ℕ) (φ : ℝ → ℝ) :
    krRow J ρ β a (m + n) φ = krRow J ρ β a m (krRow J ρ β a n φ) := by
  conv_rhs => rw [krRow, indicator_krRow]
  exact Function.iterate_add_apply _ _ _ _

/-- The row after the first step is the shorter row of the stepped test. -/
theorem krRow_succ_eq_krRow_krStep (n : ℕ) (φ : ℝ → ℝ) :
    krRow J ρ β a (n + 1) φ = krRow J ρ β a n (krStep J ρ β a (J.indicator φ)) := by
  conv_rhs => rw [krRow, indicator_krStep]
  exact Function.iterate_succ_apply _ _ _

/-! ## Head splitting of the product law -/

/-- The law of `(g 0, g ∘ succ)` under `iidLaw ν` is `ν ⊗ iidLaw ν`. -/
theorem kr_iidLaw_map_head (ν : ProbabilityMeasure ℝ) :
    (iidLaw ν).map (fun g => (g 0, fun i => g (i + 1))) = (ν : Measure ℝ).prod (iidLaw ν) := by
  unfold iidLaw
  exact kill_infinitePi_map_eval_comp 0 (c := fun i => i + 1) (fun i j h => by simpa using h)
    (fun i => Nat.succ_ne_zero i)

/-- A bounded measurable function is integrable for a finite measure. -/
theorem kr_integrable_of_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {F : α → ℝ} (hF : Measurable F) {M : ℝ} (hM : ∀ x, |F x| ≤ M) : Integrable F μ :=
  (integrable_const M).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)

/-- The integral of a function bounded by `M` against a probability measure is bounded by `M`. -/
theorem kr_abs_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {F : α → ℝ} {M : ℝ} (hM : ∀ x, |F x| ≤ M) :
    |∫ x, F x ∂μ| ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := M)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at h

/-- Head/tail decomposition of a bounded jointly measurable integrand under `iidLaw ν`. -/
theorem kr_integral_head (ν : ProbabilityMeasure ℝ) {F : ℝ → (ℕ → ℝ) → ℝ}
    (hF : Measurable (Function.uncurry F)) {M : ℝ} (hM : ∀ x g, |F x g| ≤ M) :
    ∫ g, F (g 0) (fun i => g (i + 1)) ∂(iidLaw ν) =
      ∫ x, ∫ g, F x g ∂(iidLaw ν) ∂(ν : Measure ℝ) := by
  have hpair : Measurable (fun g : ℕ → ℝ => (g 0, fun i => g (i + 1))) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_lambda _ fun i => measurable_pi_apply (i + 1))
  have hint : Integrable (Function.uncurry F) ((ν : Measure ℝ).prod (iidLaw ν)) :=
    (integrable_const M).mono' hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hM p.1 p.2)
  have h := integral_map (μ := iidLaw ν) hpair.aemeasurable
    (f := Function.uncurry F) (by rw [kr_iidLaw_map_head ν]; exact hF.aestronglyMeasurable)
  rw [kr_iidLaw_map_head ν, integral_prod _ hint] at h
  simp only [Function.uncurry_apply_pair] at h
  exact h.symm

/-! ## The path form of the row -/

/-- **Path form of the real row**: `krRow … n φ y₀ = ∫ (∏_{l ≤ n} 1_J(y_l)) φ(y_n) d iidLaw ν`. -/
theorem krRow_eq_integral (hJ : MeasurableSet J) (ν : ProbabilityMeasure ℝ) (β a : ℝ) (n : ℕ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) (y₀ : ℝ) :
    krRow J (ν : Measure ℝ) β a n φ y₀ =
      ∫ g, krAlive J β a n y₀ g * φ (kWalk y₀ β a g n) ∂(iidLaw ν) := by
  induction n generalizing y₀ with
  | zero =>
    simp only [krRow_zero, krAlive_zero, kWalk_zero, integral_const, probReal_univ, one_smul]
    by_cases hy : y₀ ∈ J <;> simp [hy]
  | succ n ih =>
    rw [krRow_succ]
    by_cases hy : y₀ ∉ J
    · rw [krStep_eq_zero_of_notMem hy]
      simp [krAlive_eq_zero_of_notMem hy]
    push Not at hy
    set F : ℝ → (ℕ → ℝ) → ℝ := fun x h =>
      krAlive J β a n (y₀ + β - a * x) h * φ (kWalk (y₀ + β - a * x) β a h n) with hF
    have hFm : Measurable (Function.uncurry F) := by
      have h1 : Measurable (fun p : ℝ × (ℕ → ℝ) => ((y₀ + β - a * p.1, p.2) : ℝ × (ℕ → ℝ))) := by
        fun_prop
      exact ((measurable_krAlive_prod hJ β a n).mul (hφ.comp (measurable_kWalk_prod β a n))).comp h1
    have hFb : ∀ x h, |F x h| ≤ |M| := by
      intro x h
      simp only [hF]
      rw [abs_mul, abs_of_nonneg (krAlive_nonneg _ _ _)]
      calc krAlive J β a n (y₀ + β - a * x) h * |φ (kWalk (y₀ + β - a * x) β a h n)|
          ≤ 1 * |M| := mul_le_mul (krAlive_le_one _ _ _) ((hM _).trans (le_abs_self M))
            (abs_nonneg _) zero_le_one
        _ = |M| := one_mul _
    have hrhs : ∀ g : ℕ → ℝ, krAlive J β a (n + 1) y₀ g * φ (kWalk y₀ β a g (n + 1)) =
        F (g 0) (fun i => g (i + 1)) := by
      intro g
      rw [krAlive_succ, kWalk_succ, indicator_of_mem hy, one_mul]
    simp_rw [hrhs]
    rw [kr_integral_head ν hFm hFb, krStep_of_mem hy]
    congr 1
    funext x
    exact ih _

theorem measurable_krRow (hJ : MeasurableSet J) (ν : ProbabilityMeasure ℝ) (β a : ℝ) (n : ℕ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    Measurable (krRow J (ν : Measure ℝ) β a n φ) := by
  have e : krRow J (ν : Measure ℝ) β a n φ = fun y₀ =>
      ∫ g, krAlive J β a n y₀ g * φ (kWalk y₀ β a g n) ∂(iidLaw ν) :=
    funext fun y₀ => krRow_eq_integral hJ ν β a n hφ hM y₀
  rw [e]
  exact (((measurable_krAlive_prod hJ β a n).mul
    (hφ.comp (measurable_kWalk_prod β a n))).stronglyMeasurable.integral_prod_right').measurable

theorem abs_krRow_le (hJ : MeasurableSet J) (ν : ProbabilityMeasure ℝ) (β a : ℝ) (n : ℕ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) (y₀ : ℝ) :
    |krRow J (ν : Measure ℝ) β a n φ y₀| ≤ M := by
  rw [krRow_eq_integral hJ ν β a n hφ hM y₀]
  refine kr_abs_integral_le fun g => ?_
  rw [abs_mul, abs_of_nonneg (krAlive_nonneg _ _ _)]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc krAlive J β a n y₀ g * |φ (kWalk y₀ β a g n)| ≤ 1 * M :=
        mul_le_mul (krAlive_le_one _ _ _) (hM _) (abs_nonneg _) zero_le_one
    _ = M := one_mul M

theorem krRow_nonneg (hJ : MeasurableSet J) (ν : ProbabilityMeasure ℝ) (β a : ℝ) (n : ℕ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) (hφ0 : ∀ y, 0 ≤ φ y) (y₀ : ℝ) :
    0 ≤ krRow J (ν : Measure ℝ) β a n φ y₀ := by
  rw [krRow_eq_integral hJ ν β a n hφ hM y₀]
  exact integral_nonneg fun g => mul_nonneg (krAlive_nonneg _ _ _) (hφ0 _)

theorem krRow_mono (hJ : MeasurableSet J) (ν : ProbabilityMeasure ℝ) (β a : ℝ) (n : ℕ)
    {φ ψ : ℝ → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) {M : ℝ} (hMφ : ∀ y, |φ y| ≤ M)
    (hMψ : ∀ y, |ψ y| ≤ M) (h : ∀ y, φ y ≤ ψ y) (y₀ : ℝ) :
    krRow J (ν : Measure ℝ) β a n φ y₀ ≤ krRow J (ν : Measure ℝ) β a n ψ y₀ := by
  rw [krRow_eq_integral hJ ν β a n hφ hMφ y₀, krRow_eq_integral hJ ν β a n hψ hMψ y₀]
  refine integral_mono (kr_integrable_of_bdd ?_ (M := M) ?_) (kr_integrable_of_bdd ?_ (M := M) ?_)
    fun g => mul_le_mul_of_nonneg_left (h _) (krAlive_nonneg _ _ _)
  · exact (measurable_krAlive_right hJ β a n y₀).mul
      (hφ.comp ((measurable_kWalk_prod β a n).comp (measurable_const.prodMk measurable_id)))
  · intro g
    rw [abs_mul, abs_of_nonneg (krAlive_nonneg _ _ _)]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMφ 0)
    calc _ ≤ 1 * M := mul_le_mul (krAlive_le_one _ _ _) (hMφ _) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  · exact (measurable_krAlive_right hJ β a n y₀).mul
      (hψ.comp ((measurable_kWalk_prod β a n).comp (measurable_const.prodMk measurable_id)))
  · intro g
    rw [abs_mul, abs_of_nonneg (krAlive_nonneg _ _ _)]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMψ 0)
    calc _ ≤ 1 * M := mul_le_mul (krAlive_le_one _ _ _) (hMψ _) (abs_nonneg _) zero_le_one
      _ = M := one_mul M

/-- The survival probability in path form. -/
theorem krSurv_eq_integral (hJ : MeasurableSet J) (ν : ProbabilityMeasure ℝ) (β a : ℝ) (n : ℕ)
    (y₀ : ℝ) : krSurv J (ν : Measure ℝ) β a n y₀ = ∫ g, krAlive J β a n y₀ g ∂(iidLaw ν) := by
  unfold krSurv
  rw [krRow_eq_integral hJ ν β a n measurable_const (M := 1) (fun _ => by simp) y₀]
  simp only [mul_one]

theorem krSurv_nonneg (hJ : MeasurableSet J) (ν : ProbabilityMeasure ℝ) (β a : ℝ) (n : ℕ)
    (y₀ : ℝ) : 0 ≤ krSurv J (ν : Measure ℝ) β a n y₀ := by
  rw [krSurv_eq_integral hJ ν β a n y₀]
  exact integral_nonneg fun g => krAlive_nonneg _ _ _

theorem krSurv_le_one (hJ : MeasurableSet J) (ν : ProbabilityMeasure ℝ) (β a : ℝ) (n : ℕ)
    (y₀ : ℝ) : krSurv J (ν : Measure ℝ) β a n y₀ ≤ 1 := by
  have h := abs_krRow_le hJ ν β a n (φ := fun _ => (1 : ℝ)) measurable_const (M := 1)
    (fun _ => by simp) y₀
  exact (le_abs_self _).trans h

theorem measurable_krSurv (hJ : MeasurableSet J) (ν : ProbabilityMeasure ℝ) (β a : ℝ) (n : ℕ) :
    Measurable (krSurv J (ν : Measure ℝ) β a n) :=
  measurable_krRow hJ ν β a n measurable_const (M := 1) fun _ => by simp

/-- Survival is monotone in time. -/
theorem krSurv_le_of_le (hJ : MeasurableSet J) (ν : ProbabilityMeasure ℝ) (β a : ℝ) {m n : ℕ}
    (hmn : m ≤ n) (y₀ : ℝ) :
    krSurv J (ν : Measure ℝ) β a n y₀ ≤ krSurv J (ν : Measure ℝ) β a m y₀ := by
  rw [krSurv_eq_integral hJ ν β a n y₀, krSurv_eq_integral hJ ν β a m y₀]
  exact integral_mono (kr_integrable_of_bdd (measurable_krAlive_right hJ β a n y₀)
    (abs_krAlive_le_one n y₀)) (kr_integrable_of_bdd (measurable_krAlive_right hJ β a m y₀)
    (abs_krAlive_le_one m y₀)) fun g => krAlive_le_of_le m n hmn y₀ g

theorem krSurv_eq_zero_of_notMem {n : ℕ} {y : ℝ} (hy : y ∉ J) : krSurv J ρ β a n y = 0 :=
  krRow_eq_zero_of_notMem hy

/-! ## Markov splitting -/

/-- **Markov splitting at time `m`.**  For a bounded jointly measurable `F`,
`∫ (∏_{l ≤ m} 1_J(y_l)) F(y_m, g ∘ (· + m)) = ∫ (∏_{l ≤ m} 1_J(y_l)) (∫ F(y_m, g') dg')`. -/
theorem kr_integral_markov (hJ : MeasurableSet J) (ν : ProbabilityMeasure ℝ) (β a : ℝ) (m : ℕ)
    {F : ℝ → (ℕ → ℝ) → ℝ} (hF : Measurable (Function.uncurry F)) {M : ℝ}
    (hM : ∀ y g, |F y g| ≤ M) (y₀ : ℝ) :
    ∫ g, krAlive J β a m y₀ g * F (kWalk y₀ β a g m) (fun i => g (i + m)) ∂(iidLaw ν) =
      ∫ g, krAlive J β a m y₀ g * ∫ g', F (kWalk y₀ β a g m) g' ∂(iidLaw ν) ∂(iidLaw ν) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  -- the integrated function
  have hGm : Measurable (fun y => ∫ g', F y g' ∂(iidLaw ν)) :=
    hF.stronglyMeasurable.integral_prod_right.measurable
  have hGb : ∀ y, |∫ g', F y g' ∂(iidLaw ν)| ≤ M := fun y => kr_abs_integral_le (hM y)
  induction m generalizing y₀ with
  | zero =>
    simp only [krAlive_zero, kWalk_zero, Nat.add_zero, integral_const_mul, integral_const,
      probReal_univ, one_smul]
  | succ m ih =>
    by_cases hy : y₀ ∉ J
    · simp [krAlive_eq_zero_of_notMem hy]
    push Not at hy
    have hshift : Measurable (fun p : ℝ × (ℕ → ℝ) => ((y₀ + β - a * p.1, p.2) : ℝ × (ℕ → ℝ))) := by
      fun_prop
    have htail : Measurable (fun p : ℝ × (ℕ → ℝ) =>
        ((kWalk p.1 β a p.2 m, fun i => p.2 (i + m)) : ℝ × (ℕ → ℝ))) :=
      (measurable_kWalk_prod β a m).prodMk
        (measurable_pi_lambda _ fun i => (measurable_pi_apply (i + m)).comp measurable_snd)
    have hF₁m : Measurable (Function.uncurry fun (x : ℝ) (h : ℕ → ℝ) =>
        krAlive J β a m (y₀ + β - a * x) h *
          F (kWalk (y₀ + β - a * x) β a h m) (fun i => h (i + m))) :=
      show Measurable ((fun p : ℝ × (ℕ → ℝ) => krAlive J β a m p.1 p.2 *
          F (kWalk p.1 β a p.2 m) (fun i => p.2 (i + m))) ∘
          (fun p : ℝ × (ℕ → ℝ) => ((y₀ + β - a * p.1, p.2) : ℝ × (ℕ → ℝ)))) from
        ((measurable_krAlive_prod hJ β a m).mul (hF.comp htail)).comp hshift
    have hF₂m : Measurable (Function.uncurry fun (x : ℝ) (h : ℕ → ℝ) =>
        krAlive J β a m (y₀ + β - a * x) h *
          ∫ g', F (kWalk (y₀ + β - a * x) β a h m) g' ∂(iidLaw ν)) :=
      show Measurable ((fun p : ℝ × (ℕ → ℝ) => krAlive J β a m p.1 p.2 *
          (fun y => ∫ g', F y g' ∂(iidLaw ν)) (kWalk p.1 β a p.2 m)) ∘
          (fun p : ℝ × (ℕ → ℝ) => ((y₀ + β - a * p.1, p.2) : ℝ × (ℕ → ℝ)))) from
        ((measurable_krAlive_prod hJ β a m).mul (hGm.comp (measurable_kWalk_prod β a m))).comp
          hshift
    have hF₁b : ∀ (x : ℝ) (h : ℕ → ℝ), |krAlive J β a m (y₀ + β - a * x) h *
        F (kWalk (y₀ + β - a * x) β a h m) (fun i => h (i + m))| ≤ M := by
      intro x h
      rw [abs_mul, abs_of_nonneg (krAlive_nonneg _ _ _)]
      calc _ ≤ 1 * M := mul_le_mul (krAlive_le_one _ _ _) (hM _ _) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    have hF₂b : ∀ (x : ℝ) (h : ℕ → ℝ), |krAlive J β a m (y₀ + β - a * x) h *
        ∫ g', F (kWalk (y₀ + β - a * x) β a h m) g' ∂(iidLaw ν)| ≤ M := by
      intro x h
      rw [abs_mul, abs_of_nonneg (krAlive_nonneg _ _ _)]
      calc _ ≤ 1 * M := mul_le_mul (krAlive_le_one _ _ _) (hGb _) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    have hL : ∀ g : ℕ → ℝ, krAlive J β a (m + 1) y₀ g *
        F (kWalk y₀ β a g (m + 1)) (fun i => g (i + (m + 1))) =
        krAlive J β a m (y₀ + β - a * g 0) (fun i => g (i + 1)) *
          F (kWalk (y₀ + β - a * g 0) β a (fun i => g (i + 1)) m)
            (fun i => g (i + m + 1)) := by
      intro g
      rw [krAlive_succ, kWalk_succ, indicator_of_mem hy, one_mul]
      rfl
    have hR : ∀ g : ℕ → ℝ, krAlive J β a (m + 1) y₀ g *
        ∫ g', F (kWalk y₀ β a g (m + 1)) g' ∂(iidLaw ν) =
        krAlive J β a m (y₀ + β - a * g 0) (fun i => g (i + 1)) *
          ∫ g', F (kWalk (y₀ + β - a * g 0) β a (fun i => g (i + 1)) m) g' ∂(iidLaw ν) := by
      intro g
      rw [krAlive_succ, kWalk_succ, indicator_of_mem hy, one_mul]
    simp_rw [hL, hR]
    rw [kr_integral_head ν hF₁m hF₁b, kr_integral_head ν hF₂m hF₂b]
    congr 1
    funext x
    exact ih _

/-! ## The one-step kernel density -/

/-- The pointwise density representative of one killed step from `y` to `z`:
`1_J(y) 1_J(z) f((y + β - z)/a) / |a|`. -/
def krKer (J : Set ℝ) (f : ℝ → ℝ) (β a : ℝ) (y z : ℝ) : ℝ :=
  J.indicator (fun _ => (1 : ℝ)) y * J.indicator (fun _ => (1 : ℝ)) z * (f ((y + β - z) / a) / |a|)

theorem krKer_nonneg {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (y z : ℝ) : 0 ≤ krKer J f β a y z :=
  mul_nonneg (mul_nonneg (kr_indicator_one_nonneg _) (kr_indicator_one_nonneg _))
    (div_nonneg (hf0 _) (abs_nonneg _))

theorem krKer_le {f : ℝ → ℝ} {D : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D) (y z : ℝ) :
    krKer J f β a y z ≤ D / |a| := by
  have hD0 : 0 ≤ D := (hf0 0).trans (hfD 0)
  unfold krKer
  have h1 : J.indicator (fun _ => (1 : ℝ)) y * J.indicator (fun _ => (1 : ℝ)) z ≤ 1 * 1 :=
    mul_le_mul (kr_indicator_one_le_one _) (kr_indicator_one_le_one _)
      (kr_indicator_one_nonneg _) zero_le_one
  calc J.indicator (fun _ => (1 : ℝ)) y * J.indicator (fun _ => (1 : ℝ)) z *
        (f ((y + β - z) / a) / |a|) ≤ 1 * 1 * (D / |a|) :=
        mul_le_mul h1 (div_le_div_of_nonneg_right (hfD _) (abs_nonneg _))
          (div_nonneg (hf0 _) (abs_nonneg _)) (by norm_num)
    _ = D / |a| := by ring

theorem abs_krKer_le {f : ℝ → ℝ} {D : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D) (y z : ℝ) :
    |krKer J f β a y z| ≤ D / |a| := by
  rw [abs_of_nonneg (krKer_nonneg hf0 y z)]
  exact krKer_le hf0 hfD y z

theorem krKer_eq_zero_of_left_notMem {f : ℝ → ℝ} {y : ℝ} (hy : y ∉ J) (z : ℝ) :
    krKer J f β a y z = 0 := by
  simp [krKer, indicator_of_notMem hy]

theorem krKer_eq_zero_of_right_notMem {f : ℝ → ℝ} {z : ℝ} (hz : z ∉ J) (y : ℝ) :
    krKer J f β a y z = 0 := by
  simp [krKer, indicator_of_notMem hz]

theorem indicator_mul_krKer (f : ℝ → ℝ) (y z : ℝ) :
    J.indicator (fun _ => (1 : ℝ)) y * krKer J f β a y z = krKer J f β a y z := by
  unfold krKer
  rw [← mul_assoc, ← mul_assoc, kr_indicator_one_mul_self]

/-- Forward/reverse symmetry of the one-step kernel. -/
theorem krKer_symm (f : ℝ → ℝ) (y z : ℝ) : krKer J f β a y z = krKer J f (-β) (-a) z y := by
  unfold krKer
  rw [show z + -β - y = -(y + β - z) by ring, neg_div_neg_eq, abs_neg]
  ring

theorem measurable_krKer_prod (hJ : MeasurableSet J) {f : ℝ → ℝ} (hf : Measurable f) (β a : ℝ) :
    Measurable (fun p : ℝ × ℝ => krKer J f β a p.1 p.2) := by
  unfold krKer
  refine (((measurable_const.indicator hJ).comp measurable_fst).mul
    ((measurable_const.indicator hJ).comp measurable_snd)).mul ?_
  exact (hf.comp (by fun_prop)).div_const _

/-- **Change of variables for one step**: for `ν = f dx`,
`krStep J ν β a (1_J φ) y = ∫ krKer(y, z) φ(z) dz`. -/
theorem krStep_indicator_eq_integral {ν : Measure ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (ha : a ≠ 0) (φ : ℝ → ℝ) (y : ℝ) :
    krStep J ν β a (J.indicator φ) y = ∫ z, krKer J f β a y z * φ z := by
  by_cases hy : y ∉ J
  · rw [krStep_eq_zero_of_notMem hy]
    simp [krKer_eq_zero_of_left_notMem hy]
  push Not at hy
  rw [krStep_of_mem hy, hν, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]
  set G : ℝ → ℝ := fun t => f (-t / a) * J.indicator φ (y + β + t) with hG
  have h1 : ∀ x, f x * J.indicator φ (y + β - a * x) = G (-a * x) := by
    intro x
    simp only [hG]
    rw [neg_mul, neg_neg, mul_div_cancel_left₀ x ha, sub_eq_add_neg]
  have h2 : ∀ z, krKer J f β a y z * φ z = |a|⁻¹ * (f ((y + β - z) / a) * J.indicator φ z) := by
    intro z
    unfold krKer
    rw [indicator_of_mem hy]
    by_cases hz : z ∈ J
    · simp only [indicator_of_mem hz]; ring
    · simp only [indicator_of_notMem hz]; ring
  simp_rw [h1, h2]
  rw [Measure.integral_comp_mul_left G (-a), integral_const_mul, smul_eq_mul, abs_inv, abs_neg]
  congr 1
  rw [← integral_add_left_eq_self (fun z => f ((y + β - z) / a) * J.indicator φ z) (y + β)]
  congr 1
  funext t
  simp only [hG]
  congr 2
  ring

/-! ## The `n`-step density representative -/

/-- The pointwise density representative of the `n`-step killed kernel (`n ≥ 1`; the value at
`n = 0` is the one-step kernel and is never used): with `y_l = kWalk y₀ β a g l`,
`krDens … (n+1) y₀ z = ∫ (∏_{l ≤ n} 1_J(y_l)) krKer(y_n, z) d iidLaw ν`. -/
def krDens (J : Set ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (β a : ℝ) (n : ℕ) (y₀ z : ℝ) : ℝ :=
  ∫ g, krAlive J β a (n - 1) y₀ g * krKer J f β a (kWalk y₀ β a g (n - 1)) z ∂(iidLaw ν)

variable (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

theorem krDens_succ (n : ℕ) (y₀ z : ℝ) :
    krDens J ν f β a (n + 1) y₀ z =
      ∫ g, krAlive J β a n y₀ g * krKer J f β a (kWalk y₀ β a g n) z ∂(iidLaw ν) := by
  simp only [krDens, Nat.add_sub_cancel]

theorem krDens_one (y₀ z : ℝ) : krDens J ν f β a 1 y₀ z = krKer J f β a y₀ z := by
  rw [krDens_succ]
  simp only [krAlive_zero, kWalk_zero, indicator_mul_krKer, integral_const, probReal_univ,
    one_smul]

theorem krDens_nonneg (hf0 : ∀ x, 0 ≤ f x) (n : ℕ) (y₀ z : ℝ) : 0 ≤ krDens J ν f β a n y₀ z :=
  integral_nonneg fun _ => mul_nonneg (krAlive_nonneg _ _ _) (krKer_nonneg hf0 _ _)

theorem krDens_le_div (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D) (n : ℕ) (y₀ z : ℝ) :
    krDens J ν f β a n y₀ z ≤ D / |a| := by
  refine (le_abs_self _).trans (kr_abs_integral_le fun g => ?_)
  rw [abs_mul, abs_of_nonneg (krAlive_nonneg _ _ _)]
  have hD0 : 0 ≤ D / |a| := div_nonneg ((hf0 0).trans (hfD 0)) (abs_nonneg _)
  calc _ ≤ 1 * (D / |a|) :=
        mul_le_mul (krAlive_le_one _ _ _) (abs_krKer_le hf0 hfD _ _) (abs_nonneg _) zero_le_one
    _ = D / |a| := one_mul _

theorem abs_krDens_le (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D) (n : ℕ) (y₀ z : ℝ) :
    |krDens J ν f β a n y₀ z| ≤ D / |a| := by
  rw [abs_of_nonneg (krDens_nonneg ν hf0 n y₀ z)]
  exact krDens_le_div ν hf0 hfD n y₀ z

theorem krDens_eq_zero_of_left_notMem {y₀ : ℝ} (hy : y₀ ∉ J) (n : ℕ) (z : ℝ) :
    krDens J ν f β a n y₀ z = 0 := by
  simp [krDens, krAlive_eq_zero_of_notMem hy]

theorem krDens_eq_zero_of_right_notMem {z : ℝ} (hz : z ∉ J) (n : ℕ) (y₀ : ℝ) :
    krDens J ν f β a n y₀ z = 0 := by
  simp [krDens, krKer_eq_zero_of_right_notMem hz]

/-- The density integrand as a function of `((y₀, z), g)`. -/
theorem measurable_krDens_integrand (hJ : MeasurableSet J) (hf : Measurable f) (β a : ℝ) (n : ℕ) :
    Measurable (fun p : (ℝ × ℝ) × (ℕ → ℝ) =>
      krAlive J β a n p.1.1 p.2 * krKer J f β a (kWalk p.1.1 β a p.2 n) p.1.2) := by
  refine ((measurable_krAlive_prod hJ β a n).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul ?_
  exact (measurable_krKer_prod hJ hf β a).comp (((measurable_kWalk_prod β a n).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
    (measurable_snd.comp measurable_fst))

theorem measurable_krDens_prod (hJ : MeasurableSet J) (hf : Measurable f) (β a : ℝ) (n : ℕ) :
    Measurable (fun p : ℝ × ℝ => krDens J ν f β a n p.1 p.2) :=
  (measurable_krDens_integrand hJ hf β a (n - 1)).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_krDens_left (hJ : MeasurableSet J) (hf : Measurable f) (β a : ℝ) (n : ℕ)
    (z : ℝ) : Measurable (fun y₀ : ℝ => krDens J ν f β a n y₀ z) :=
  (measurable_krDens_prod ν hJ hf β a n).comp (measurable_id.prodMk measurable_const)

theorem measurable_krDens_right (hJ : MeasurableSet J) (hf : Measurable f) (β a : ℝ) (n : ℕ)
    (y₀ : ℝ) : Measurable (fun z : ℝ => krDens J ν f β a n y₀ z) :=
  (measurable_krDens_prod ν hJ hf β a n).comp (measurable_const.prodMk measurable_id)

/-- **The density represents the row**: for `ν = f dx` with `0 ≤ f ≤ D`, bounded measurable `φ`
and an interval-like `J` of finite measure,
`krRow … (n+1) φ y₀ = ∫ krDens (n+1) y₀ z φ(z) dz` for **every** `y₀`. -/
theorem krRow_succ_eq_integral_krDens (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (n : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) (y₀ : ℝ) :
    krRow J (ν : Measure ℝ) β a (n + 1) φ y₀ = ∫ z, krDens J ν f β a (n + 1) y₀ z * φ z := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hD0 : 0 ≤ D / |a| := div_nonneg ((hf0 0).trans (hfD 0)) (abs_nonneg _)
  -- the stepped test
  set ψ : ℝ → ℝ := krStep J (ν : Measure ℝ) β a (J.indicator φ) with hψ
  have hψe : ∀ y, ψ y = ∫ z, krKer J f β a y z * φ z := fun y =>
    krStep_indicator_eq_integral hf hf0 hν ha φ y
  have hker : Measurable (fun p : ℝ × ℝ => krKer J f β a p.1 p.2 * φ p.2) :=
    (measurable_krKer_prod hJ hf β a).mul (hφ.comp measurable_snd)
  have hψm : Measurable ψ := by
    have e : ψ = fun y => ∫ z, krKer J f β a y z * φ z := funext hψe
    rw [e]
    exact hker.stronglyMeasurable.integral_prod_right'.measurable
  have hψb : ∀ y, |ψ y| ≤ M := by
    intro y
    have h := abs_krRow_le hJ ν β a 1 hφ hM y
    rwa [krRow_succ, krRow_zero] at h
  rw [krRow_succ_eq_krRow_krStep, ← hψ, krRow_eq_integral hJ ν β a n hψm hψb y₀]
  simp only [krDens_succ]
  -- Fubini
  have hint : Integrable (Function.uncurry fun (g : ℕ → ℝ) (z : ℝ) =>
      krAlive J β a n y₀ g * krKer J f β a (kWalk y₀ β a g n) z * φ z)
      ((iidLaw ν).prod volume) := by
    have hdom : Integrable (fun p : (ℕ → ℝ) × ℝ => D / |a| * M * J.indicator (fun _ => (1 : ℝ)) p.2)
        ((iidLaw ν).prod volume) := by
      refine Integrable.const_mul ?_ _
      refine Integrable.comp_snd ?_ (iidLaw ν)
      rw [integrable_indicator_iff hJ]
      exact integrableOn_const hJfin
    have hmeas : Measurable (Function.uncurry fun (g : ℕ → ℝ) (z : ℝ) =>
        krAlive J β a n y₀ g * krKer J f β a (kWalk y₀ β a g n) z * φ z) := by
      refine (((measurable_krAlive_right hJ β a n y₀).comp measurable_fst).mul
        ((measurable_krKer_prod hJ hf β a).comp
          (((measurable_kWalk_prod β a n).comp (measurable_const.prodMk measurable_id)).comp
            measurable_fst |>.prodMk measurable_snd))).mul (hφ.comp measurable_snd)
    refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨g, z⟩
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
    by_cases hz : z ∈ J
    · rw [indicator_of_mem hz, mul_one, abs_mul, abs_mul, abs_of_nonneg (krAlive_nonneg _ _ _)]
      have h1 : krAlive J β a n y₀ g * |krKer J f β a (kWalk y₀ β a g n) z| ≤ 1 * (D / |a|) :=
        mul_le_mul (krAlive_le_one _ _ _) (abs_krKer_le hf0 hfD _ _) (abs_nonneg _) zero_le_one
      calc krAlive J β a n y₀ g * |krKer J f β a (kWalk y₀ β a g n) z| * |φ z|
          ≤ 1 * (D / |a|) * M := mul_le_mul h1 (hM _) (abs_nonneg _) (by positivity)
        _ = D / |a| * M := by ring
    · rw [indicator_of_notMem hz, krKer_eq_zero_of_right_notMem hz]
      simp
  have hswap := integral_integral_swap hint
  calc ∫ g, krAlive J β a n y₀ g * ψ (kWalk y₀ β a g n) ∂(iidLaw ν)
      = ∫ g, ∫ z, krAlive J β a n y₀ g * krKer J f β a (kWalk y₀ β a g n) z * φ z ∂volume
          ∂(iidLaw ν) := by
        congr 1
        funext g
        rw [hψe, ← integral_const_mul]
        congr 1
        funext z
        ring
    _ = ∫ z, ∫ g, krAlive J β a n y₀ g * krKer J f β a (kWalk y₀ β a g n) z * φ z ∂(iidLaw ν)
          ∂volume := hswap
    _ = ∫ z, (∫ g, krAlive J β a n y₀ g * krKer J f β a (kWalk y₀ β a g n) z ∂(iidLaw ν)) *
          φ z := by
        congr 1
        funext z
        rw [← integral_mul_const]

/-- **Mass identity**: `∫ krDens (n+1) y₀ z dz = krSurv (n+1) y₀`. -/
theorem integral_krDens (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (n : ℕ) (y₀ : ℝ) :
    ∫ z, krDens J ν f β a (n + 1) y₀ z = krSurv J (ν : Measure ℝ) β a (n + 1) y₀ := by
  unfold krSurv
  rw [krRow_succ_eq_integral_krDens ν hJ hJfin hf hf0 hfD hν ha n measurable_const (M := 1)
    (fun _ => by simp) y₀]
  simp only [mul_one]

/-- `krDens (n+1) y₀ z ≤ (D/|a|) · krSurv n y₀`: the last step costs at most the density sup. -/
theorem krDens_le_div_mul_krSurv (hJ : MeasurableSet J) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfD : ∀ x, f x ≤ D) (n : ℕ) (y₀ z : ℝ) :
    krDens J ν f β a (n + 1) y₀ z ≤ D / |a| * krSurv J (ν : Measure ℝ) β a n y₀ := by
  rw [krDens_succ, krSurv_eq_integral hJ ν β a n y₀, ← integral_const_mul]
  refine integral_mono (kr_integrable_of_bdd ?_ (M := D / |a|) ?_)
    ((kr_integrable_of_bdd (measurable_krAlive_right hJ β a n y₀) (abs_krAlive_le_one n y₀)).const_mul
      _) fun g => ?_
  · exact (measurable_krAlive_right hJ β a n y₀).mul ((measurable_krKer_prod hJ hf β a).comp
      (((measurable_kWalk_prod β a n).comp (measurable_const.prodMk measurable_id)).prodMk
        measurable_const))
  · intro g
    rw [abs_mul, abs_of_nonneg (krAlive_nonneg _ _ _)]
    have hD0 : 0 ≤ D / |a| := div_nonneg ((hf0 0).trans (hfD 0)) (abs_nonneg _)
    calc _ ≤ 1 * (D / |a|) :=
          mul_le_mul (krAlive_le_one _ _ _) (abs_krKer_le hf0 hfD _ _) (abs_nonneg _) zero_le_one
      _ = D / |a| := one_mul _
  · rw [mul_comm (D / |a|)]
    exact mul_le_mul_of_nonneg_left (krKer_le hf0 hfD _ _) (krAlive_nonneg _ _ _)

end

end PGM
