import PLAStochastic.ForMathlib.Probability.StoppedSum.IndepIncrements
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Wald's identity for `ℕ∞`-valued stopping indices

Segment lengths take values in `ℕ∞` (`⊤` when the segment never ends).  A stopping
index is a map `T : Ω → ℕ∞` whose events `{t < T}` are `F t`-measurable, and the
stopped sum is the series `∑' t, 1{t < T} * Y t`, written with `Set.indicator`.

* `lintegral_enat_eq_tsum`: `E[T] = ∑' t, P(t < T)` for any measurable `T : Ω → ℕ∞`.
* `wald_lintegral`: nonnegative Wald identity in `ℝ≥0∞`, no integrability needed.
* `wald_integral_truncated`: `E[∑_{t<n} 1{t<T} Y t] = μ0 * ∑_{t<n} P(t < T)`.
* `wald_ae_lt_top`, `wald_ae_summable`, `wald_integrable`, `wald_integral`, `wald`:
  the real Wald identity `E[∑' t, 1{t<T} Y t] = μ0 * E[T]` when `E[T] < ∞` and
  `E|Y t| ≤ c` uniformly.

No finiteness of `P` is used: the product rule for independent factors holds for any
measure.
-/

namespace PGM

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `n = ∑' t, 1{t < n}` in `ℝ≥0∞` for `n : ℕ∞`. -/
theorem wald_tsum_ite_lt (n : ℕ∞) :
    ∑' t : ℕ, (if (t : ℕ∞) < n then (1 : ℝ≥0∞) else 0) = (n : ℝ≥0∞) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k =>
    rw [tsum_eq_sum (s := Finset.range k)]
    · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
      · simp
      · intro t ht
        simp [Finset.mem_range.1 ht]
    · intro t ht
      simp only [Finset.mem_range, not_lt] at ht
      simp [ht]

/-- An `ℕ∞`-valued map is measurable once all events `{t < T}` are measurable. -/
theorem wald_measurable_of_lt {T : Ω → ℕ∞}
    (hT : ∀ t : ℕ, MeasurableSet {ω | (t : ℕ∞) < T ω}) : Measurable T := by
  refine measurable_to_countable' fun x => ?_
  induction x using ENat.recTopCoe with
  | top =>
    have : T ⁻¹' {⊤} = ⋂ t : ℕ, {ω | (t : ℕ∞) < T ω} := by
      ext ω
      simp [ENat.eq_top_iff_forall_gt]
    rw [this]
    exact MeasurableSet.iInter hT
  | coe k =>
    have : T ⁻¹' {(k : ℕ∞)} =
        {ω | (k : ℕ∞) < T ω}ᶜ ∩ ⋂ j ∈ Finset.range k, {ω | (j : ℕ∞) < T ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
      induction T ω using ENat.recTopCoe with
      | top => simp
      | coe m =>
        simp only [Nat.cast_inj, Nat.cast_lt, not_lt]
        constructor
        · rintro rfl
          exact ⟨le_rfl, fun j hj => hj⟩
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge m k with hmk | hmk
          · exact absurd (h2 m hmk) (lt_irrefl m)
          · omega
    rw [this]
    exact (hT k).compl.inter
      (MeasurableSet.biInter (Finset.range k).countable_toSet fun j _ => hT j)

/-- The Lebesgue integral of an `ℕ∞`-valued map is the sum of its tail probabilities. -/
theorem lintegral_enat_eq_tsum {P : Measure Ω} {T : Ω → ℕ∞} (hT : Measurable T) :
    ∫⁻ ω, (T ω : ℝ≥0∞) ∂P = ∑' t : ℕ, P {ω | (t : ℕ∞) < T ω} := by
  have hs : ∀ t : ℕ, MeasurableSet {ω | (t : ℕ∞) < T ω} := fun t =>
    hT (MeasurableSet.of_discrete : MeasurableSet (Set.Ioi (t : ℕ∞)))
  calc ∫⁻ ω, (T ω : ℝ≥0∞) ∂P
      = ∫⁻ ω, ∑' t : ℕ, Set.indicator {ω | (t : ℕ∞) < T ω} 1 ω ∂P := by
        congr 1
        ext ω
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
        exact (wald_tsum_ite_lt _).symm
    _ = ∑' t : ℕ, ∫⁻ ω, Set.indicator {ω | (t : ℕ∞) < T ω} 1 ω ∂P :=
        lintegral_tsum fun t => (measurable_one.indicator (hs t)).aemeasurable
    _ = ∑' t : ℕ, P {ω | (t : ℕ∞) < T ω} := by
        simp_rw [lintegral_indicator_one (hs _)]

/-- Finite expected length forces a finite length almost surely. -/
theorem wald_ae_lt_top {P : Measure Ω} {T : Ω → ℕ∞} (hTm : Measurable T)
    (hTfin : ∫⁻ ω, (T ω : ℝ≥0∞) ∂P ≠ ∞) : ∀ᵐ ω ∂P, T ω < ⊤ := by
  filter_upwards [ae_lt_top (Measurable.of_discrete.comp hTm) hTfin] with ω hω
  exact ENat.toENNReal_lt_top.1 hω

omit mΩ in
/-- On `{T = n}` the stopped series is the finite partial sum `Y 0 + ⋯ + Y (n - 1)`. -/
theorem wald_hasSum_indicator (Y : ℕ → Ω → ℝ) {T : Ω → ℕ∞} {ω : Ω} {n : ℕ} (hn : T ω = n) :
    HasSum (fun t : ℕ => Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω) (partialSum Y n ω) := by
  have hsum : partialSum Y n ω
      = ∑ t ∈ Finset.range n, Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω := by
    unfold partialSum
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Set.indicator_of_mem]
    simpa [hn] using Finset.mem_range.1 ht
  rw [hsum]
  refine hasSum_sum_of_ne_finset_zero fun t ht => ?_
  rw [Set.indicator_of_notMem]
  simpa [hn] using Finset.mem_range.not.1 ht

/-- The stopped series is almost surely a finite sum when the expected length is finite. -/
theorem wald_ae_summable (Y : ℕ → Ω → ℝ) {P : Measure Ω} {T : Ω → ℕ∞} (hTm : Measurable T)
    (hTfin : ∫⁻ ω, (T ω : ℝ≥0∞) ∂P ≠ ∞) :
    ∀ᵐ ω ∂P, Summable (fun t : ℕ => Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω) := by
  filter_upwards [wald_ae_lt_top hTm hTfin] with ω hω
  lift T ω to ℕ using hω.ne with n hn
  exact (wald_hasSum_indicator Y hn.symm).summable

section Wald

variable {P : Measure Ω} {F : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ} {T : Ω → ℕ∞}

/-- `E[1{t<T} f(Y t)] = E[f(Y t)] P(t < T)`, by independence of `Y t` from `F t`. -/
theorem wald_lintegral_indicator (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    (t : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, Set.indicator {ω | (t : ℕ∞) < T ω} (fun ω => f (Y t ω)) ω ∂P
      = (∫⁻ ω, f (Y t ω) ∂P) * P {ω | (t : ℕ∞) < T ω} := by
  have hYm : Measurable (Y t) := (h.measurable t).mono (F.le _) le_rfl
  have hind := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (f := fun ω => f (Y t ω)) (g := Set.indicator {ω | (t : ℕ∞) < T ω} fun _ => 1)
    (measurable_iff_comap_le.1 hYm) (F.le t) (h.indep t)
    (hf.comp (comap_measurable (Y t))) (measurable_const.indicator (hT t))
  rw [lintegral_indicator_const ((F.le t) _ (hT t)), one_mul] at hind
  rw [← hind]
  congr 1
  ext ω
  by_cases hω : (t : ℕ∞) < T ω <;> simp [hω]

/-- Tonelli form of the stopped series for a nonnegative transform `f` of the increments. -/
theorem wald_lintegral_tsum (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, ∑' t : ℕ, Set.indicator {ω | (t : ℕ∞) < T ω} (fun ω => f (Y t ω)) ω ∂P
      = ∑' t : ℕ, (∫⁻ ω, f (Y t ω) ∂P) * P {ω | (t : ℕ∞) < T ω} := by
  rw [lintegral_tsum]
  · simp_rw [wald_lintegral_indicator h hT _ hf]
  · intro t
    exact ((hf.comp ((h.measurable t).mono (F.le _) le_rfl)).indicator
      (F.le t _ (hT t))).aemeasurable

/-- **Wald's identity, nonnegative form.** -/
theorem wald_lintegral (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    {m : ℝ≥0∞} (hm : ∀ t, ∫⁻ ω, ENNReal.ofReal (Y t ω) ∂P = m) :
    ∫⁻ ω, ∑' t : ℕ, Set.indicator {ω | (t : ℕ∞) < T ω} (fun ω => ENNReal.ofReal (Y t ω)) ω ∂P
      = m * ∫⁻ ω, (T ω : ℝ≥0∞) ∂P := by
  have hTm : Measurable T := wald_measurable_of_lt fun t => F.le t _ (hT t)
  rw [wald_lintegral_tsum h hT ENNReal.measurable_ofReal, lintegral_enat_eq_tsum hTm,
    ← ENNReal.tsum_mul_left]
  simp_rw [hm]

/-- `E[1{t<T} Y t] = P(t < T) E[Y t]`, by independence of `Y t` from `F t`. -/
theorem wald_integral_indicator (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω}) (t : ℕ) :
    ∫ ω, Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω ∂P
      = P.real {ω | (t : ℕ∞) < T ω} * ∫ ω, Y t ω ∂P := by
  have hYm : Measurable (Y t) := (h.measurable t).mono (F.le _) le_rfl
  have hZ : Measurable[F t] (Set.indicator {ω | (t : ℕ∞) < T ω} fun _ => (1 : ℝ)) :=
    measurable_const.indicator (hT t)
  have hmul := h.integral_mul_past t hZ hYm
  rw [integral_indicator_const _ ((F.le t) _ (hT t)), smul_eq_mul, mul_one] at hmul
  rw [← hmul]
  congr 1
  ext ω
  by_cases hω : (t : ℕ∞) < T ω <;> simp [hω]

/-- **Wald's identity for the truncated stopped sum.** -/
theorem wald_integral_truncated (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    (hint : ∀ t, Integrable (Y t) P) {μ0 : ℝ} (hmean : ∀ t, ∫ ω, Y t ω ∂P = μ0) (n : ℕ) :
    ∫ ω, ∑ t ∈ Finset.range n, Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω ∂P
      = μ0 * ∑ t ∈ Finset.range n, P.real {ω | (t : ℕ∞) < T ω} := by
  rw [integral_finsetSum _ fun t _ => (hint t).indicator ((F.le t) _ (hT t)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [wald_integral_indicator h hT t, hmean, mul_comm]

/-- Domination of the stopped series by `c * E[T]` under `E|Y t| ≤ c`. -/
theorem wald_lintegral_enorm_le (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    (hint : ∀ t, Integrable (Y t) P) {c : ℝ} (habs : ∀ t, ∫ ω, |Y t ω| ∂P ≤ c) :
    ∫⁻ ω, ∑' t : ℕ, ‖Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω‖ₑ ∂P
      ≤ ENNReal.ofReal c * ∫⁻ ω, (T ω : ℝ≥0∞) ∂P := by
  have hTm : Measurable T := wald_measurable_of_lt fun t => F.le t _ (hT t)
  have e : ∀ (t : ℕ) (ω : Ω), ‖Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω‖ₑ
      = Set.indicator {ω | (t : ℕ∞) < T ω} (fun ω => ‖Y t ω‖ₑ) ω := fun t ω => by
    by_cases hω : (t : ℕ∞) < T ω <;> simp [hω]
  simp_rw [e]
  rw [wald_lintegral_tsum h hT measurable_enorm, lintegral_enat_eq_tsum hTm,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun t => ?_
  gcongr
  rw [← ofReal_integral_norm_eq_lintegral_enorm (hint t)]
  exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using habs t)

/-- **Wald's identity, integrability of the stopped sum.** -/
theorem wald_integrable (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    (hint : ∀ t, Integrable (Y t) P) {c : ℝ} (habs : ∀ t, ∫ ω, |Y t ω| ∂P ≤ c)
    (hTfin : ∫⁻ ω, (T ω : ℝ≥0∞) ∂P ≠ ∞) :
    Integrable (fun ω => ∑' t : ℕ, Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω) P := by
  have hTm : Measurable T := wald_measurable_of_lt fun t => F.le t _ (hT t)
  have hmeas : ∀ t : ℕ, Measurable (Set.indicator {ω | (t : ℕ∞) < T ω} (Y t)) := fun t =>
    ((h.measurable t).mono (F.le _) le_rfl).indicator (F.le t _ (hT t))
  refine ⟨?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n ω => ∑ t ∈ Finset.range n, Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω)
      (fun n => (Finset.measurable_fun_sum _ fun t _ => hmeas t).aestronglyMeasurable) ?_
    filter_upwards [wald_ae_summable Y hTm hTfin] with ω hω
    exact hω.hasSum.tendsto_sum_nat
  · calc ∫⁻ ω, ‖∑' t : ℕ, Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω‖ₑ ∂P
        ≤ ∫⁻ ω, ∑' t : ℕ, ‖Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω‖ₑ ∂P :=
          lintegral_mono fun ω => enorm_tsum_le_tsum_enorm
      _ ≤ ENNReal.ofReal c * ∫⁻ ω, (T ω : ℝ≥0∞) ∂P := wald_lintegral_enorm_le h hT hint habs
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hTfin.lt_top

/-- **Wald's identity, real form.** -/
theorem wald_integral (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    (hint : ∀ t, Integrable (Y t) P) {μ0 : ℝ} (hmean : ∀ t, ∫ ω, Y t ω ∂P = μ0)
    {c : ℝ} (habs : ∀ t, ∫ ω, |Y t ω| ∂P ≤ c) (hTfin : ∫⁻ ω, (T ω : ℝ≥0∞) ∂P ≠ ∞) :
    ∫ ω, ∑' t : ℕ, Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω ∂P
      = μ0 * (∫⁻ ω, (T ω : ℝ≥0∞) ∂P).toReal := by
  have hTm : Measurable T := wald_measurable_of_lt fun t => F.le t _ (hT t)
  have hmeas : ∀ t : ℕ, Measurable (Set.indicator {ω | (t : ℕ∞) < T ω} (Y t)) := fun t =>
    ((h.measurable t).mono (F.le _) le_rfl).indicator (F.le t _ (hT t))
  have hfin : ∑' t : ℕ, ∫⁻ ω, ‖Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω‖ₑ ∂P ≠ ∞ := by
    rw [← lintegral_tsum fun t => (hmeas t).enorm.aemeasurable]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTfin)
      (wald_lintegral_enorm_le h hT hint habs)
  have hTsum := hTfin
  rw [lintegral_enat_eq_tsum hTm] at hTsum
  rw [integral_tsum (fun t => (hmeas t).aestronglyMeasurable) hfin]
  simp_rw [wald_integral_indicator h hT, hmean]
  rw [tsum_mul_right, mul_comm, lintegral_enat_eq_tsum hTm,
    ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hTsum)]
  rfl

/-- **Wald's identity** for an `ℕ∞`-valued stopping index with finite expected length:
the length is a.s. finite, the stopped series is a.s. a finite sum, the stopped sum is
integrable, and its mean is `μ0 * E[T]`. -/
theorem wald (h : IndepIncrements P F Y)
    (hT : ∀ t : ℕ, MeasurableSet[F t] {ω | (t : ℕ∞) < T ω})
    (hint : ∀ t, Integrable (Y t) P) {μ0 : ℝ} (hmean : ∀ t, ∫ ω, Y t ω ∂P = μ0)
    {c : ℝ} (habs : ∀ t, ∫ ω, |Y t ω| ∂P ≤ c) (hTfin : ∫⁻ ω, (T ω : ℝ≥0∞) ∂P ≠ ∞) :
    (∀ᵐ ω ∂P, T ω < ⊤) ∧
      (∀ᵐ ω ∂P, Summable fun t : ℕ => Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω) ∧
      Integrable (fun ω => ∑' t : ℕ, Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω) P ∧
      ∫ ω, ∑' t : ℕ, Set.indicator {ω | (t : ℕ∞) < T ω} (Y t) ω ∂P
        = μ0 * (∫⁻ ω, (T ω : ℝ≥0∞) ∂P).toReal := by
  have hTm : Measurable T := wald_measurable_of_lt fun t => F.le t _ (hT t)
  exact ⟨wald_ae_lt_top hTm hTfin, wald_ae_summable Y hTm hTfin,
    wald_integrable h hT hint habs hTfin, wald_integral h hT hint hmean habs hTfin⟩

end Wald

end PGM
