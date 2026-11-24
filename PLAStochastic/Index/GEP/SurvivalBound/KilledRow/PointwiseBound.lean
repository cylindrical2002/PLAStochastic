import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.L2Gap

/-!
# WP4 `SurvivalBound`: the pointwise bound of the complex killed row (mixed decomposition)

Source: `research/2026-09-28-gep-closure/mixed-kernel-response.md` §2;
`rawdisc-design.md` §2.2.

Split the killed step `P = kStepZ J ν σ z β a` as `P = P₀ + R`, `P₀ v = (1 - z) kStep J ν v`,
`R v = z kStep J σ v`.  With `ν = f dx`, `0 ≤ f ≤ D`, Cauchy–Schwarz gives at **every** point `y`

`‖kStep J ν β a v y‖² ≤ (D/|a|) ∫ ‖v‖²`  (`kill_norm_integral_density_sq_le`),

and `‖R v‖ ≤ ‖z‖ sup ‖v‖`.  If `P` contracts `L²` by `λ²` on bounded functions supported in `J`
(hypothesis `hL2`), then `∫ ‖Pⁿ(1_J φ)‖² ≤ λ^{2n} |J|`, and the recursion
`Pⁿ⁺¹ψ = P₀(Pⁿψ) + R(Pⁿψ)` gives by induction (no linearity of `P` is needed)

`‖kRow J ν σ z β a n φ y‖ ≤ 3 √(D w / a₀) λ^{n-1} + ‖z‖ⁿ`   (`n ≥ 1`, all `y`, `‖φ‖ ≤ 1`)

when `|J| ≤ w`, `|a| ≥ a₀ > 0`, `‖z‖ ≤ 1/2`, `‖z‖ ≤ λ/2` (`norm_kRow_le`).  The step law `σ`
needs no density.  Combined with the killed gap (`integral_norm_kStepZ_sq_le_gap`) this gives
`norm_kRow_le_gap` on `J = [α, α + w]` with `λ = √(1 - c₁/w²)`, and
`λ^{n-1} ≤ exp(-c₁ (n-1)/(2w²))` (`norm_kRow_le_gap_exp`).  Without a gap (`‖m‖ ≤ 1`) the same
argument with `λ = 1` gives `3 √(D w / a₀) + ‖z‖ⁿ` (`norm_kRow_le_of_mult_le_one`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {J : Set ℝ} {ν σ : Measure ℝ} {z : ℂ} {β a : ℝ}

/-- `kStep` is the indicator of the measure convolution. -/
theorem kStep_eq_indicator_kConv (J : Set ℝ) (ρ : Measure ℝ) (β a : ℝ) (u : ℝ → ℂ) :
    kStep J ρ β a u = J.indicator (kConv ρ β a u) := rfl

theorem measurable_kStep (hJ : MeasurableSet J) (ρ : Measure ℝ) [SFinite ρ] {u : ℝ → ℂ}
    (hu : Measurable u) : Measurable (kStep J ρ β a u) :=
  (measurable_kConv ρ hu β a).indicator hJ

theorem measurable_kStepZ (hJ : MeasurableSet J) [SFinite ν] [SFinite σ] {u : ℝ → ℂ}
    (hu : Measurable u) : Measurable (kStepZ J ν σ z β a u) := by
  unfold kStepZ
  exact ((measurable_kStep hJ ν hu).const_mul _).add ((measurable_kStep hJ σ hu).const_mul _)

theorem kStepZ_eq_zero_of_notMem {u : ℝ → ℂ} {y : ℝ} (hy : y ∉ J) :
    kStepZ J ν σ z β a u y = 0 := by
  unfold kStepZ kStep
  simp [indicator_of_notMem hy]

/-- A probability step does not increase the sup norm. -/
theorem norm_kStep_le {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {u : ℝ → ℂ} {M : ℝ}
    (hM : ∀ y, ‖u y‖ ≤ M) (y : ℝ) : ‖kStep J ρ β a u y‖ ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  unfold kStep
  by_cases hy : y ∈ J
  · rw [indicator_of_mem hy]
    have h := norm_integral_le_of_norm_le_const (μ := ρ)
      (f := fun x => u (y + β - a * x)) (C := M) (Filter.Eventually.of_forall fun x => hM _)
    rwa [probReal_univ, mul_one] at h
  · rw [indicator_of_notMem hy, norm_zero]; exact hM0

/-- A bounded measurable function supported in a set of finite measure is square integrable. -/
theorem kill_integrable_sq_of_bdd (hJfin : volume J ≠ ⊤) {v : ℝ → ℂ} (hv : Measurable v)
    (hsupp : ∀ y, y ∉ J → v y = 0) {M : ℝ} (hM : ∀ y, ‖v y‖ ≤ M) :
    Integrable (fun y => ‖v y‖ ^ 2) := by
  have hsub : Function.support (fun y => ‖v y‖ ^ 2) ⊆ J := by
    intro y hy
    by_contra h
    exact hy (by simp [hsupp y h])
  rw [← integrableOn_iff_integrable_of_support_subset hsub]
  have : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.2 hJfin
  refine (integrable_const (M ^ 2)).mono' (hv.norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM y) 2

/-- **Pointwise Cauchy–Schwarz for a bounded density.**  If `ν = f dx` with `0 ≤ f ≤ D` is a
probability measure and `a ≠ 0`, then for every `y`,
`‖∫ v(y + β - a x) dν(x)‖² ≤ (D/|a|) ∫ ‖v‖²` (`v` bounded measurable, square integrable). -/
theorem kill_norm_integral_density_sq_le {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (f x))) [IsProbabilityMeasure ν]
    (ha : a ≠ 0) {v : ℝ → ℂ} (hv : Measurable v) (hv2 : Integrable (fun y => ‖v y‖ ^ 2))
    {M : ℝ} (hM : ∀ y, ‖v y‖ ≤ M) (y : ℝ) :
    ‖∫ x, v (y + β - a * x) ∂ν‖ ^ 2 ≤ D / |a| * ∫ s, ‖v s‖ ^ 2 := by
  set g : ℝ → ℝ := fun x => ‖v (y + β - a * x)‖ with hg
  have hgm : Measurable g := (hv.comp (by fun_prop)).norm
  have hg1 : Integrable g ν :=
    (integrable_const M).mono' hgm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [hg, norm_norm]; exact hM _)
  have hg2 : Integrable (fun x => g x ^ 2) ν :=
    (integrable_const (M ^ 2)).mono' (hgm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hM _) 2)
  have h1 : ‖∫ x, v (y + β - a * x) ∂ν‖ ≤ ∫ x, g x ∂ν := norm_integral_le_integral_norm _
  have h2 := kill_sq_integral_le hg1 hg2
  rw [probReal_univ, one_mul] at h2
  -- the density
  have hdens : ∫ x, g x ^ 2 ∂ν = ∫ x, f x * g x ^ 2 := by
    rw [hν, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    congr 1
    funext x
    rw [ENNReal.toReal_ofReal (hf0 x), smul_eq_mul]
  -- the change of variables
  set H : ℝ → ℝ := fun s => ‖v s‖ ^ 2 with hH
  have hgH : ∀ x, g x ^ 2 = H ((y + β) + (-a) * x) := by
    intro x; rw [hg, hH]; congr 3; ring_nf
  have hHi : Integrable (fun x => H ((y + β) + (-a) * x)) :=
    (hv2.comp_add_left (y + β)).comp_mul_left' (neg_ne_zero.2 ha)
  have hcv : ∫ x, H ((y + β) + (-a) * x) = |a|⁻¹ * ∫ s, H s := by
    have := Measure.integral_comp_mul_left (fun s => H ((y + β) + s)) (-a)
    rw [this, integral_add_left_eq_self (fun s => H s) (y + β), smul_eq_mul, abs_inv, abs_neg]
  have hle : ∫ x, f x * g x ^ 2 ≤ ∫ x, D * H ((y + β) + (-a) * x) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) (hHi.const_mul D)
      (Filter.Eventually.of_forall fun x => ?_)
    · exact mul_nonneg (hf0 x) (sq_nonneg _)
    · simp only
      rw [← hgH]
      exact mul_le_mul_of_nonneg_right (hfD x) (sq_nonneg _)
  calc ‖∫ x, v (y + β - a * x) ∂ν‖ ^ 2 ≤ (∫ x, g x ∂ν) ^ 2 := by gcongr
    _ ≤ ∫ x, g x ^ 2 ∂ν := h2
    _ = ∫ x, f x * g x ^ 2 := hdens
    _ ≤ ∫ x, D * H ((y + β) + (-a) * x) := hle
    _ = D / |a| * ∫ s, ‖v s‖ ^ 2 := by
        rw [integral_const_mul, hcv, hH]; ring

/-- **Pointwise row bound (mixed decomposition, MK §2).**  Let `ν = f dx` be a probability
measure with `0 ≤ f ≤ D`, `σ` a probability measure, `J` measurable with `|J| ≤ w`,
`0 < a₀ ≤ |a|`, `‖z‖ ≤ 1/2`, `‖z‖ ≤ λ/2`, `λ > 0`, and assume the killed step contracts `L²` by
`λ²` on bounded measurable functions supported in `J`.  Then for measurable `φ` with `‖φ‖ ≤ 1`,
every `n ≥ 1` and **every** point `y`,
`‖kRow J ν σ z β a n φ y‖ ≤ 3 √(D w / a₀) λ^{n-1} + ‖z‖ⁿ`. -/
theorem norm_kRow_le {f : ℝ → ℝ} {D w a₀ lam : ℝ} (hJ : MeasurableSet J)
    (hJw : volume J ≤ ENNReal.ofReal w) (hw : 0 ≤ w) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfD : ∀ x, f x ≤ D) (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure σ] (ha₀ : 0 < a₀) (ha : a₀ ≤ |a|)
    (hz : ‖z‖ ≤ 1 / 2) (hzl : ‖z‖ ≤ lam / 2) (hl0 : 0 < lam)
    (hL2 : ∀ v : ℝ → ℂ, Measurable v → (∀ y, y ∉ J → v y = 0) → (∃ M, ∀ y, ‖v y‖ ≤ M) →
      ∫ y, ‖kStepZ J ν σ z β a v y‖ ^ 2 ≤ lam ^ 2 * ∫ y, ‖v y‖ ^ 2)
    {φ : ℝ → ℂ} (hφ : Measurable φ) (hφ1 : ∀ y, ‖φ y‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    ‖kRow J ν σ z β a n φ y‖ ≤ 3 * Real.sqrt (D * w / a₀) * lam ^ (n - 1) + ‖z‖ ^ n := by
  have hJfin : volume J ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hJw
  have hD : 0 ≤ D := (hf0 0).trans (hfD 0)
  have ha0 : a ≠ 0 := by
    intro h; rw [h, abs_zero] at ha; linarith
  set P := kStepZ J ν σ z β a with hP
  set ψ := J.indicator φ with hψ
  have hrow : ∀ m, kRow J ν σ z β a m φ = P^[m] ψ := fun m => rfl
  -- basic properties of the iterates
  have hprop : ∀ m, Measurable (P^[m] ψ) ∧ (∀ y, y ∉ J → P^[m] ψ y = 0) ∧
      ∃ M, ∀ y, ‖P^[m] ψ y‖ ≤ M := by
    intro m
    induction m with
    | zero =>
      refine ⟨hφ.indicator hJ, fun y hy => indicator_of_notMem hy _, 1, fun y => ?_⟩
      simp only [Function.iterate_zero, id_eq, hψ]
      exact (norm_indicator_le_norm_self _ _).trans (hφ1 y)
    | succ m ih =>
      obtain ⟨hm, -, M, hM⟩ := ih
      rw [Function.iterate_succ_apply']
      refine ⟨measurable_kStepZ hJ hm, fun y hy => kStepZ_eq_zero_of_notMem hy,
        ‖1 - z‖ * M + ‖z‖ * M, fun y => ?_⟩
      rw [hP]
      unfold kStepZ
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      gcongr
      · exact norm_kStep_le hM y
      · exact norm_kStep_le hM y
  -- `L²` norms of the iterates
  have hψ2 : ∫ y, ‖ψ y‖ ^ 2 ≤ w := by
    have hind : Integrable (J.indicator fun _ => (1 : ℝ)) :=
      (integrableOn_const (C := (1 : ℝ)) hJfin).integrable_indicator hJ
    calc ∫ y, ‖ψ y‖ ^ 2 ≤ ∫ y, J.indicator (fun _ => (1 : ℝ)) y := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
            hind (Filter.Eventually.of_forall fun y => ?_)
          by_cases hy : y ∈ J
          · simp only [hψ, indicator_of_mem hy]
            have := hφ1 y
            nlinarith [norm_nonneg (φ y)]
          · simp [hψ, indicator_of_notMem hy]
      _ = volume.real J := by rw [integral_indicator_const _ hJ, smul_eq_mul, mul_one]
      _ ≤ w := ENNReal.toReal_le_of_le_ofReal hw hJw
  have hL2n : ∀ m, ∫ y, ‖P^[m] ψ y‖ ^ 2 ≤ lam ^ (2 * m) * w := by
    intro m
    induction m with
    | zero => simpa using hψ2
    | succ m ih =>
      obtain ⟨hm, hsupp, hbd⟩ := hprop m
      rw [Function.iterate_succ_apply']
      calc ∫ y, ‖P (P^[m] ψ) y‖ ^ 2 ≤ lam ^ 2 * ∫ y, ‖P^[m] ψ y‖ ^ 2 :=
            hL2 _ hm hsupp hbd
        _ ≤ lam ^ 2 * (lam ^ (2 * m) * w) := by gcongr
        _ = lam ^ (2 * (m + 1)) * w := by ring
  -- the `ν`-part at every point
  set S := Real.sqrt (D * w / a₀) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hP0 : ∀ m y, ‖kStep J ν β a (P^[m] ψ) y‖ ≤ S * lam ^ m := by
    intro m y
    obtain ⟨hm, hsupp, M, hM⟩ := hprop m
    have hv2 := kill_integrable_sq_of_bdd hJfin hm hsupp hM
    have hsq : ‖kStep J ν β a (P^[m] ψ) y‖ ^ 2 ≤ (S * lam ^ m) ^ 2 := by
      have hk : ‖kStep J ν β a (P^[m] ψ) y‖ ≤ ‖∫ x, P^[m] ψ (y + β - a * x) ∂ν‖ := by
        unfold kStep
        exact norm_indicator_le_norm_self _ _
      have hd := kill_norm_integral_density_sq_le (β := β) hf hf0 hfD hν ha0 hm hv2 hM y
      have hDa : D / |a| ≤ D / a₀ := div_le_div_of_nonneg_left hD ha₀ ha
      have hint0 : 0 ≤ ∫ s, ‖P^[m] ψ s‖ ^ 2 := integral_nonneg fun s => by positivity
      calc ‖kStep J ν β a (P^[m] ψ) y‖ ^ 2 ≤ ‖∫ x, P^[m] ψ (y + β - a * x) ∂ν‖ ^ 2 := by
            gcongr
        _ ≤ D / |a| * ∫ s, ‖P^[m] ψ s‖ ^ 2 := hd
        _ ≤ D / a₀ * (lam ^ (2 * m) * w) :=
            mul_le_mul hDa (hL2n m) hint0 (by positivity)
        _ = (S * lam ^ m) ^ 2 := by
            rw [mul_pow, hS, Real.sq_sqrt (by positivity)]
            ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq
  have h1z : ‖1 - z‖ ≤ 3 / 2 := by
    calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ 3 / 2 := by rw [norm_one]; linarith
  -- one step of the recursion
  have hstep : ∀ m (B : ℝ), (∀ y, ‖P^[m] ψ y‖ ≤ B) → ∀ y,
      ‖P^[m + 1] ψ y‖ ≤ 3 / 2 * (S * lam ^ m) + ‖z‖ * B := by
    intro m B hB y
    rw [Function.iterate_succ_apply', hP]
    unfold kStepZ
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    gcongr
    · exact hP0 m y
    · exact norm_kStep_le hB y
  -- the induction on `n ≥ 1`
  have hmain : ∀ n, 1 ≤ n → ∀ y, ‖P^[n] ψ y‖ ≤ 3 * S * lam ^ (n - 1) + ‖z‖ ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro y
      have h0 : ∀ y, ‖P^[0] ψ y‖ ≤ 1 := by
        intro y
        simp only [Function.iterate_zero, id_eq, hψ]
        exact (norm_indicator_le_norm_self _ _).trans (hφ1 y)
      have := hstep 0 1 h0 y
      simp only [zero_add, pow_zero, mul_one] at this
      simp only [le_refl, tsub_eq_zero_of_le, pow_zero, mul_one, pow_one]
      nlinarith
    | succ n hn ih =>
      intro y
      have := hstep n _ ih y
      have hn' : n + 1 - 1 = n := by omega
      rw [hn']
      have hlp : lam ^ n = lam ^ (n - 1) * lam := by
        rw [← pow_succ]; congr 1; omega
      have hz0 := norm_nonneg z
      have hl : 0 ≤ lam ^ (n - 1) := by positivity
      calc ‖P^[n + 1] ψ y‖ ≤ 3 / 2 * (S * lam ^ n) + ‖z‖ * (3 * S * lam ^ (n - 1) + ‖z‖ ^ n) :=
            this
        _ = 3 / 2 * (S * lam ^ n) + ‖z‖ * (3 * S * lam ^ (n - 1)) + ‖z‖ ^ (n + 1) := by ring
        _ ≤ 3 / 2 * (S * lam ^ n) + lam / 2 * (3 * S * lam ^ (n - 1)) + ‖z‖ ^ (n + 1) := by
            gcongr
        _ = 3 * S * lam ^ n + ‖z‖ ^ (n + 1) := by rw [hlp]; ring
  rw [hrow]
  have := hmain n hn y
  simpa [hS, mul_assoc] using this

/-- **Row bound with coefficient one.**  If the multiplier satisfies
`‖(1 - z) φ_ν(t) + z φ_σ(t)‖ ≤ 1` for all `t` (no gap), then under the hypotheses of
`norm_kRow_le` with `λ = 1` (`‖z‖ ≤ 1/2`): `‖kRow J ν σ z β a n φ y‖ ≤ 3 √(D w / a₀) + ‖z‖ⁿ`
for `n ≥ 1` and every `y`. -/
theorem norm_kRow_le_of_mult_le_one {f : ℝ → ℝ} {D w a₀ : ℝ} (hJ : MeasurableSet J)
    (hJw : volume J ≤ ENNReal.ofReal w) (hw : 0 ≤ w) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfD : ∀ x, f x ≤ D) (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure σ] (ha₀ : 0 < a₀) (ha : a₀ ≤ |a|)
    (hz : ‖z‖ ≤ 1 / 2)
    (hm : ∀ t : ℝ, ‖(1 - z) * charFun ν t + z * charFun σ t‖ ≤ 1)
    {φ : ℝ → ℂ} (hφ : Measurable φ) (hφ1 : ∀ y, ‖φ y‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) (y : ℝ) :
    ‖kRow J ν σ z β a n φ y‖ ≤ 3 * Real.sqrt (D * w / a₀) + ‖z‖ ^ n := by
  have hJfin : volume J ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hJw
  have hL2 : ∀ v : ℝ → ℂ, Measurable v → (∀ y, y ∉ J → v y = 0) → (∃ M, ∀ y, ‖v y‖ ≤ M) →
      ∫ y, ‖kStepZ J ν σ z β a v y‖ ^ 2 ≤ (1 : ℝ) ^ 2 * ∫ y, ‖v y‖ ^ 2 := by
    intro v hv hsupp ⟨M, hM⟩
    have hv2 := kill_integrable_sq_of_bdd hJfin hv hsupp hM
    have hmem : MemLp v 2 := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).2 hv2
    have h1 : Integrable v := kill_integrable_of_support hJfin hsupp hmem
    rw [one_pow, one_mul]
    exact integral_norm_kStepZ_sq_le hm hv h1 hmem
  have h := norm_kRow_le (β := β) hJ hJw hw hf hf0 hfD hν ha₀ ha hz (by linarith) one_pos hL2
    hφ hφ1 hn y
  rwa [one_pow, mul_one] at h

/-- `√(1 - x) ≤ e^{-x/2}`. -/
theorem kill_sqrt_one_sub_le_exp (x : ℝ) :
    Real.sqrt (1 - x) ≤ Real.exp (-x / 2) := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : Real.exp (-x) = Real.exp (-x / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h2] at h1
  calc Real.sqrt (1 - x) ≤ Real.sqrt (Real.exp (-x / 2) ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
    _ = Real.exp (-x / 2) := Real.sqrt_sq (Real.exp_pos _).le

/-- **Row bound from the multiplier gap.**  On `J = [α, α + w]` (`w ≥ 1`), with `ν = f dx`
(`0 ≤ f ≤ D`) and `σ` probability measures, `0 < a₀ ≤ |a|`, `‖z‖ ≤ 1/3` and the multiplier gap
`‖(1 - z) φ_ν(t) + z φ_σ(t)‖² ≤ 1 - c min(t², 1)` (`0 < c ≤ 1`): for measurable `‖φ‖ ≤ 1`,
`n ≥ 1` and every `y`,
`‖kRow J ν σ z β a n φ y‖ ≤ 3 √(D w / a₀) λ^{n-1} + ‖z‖ⁿ`, `λ = √(1 - c₁/w²)`,
`c₁ = killGapConst c a₀`. -/
theorem norm_kRow_le_gap {f : ℝ → ℝ} {D α w a₀ c : ℝ} (hw : 1 ≤ w) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure σ] (ha₀ : 0 < a₀) (ha : a₀ ≤ |a|)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hgap : ∀ t : ℝ, ‖(1 - z) * charFun ν t + z * charFun σ t‖ ^ 2 ≤ 1 - c * min (t ^ 2) 1)
    (hz : ‖z‖ ≤ 1 / 3) {φ : ℝ → ℂ} (hφ : Measurable φ) (hφ1 : ∀ y, ‖φ y‖ ≤ 1) {n : ℕ}
    (hn : 1 ≤ n) (y : ℝ) :
    ‖kRow (Icc α (α + w)) ν σ z β a n φ y‖ ≤
      3 * Real.sqrt (D * w / a₀) * Real.sqrt (1 - killGapConst c a₀ / w ^ 2) ^ (n - 1) +
        ‖z‖ ^ n := by
  set c₁ := killGapConst c a₀ with hc₁
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw
  have hc₁le : c₁ / w ^ 2 ≤ 1 / 2 := by
    have hk : c₁ ≤ 1 / 2 := by
      rw [hc₁, killGapConst]
      have : min (Real.pi ^ 2 * a₀ ^ 2 / 4) 1 ≤ 1 := min_le_right _ _
      have : c * min (Real.pi ^ 2 * a₀ ^ 2 / 4) 1 ≤ 1 := by
        calc c * min (Real.pi ^ 2 * a₀ ^ 2 / 4) 1 ≤ 1 * 1 := by gcongr
          _ = 1 := one_mul 1
      linarith
    have hw2 : 1 ≤ w ^ 2 := by nlinarith
    calc c₁ / w ^ 2 ≤ c₁ / 1 := by
          gcongr
          exact (killGapConst_pos hc ha₀).le
      _ ≤ 1 / 2 := by rw [div_one]; exact hk
  set lam := Real.sqrt (1 - c₁ / w ^ 2) with hlam
  have hlam2 : lam ^ 2 = 1 - c₁ / w ^ 2 := Real.sq_sqrt (by linarith)
  have hlam0 : 0 < lam := Real.sqrt_pos.2 (by linarith)
  have hzl : ‖z‖ ≤ lam / 2 := by
    have : 2 / 3 ≤ lam := by
      rw [hlam]
      refine Real.le_sqrt_of_sq_le ?_
      linarith
    linarith
  have hL2 : ∀ v : ℝ → ℂ, Measurable v → (∀ y, y ∉ Icc α (α + w) → v y = 0) →
      (∃ M, ∀ y, ‖v y‖ ≤ M) →
      ∫ y, ‖kStepZ (Icc α (α + w)) ν σ z β a v y‖ ^ 2 ≤ lam ^ 2 * ∫ y, ‖v y‖ ^ 2 := by
    intro v hv hsupp ⟨M, hM⟩
    have hv2 := kill_integrable_sq_of_bdd
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hv hsupp hM
    rw [hlam2]
    exact integral_norm_kStepZ_sq_le_gap hw hc ha₀ ha hgap hv hsupp hv2
  have hJw : volume (Icc α (α + w)) ≤ ENNReal.ofReal w := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact norm_kRow_le measurableSet_Icc hJw hw0.le hf hf0 hfD hν ha₀ ha (by linarith) hzl hlam0
    hL2 hφ hφ1 hn y

/-- The row bound from the gap in exponential form:
`‖kRow J ν σ z β a n φ y‖ ≤ 3 √(D w / a₀) e^{-c₁ (n-1)/(2w²)} + ‖z‖ⁿ`. -/
theorem norm_kRow_le_gap_exp {f : ℝ → ℝ} {D α w a₀ c : ℝ} (hw : 1 ≤ w) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure σ] (ha₀ : 0 < a₀) (ha : a₀ ≤ |a|)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hgap : ∀ t : ℝ, ‖(1 - z) * charFun ν t + z * charFun σ t‖ ^ 2 ≤ 1 - c * min (t ^ 2) 1)
    (hz : ‖z‖ ≤ 1 / 3) {φ : ℝ → ℂ} (hφ : Measurable φ) (hφ1 : ∀ y, ‖φ y‖ ≤ 1) {n : ℕ}
    (hn : 1 ≤ n) (y : ℝ) :
    ‖kRow (Icc α (α + w)) ν σ z β a n φ y‖ ≤
      3 * Real.sqrt (D * w / a₀) *
          Real.exp (-(killGapConst c a₀ * ((n : ℝ) - 1) / (2 * w ^ 2))) + ‖z‖ ^ n := by
  refine (norm_kRow_le_gap (α := α) (β := β) hw hf hf0 hfD hν ha₀ ha hc hc1 hgap hz hφ hφ1 hn
    y).trans ?_
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw
  set x := killGapConst c a₀ / w ^ 2 with hx
  have hx1 : x ≤ 1 := by
    have hk : killGapConst c a₀ ≤ 1 := by
      unfold killGapConst
      have : min (Real.pi ^ 2 * a₀ ^ 2 / 4) 1 ≤ 1 := min_le_right _ _
      have : c * min (Real.pi ^ 2 * a₀ ^ 2 / 4) 1 ≤ 1 := by
        calc c * min (Real.pi ^ 2 * a₀ ^ 2 / 4) 1 ≤ 1 * 1 := by gcongr
          _ = 1 := one_mul 1
      linarith
    rw [hx, div_le_one (by positivity)]
    nlinarith
  have hs := kill_sqrt_one_sub_le_exp x
  have hpow : Real.sqrt (1 - x) ^ (n - 1) ≤ Real.exp (-x / 2) ^ (n - 1) :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hs _
  have hexp : Real.exp (-x / 2) ^ (n - 1) =
      Real.exp (-(killGapConst c a₀ * ((n : ℝ) - 1) / (2 * w ^ 2))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [Nat.cast_sub hn, hx]
    push_cast
    field_simp
  have hS0 : 0 ≤ Real.sqrt (D * w / a₀) := Real.sqrt_nonneg _
  gcongr
  rw [← hexp]
  exact hpow

end

end PGM
