import PLAStochastic.Index.GEP.Kernel.Row.ChapmanKolmogorov
import PLAStochastic.Index.GEP.OrbitClosure.CyclicReduction

/-!
# WP4 kernel rows: the free-density bound and survival × free-density products

Source: `influence-lipschitz.md` §3 ("结合自由密度 `K n^{-1/2}`").

Dropping the band constraint on all but the first block bounds the killed density by the free
sum density: for `ν = f dx` in the regular class and `n ≥ 2`,

`krDens (n+1) y₀ z ≤ L / (√n |a|)`  (`krDens_le_free`),

with `L` depending only on the class constants (via `locBd_convPow`; the small argument of
`kernel_regLaw_sum_density` is reproduced here so that this file depends only on compiled
modules).  Combined with Chapman–Kolmogorov:

* `krDens_add_le_krSurv_mul`: `q_{m+1+(n+1)}(y₀, z) ≤ s_{m+1}(y₀) · L/(√n |a|)`;
* `krDens_add_le_mul_krSurv_rev`: `q_{n+1+(m+1)}(y₀, z) ≤ L/(√n |a|) · s̃_{m+1}(z)` (reverse
  survival from the target);
* `krDens_three_block_le`: `q_{m+1+(j+1)+(k+1)}(y₀, z) ≤ s_{m+1}(y₀) · L/(√j |a|) · s̃_{k+1}(z)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {J : Set ℝ} {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

/-! ## Integrals against a locally bounded measure -/

theorem kr_integral_le_of_locBd {μ : Measure ℝ} {L : ℝ} (hL : 0 ≤ L) (hμ : LocBd L μ)
    {h : ℝ → ℝ} (hh : Measurable h) (h0 : ∀ x, 0 ≤ h x) (hint : Integrable h) :
    ∫ x, h x ∂μ ≤ L * ∫ x, h x := by
  have hle : μ ≤ (ENNReal.ofReal L) • volume := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul]
    exact hμ s hs
  have h1 : ∫ x, h x ∂μ = (∫⁻ x, ENNReal.ofReal (h x) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hh.aestronglyMeasurable
  have h2 : ∫ x, h x = (∫⁻ x, ENNReal.ofReal (h x)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hh.aestronglyMeasurable
  have hfin : ∫⁻ x, ENNReal.ofReal (h x) < ⊤ := by
    have := hint.hasFiniteIntegral
    rwa [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h0)] at this
  rw [h1, h2, ← ENNReal.toReal_ofReal hL, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) ?_
  calc ∫⁻ x, ENNReal.ofReal (h x) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (h x) ∂(ENNReal.ofReal L • volume) := lintegral_mono' hle le_rfl
    _ = ENNReal.ofReal L * ∫⁻ x, ENNReal.ofReal (h x) := lintegral_smul_measure _ _

/-! ## The density of a regular law -/

theorem kr_lintegral_density_eq_one
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∫⁻ x, ENNReal.ofReal (f x) = 1 := by
  have h := measure_univ (μ := (ν : Measure ℝ))
  rwa [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h

theorem kr_integrable_density (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    Integrable f := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0),
    kr_lintegral_density_eq_one ν hν]
  exact ENNReal.one_lt_top

theorem kr_integral_density_eq_one (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∫ x, f x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hf.aestronglyMeasurable,
    kr_lintegral_density_eq_one ν hν, ENNReal.toReal_one]

/-- The density of a regular law, with the bound `f ≤ D` made explicit. -/
theorem kr_regLaw_density {θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hν : RegLaw D θ vlo vhi ν) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, x ≤ 0 → f x = 0) ∧ (∀ x, f x ≤ D) ∧
      (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
      (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  obtain ⟨f, hf, hf0, hfz, hfe, hνf⟩ := hν.density
  refine ⟨f, hf, hf0, hfz, fun x => ?_, hfe, hνf⟩
  by_cases hx : x ≤ 0
  · rw [hfz x hx]; exact hD.le
  · push Not at hx
    refine (hfe x).trans ?_
    have : Real.exp (-θ * x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    nlinarith

/-! ## The class-uniform free sum density -/

theorem kr_exp_decay_le_sqrt {c n : ℝ} (hc : 0 < c) (hn : 1 ≤ n) :
    Real.exp (-c * (n - 2)) ≤ Real.exp (2 * c) / c / Real.sqrt n := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsn : Real.sqrt n ≤ n := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hn0.le).mp
    rw [Real.sq_sqrt hn0.le]
    nlinarith
  have he : c * Real.sqrt n ≤ Real.exp (c * n) := by
    have hmul := mul_le_mul_of_nonneg_left hsn hc.le
    linarith [Real.add_one_le_exp (c * n)]
  have hi : Real.exp (-c * n) ≤ (c * Real.sqrt n)⁻¹ := by
    rw [neg_mul, Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) (mul_pos hc hs)]
    exact he
  calc
    Real.exp (-c * (n - 2)) = Real.exp (2 * c) * Real.exp (-c * n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (2 * c) * (c * Real.sqrt n)⁻¹ :=
      mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
    _ = Real.exp (2 * c) / c / Real.sqrt n := by
      rw [div_div, div_eq_mul_inv, mul_inv]

/-- Free sums from the regular class have a common `L / √n` density bound for `n ≥ 2`
(reproduction of `kernel_regLaw_sum_density`, from `locBd_convPow`). -/
theorem kr_free_sum_density (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hv : vlo ≤ vhi) :
    ∃ L : ℝ, 0 < L ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ n : ℕ, 2 ≤ n → LocBd (L / Real.sqrt n) (convPow (ν : Measure ℝ) n) := by
  obtain ⟨L₀, c₂, hL₀, hc₂, hbound⟩ := locBd_convPow (regV_pos hvlo)
    (regV_le_regB hv) (one_le_regBeta D θ vlo)
  set c := c₂ / D ^ 2 with hc_def
  have hc : 0 < c := div_pos hc₂ (sq_pos_of_pos hD)
  refine ⟨L₀ + D * (Real.exp (2 * c) / c), by positivity, ?_⟩
  intro ν hν n hn
  have hloc := hbound ν D hD (hν.momClass hθ hvlo) (hν.envBd.locBd hD.le hθ.le) n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hcoeff : L₀ / Real.sqrt n + D * Real.exp (-c₂ * ((n : ℝ) - 2) / D ^ 2) ≤
      (L₀ + D * (Real.exp (2 * c) / c)) / Real.sqrt n := by
    have he := kr_exp_decay_le_sqrt hc hn1
    have heq : -c₂ * ((n : ℝ) - 2) / D ^ 2 = -c * ((n : ℝ) - 2) := by rw [hc_def]; ring
    rw [heq]
    calc
      _ ≤ L₀ / Real.sqrt n + D * (Real.exp (2 * c) / c / Real.sqrt n) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left he hD.le)
      _ = _ := by ring
  intro A hA
  exact (hloc A hA).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoeff) le_rfl)

/-! ## The free-density bound for the killed density -/

/-- The killed `(n+1)`-step density is bounded by the free `n`-step sum density bound
divided by `|a|`. -/
theorem krDens_le_of_locBd {L : ℝ} (hL : 0 ≤ L) (hJ : MeasurableSet J)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    {n : ℕ} (hloc : LocBd L (convPow (ν : Measure ℝ) n)) (y₀ z : ℝ) :
    krDens J ν f β a (n + 1) y₀ z ≤ L / |a| := by
  have hD0 : 0 ≤ D := (hf0 0).trans (hfD 0)
  have ha0 : 0 < |a| := abs_pos.2 ha
  set c : ℝ := y₀ + n * β + β - z with hc
  set h : ℝ → ℝ := fun s => f (c / a - s) / |a| with hh
  have hhm : Measurable h := (hf.comp (measurable_const.sub measurable_id)).div_const _
  have hh0 : ∀ s, 0 ≤ h s := fun s => div_nonneg (hf0 _) (abs_nonneg _)
  have hhint : Integrable h :=
    ((kr_integrable_density ν hf hf0 hν).comp_sub_left (c / a)).div_const _
  have hhD : ∀ s, |h s| ≤ D / |a| := fun s => by
    rw [abs_of_nonneg (hh0 s)]
    exact div_le_div_of_nonneg_right (hfD _) (abs_nonneg _)
  -- pointwise domination of the integrand
  have hpt : ∀ g : ℕ → ℝ, krAlive J β a n y₀ g * krKer J f β a (kWalk y₀ β a g n) z ≤
      h (gapKeys g n) := by
    intro g
    have hker : krKer J f β a (kWalk y₀ β a g n) z ≤ h (gapKeys g n) := by
      unfold krKer
      simp only [hh, kWalk]
      rw [show y₀ + n * β - a * gapKeys g n + β - z = c - a * gapKeys g n by rw [hc]; ring,
        sub_div, mul_div_cancel_left₀ _ ha]
      calc J.indicator (fun _ => (1 : ℝ)) (y₀ + n * β - a * gapKeys g n) *
            J.indicator (fun _ => (1 : ℝ)) z * (f (c / a - gapKeys g n) / |a|)
          ≤ 1 * 1 * (f (c / a - gapKeys g n) / |a|) := by
            refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (hf0 _) (abs_nonneg _))
            exact mul_le_mul (kr_indicator_one_le_one _) (kr_indicator_one_le_one _)
              (kr_indicator_one_nonneg _) zero_le_one
        _ = _ := by ring
    calc krAlive J β a n y₀ g * krKer J f β a (kWalk y₀ β a g n) z
        ≤ 1 * h (gapKeys g n) :=
          mul_le_mul (krAlive_le_one _ _ _) hker (krKer_nonneg hf0 _ _) zero_le_one
      _ = h (gapKeys g n) := one_mul _
  have hgk : Measurable (fun g : ℕ → ℝ => gapKeys g n) :=
    (measurable_pi_apply n).comp measurable_gapKeys
  rw [krDens_succ]
  calc ∫ g, krAlive J β a n y₀ g * krKer J f β a (kWalk y₀ β a g n) z ∂(iidLaw ν)
      ≤ ∫ g, h (gapKeys g n) ∂(iidLaw ν) := by
        refine integral_mono (kr_integrable_of_bdd ?_ (M := D / |a|) ?_)
          (kr_integrable_of_bdd (hhm.comp hgk) fun g => hhD _) hpt
        · exact (measurable_krAlive_right hJ β a n y₀).mul ((measurable_krKer_prod hJ hf β a).comp
            (((measurable_kWalk_prod β a n).comp (measurable_const.prodMk measurable_id)).prodMk
              measurable_const))
        · intro g
          rw [abs_mul, abs_of_nonneg (krAlive_nonneg _ _ _)]
          calc _ ≤ 1 * (D / |a|) := mul_le_mul (krAlive_le_one _ _ _) (abs_krKer_le hf0 hfD _ _)
                (abs_nonneg _) zero_le_one
            _ = D / |a| := one_mul _
    _ = ∫ s, h s ∂(convPow (ν : Measure ℝ) n) := by
        rw [← map_gapKeys_eq_convPow ν n, integral_map hgk.aemeasurable hhm.aestronglyMeasurable]
    _ ≤ L * ∫ s, h s := kr_integral_le_of_locBd hL hloc hhm hh0 hhint
    _ = L / |a| := by
        simp only [hh]
        rw [integral_div, integral_sub_left_eq_self (fun s => f s) volume (c / a),
          kr_integral_density_eq_one ν hf hf0 hν]
        ring

/-- **Class-uniform free-density bound**: `krDens (n+1) y₀ z ≤ L / (√n |a|)` for `n ≥ 2`. -/
theorem krDens_le_free (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hv : vlo ≤ vhi) :
    ∃ L : ℝ, 0 < L ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
      (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ J : Set ℝ, MeasurableSet J → ∀ β a : ℝ, a ≠ 0 → ∀ n : ℕ, 2 ≤ n → ∀ y₀ z : ℝ,
        krDens J ν f β a (n + 1) y₀ z ≤ L / (Real.sqrt n * |a|) := by
  obtain ⟨L, hL, hloc⟩ := kr_free_sum_density D θ vlo vhi hD hθ hvlo hv
  refine ⟨L, hL, ?_⟩
  intro ν hν f hf hf0 hfD hνf J hJ β a ha n hn y₀ z
  have h := krDens_le_of_locBd ν (β := β) (L := L / Real.sqrt n) (by positivity) hJ hf hf0 hfD hνf ha
    (hloc ν hν n hn) y₀ z
  rwa [div_div] at h

/-! ## Survival × free-density products -/

/-- A bounded measurable function supported in a set of finite measure is integrable. -/
theorem kr_integrable_of_bdd_support {u : ℝ → ℝ} (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hu : Measurable u) (hsupp : ∀ y, y ∉ J → u y = 0) {M : ℝ} (hM : ∀ y, |u y| ≤ M) :
    Integrable u := by
  have hdom : Integrable (fun y => J.indicator (fun _ => M) y) := by
    rw [integrable_indicator_iff hJ]
    exact integrableOn_const hJfin
  refine hdom.mono' hu.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  by_cases hy : y ∈ J
  · rw [indicator_of_mem hy]; exact hM y
  · rw [indicator_of_notMem hy, hsupp y hy]; simp

theorem kr_integrable_krDens_right (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D) (n : ℕ) (y₀ : ℝ) :
    Integrable (fun z => krDens J ν f β a n y₀ z) :=
  kr_integrable_of_bdd_support hJ hJfin (measurable_krDens_right ν hJ hf β a n y₀)
    (fun _ hz => krDens_eq_zero_of_right_notMem ν hz n y₀) (abs_krDens_le ν hf0 hfD n y₀)

theorem kr_integrable_krDens_left (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D) (n : ℕ) (z : ℝ) :
    Integrable (fun y => krDens J ν f β a n y z) :=
  kr_integrable_of_bdd_support hJ hJfin (measurable_krDens_left ν hJ hf β a n z)
    (fun _ hy => krDens_eq_zero_of_left_notMem ν hy n z) (fun y => abs_krDens_le ν hf0 hfD n y z)

/-- `q_{m+1+(n+1)}(y₀, z) ≤ s_{m+1}(y₀) · B` when `q_{n+1}(·, z) ≤ B` pointwise. -/
theorem krDens_add_le_krSurv_mul (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (m n : ℕ) (y₀ z : ℝ) {B : ℝ} (hB : ∀ y, krDens J ν f β a (n + 1) y z ≤ B) :
    krDens J ν f β a (m + 1 + (n + 1)) y₀ z ≤ krSurv J (ν : Measure ℝ) β a (m + 1) y₀ * B := by
  rw [krDens_add ν hJ hJfin hf hf0 hfD hν ha m n y₀ z, ← integral_krDens ν hJ hJfin hf hf0 hfD hν ha,
    ← integral_mul_const]
  refine integral_mono ?_ ((kr_integrable_krDens_right ν hJ hJfin hf hf0 hfD (m + 1) y₀).mul_const _)
    fun y => mul_le_mul_of_nonneg_left (hB y) (krDens_nonneg ν hf0 _ _ _)
  refine (kr_integrable_krDens_right ν hJ hJfin hf hf0 hfD (m + 1) y₀).mul_bdd
    (c := D / |a|) (measurable_krDens_left ν hJ hf β a (n + 1) z).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_krDens_le ν hf0 hfD _ _ _

/-- `q_{n+1+(m+1)}(y₀, z) ≤ B · s̃_{m+1}(z)` when `q_{n+1}(y₀, ·) ≤ B` pointwise
(reverse survival from the target). -/
theorem krDens_add_le_mul_krSurv_rev (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (m n : ℕ) (y₀ z : ℝ) {B : ℝ} (hB : ∀ y, krDens J ν f β a (n + 1) y₀ y ≤ B) :
    krDens J ν f β a (n + 1 + (m + 1)) y₀ z ≤
      B * krSurv J (ν : Measure ℝ) (-β) (-a) (m + 1) z := by
  rw [krDens_add ν hJ hJfin hf hf0 hfD hν ha n m y₀ z,
    ← integral_krDens_left ν hJ hJfin hf hf0 hfD hν ha, ← integral_const_mul]
  refine integral_mono ?_ ((kr_integrable_krDens_left ν hJ hJfin hf hf0 hfD (m + 1) z).const_mul _)
    fun y => mul_le_mul_of_nonneg_right (hB y) (krDens_nonneg ν hf0 _ _ _)
  refine (kr_integrable_krDens_left ν hJ hJfin hf hf0 hfD (m + 1) z).bdd_mul
    (c := D / |a|) (measurable_krDens_right ν hJ hf β a (n + 1) y₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_krDens_le ν hf0 hfD _ _ _

/-- **Three-block pin bound**: `q_{m+1+(j+1)+(k+1)}(y₀, z) ≤ s_{m+1}(y₀) · B · s̃_{k+1}(z)` when
`q_{j+1} ≤ B` pointwise. -/
theorem krDens_three_block_le (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (m j k : ℕ) {B : ℝ} (hB : ∀ y z, krDens J ν f β a (j + 1) y z ≤ B) (y₀ z : ℝ) :
    krDens J ν f β a (m + 1 + (j + 1) + (k + 1)) y₀ z ≤
      krSurv J (ν : Measure ℝ) β a (m + 1) y₀ *
        (B * krSurv J (ν : Measure ℝ) (-β) (-a) (k + 1) z) := by
  have e : m + 1 + (j + 1) + (k + 1) = m + 1 + (j + 1 + k + 1) := by omega
  rw [e]
  refine krDens_add_le_krSurv_mul ν hJ hJfin hf hf0 hfD hν ha m (j + 1 + k) y₀ z fun y => ?_
  have h := krDens_add_le_mul_krSurv_rev ν hJ hJfin hf hf0 hfD hν ha k j y z (hB y)
  rwa [show j + 1 + (k + 1) = j + 1 + k + 1 by omega] at h

end

end PGM
