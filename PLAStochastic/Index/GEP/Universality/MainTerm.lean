import PLAStochastic.Index.GEP.Universality.EndpointShift
import PLAStochastic.Index.GEP.Universality.PerIntegerSandwich

/-!
# WP5, D4: the main term `d_γ(Law(v T/ε²), 𝒯)`

Blueprint `kmt-blueprint/main.tex`, proof of Theorem 8.7, "the main term", in an abstract form.
The range `r > 0` is split at `r₁ = k₁ v/ε²` and `r₂ = (n+1) v/ε²`:

* `(0, r₁)`: `|ΔF| ≤ 1`, contributing `r₁ e^{γ r₁}`;
* `[r₁, r₂)`: the per-integer sandwich at `k = ⌊r ε²/v⌋` gives
  `|ΔF(r)| ≤ 𝒯(band r) + p_fail`, and the band integral is the Tonelli bound of
  `GEPSAWeighted`;
* `[r₂, ∞)`: both tails, from `tail_rawV` and the exponential moment of `𝒯`.

All constants are explicit; the only structural inputs are an (SA) coupling at horizon `n`, the
Bernstein bounds on the input walk (as hypotheses), and `LifetimeSide`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

/-! ## Distribution functions -/

theorem one_sub_cdf_eq_real_Ioi (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℝ) :
    1 - cdf μ r = μ.real (Ioi r) := by
  rw [cdf_eq_real, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

theorem measurableSet_lt_toNat (eps : ℝ) (k : ℕ) :
    MeasurableSet {g : ℕ → ℝ | k < (gapSegLen eps g).toNat} :=
  measurableSet_lt measurable_const
    (measurable_from_top.comp (isStoppingRule_gapSegLen eps).measurable)

/-- `P(k < T.toNat) = P(k < T)` when `T` is a.s. finite. -/
theorem real_lt_toNat_eq (P : Measure (ℕ → ℝ)) {eps : ℝ}
    (hfin : ∀ᵐ g ∂P, gapSegLen eps g ≠ ⊤) (k : ℕ) :
    P.real {g | k < (gapSegLen eps g).toNat} = P.real {g | (k : ℕ∞) < gapSegLen eps g} := by
  rw [measureReal_def, measureReal_def]
  congr 1
  refine measure_congr ?_
  filter_upwards [hfin] with g hg
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.1 hg
  apply propext
  change k < (gapSegLen eps g).toNat ↔ (k : ℕ∞) < gapSegLen eps g
  rw [← ht, ENat.toNat_natCast]
  exact_mod_cast Iff.rfl

/-- `1 - F_V(r) = P(⌊r ε²/v⌋ < T)`. -/
theorem one_sub_cdf_rawV (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo) {eps : ℝ}
    (heps : epsZero vhi (univBeta vlo κ₃) ≤ eps) {r : ℝ} (hr : 0 ≤ r) :
    1 - cdf ((iidLaw ν).map (rawV eps ν)) r =
      (iidLaw ν).real {g | ((⌊r * eps ^ 2 / lawVar ν⌋₊ : ℕ) : ℕ∞) < gapSegLen eps g} := by
  have hv0 : 0 < lawVar ν := hvlo.trans_le h.var_ge
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hE : 0 < eps ^ 2 := by positivity
  have hfin := (h.oneLayer hvlo heps).1
  have : IsProbabilityMeasure ((iidLaw ν).map (rawV eps ν)) :=
    Measure.isProbabilityMeasure_map (measurable_rawV eps ν).aemeasurable
  rw [one_sub_cdf_eq_real_Ioi, measureReal_def, Measure.map_apply (measurable_rawV eps ν) measurableSet_Ioi,
    ← measureReal_def, ← real_lt_toNat_eq _ hfin]
  congr 1
  ext g
  simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_ofPred_eq, rawV]
  rw [Nat.floor_lt (by positivity), div_lt_iff₀ hv0, lt_div_iff₀ hE]
  constructor <;> intro hh <;> linarith

/-! ## The band -/

/-- The band `{t | α r - β₀ ≤ t ≤ α' r}` written through the pushforward `t ↦ (t/α', (t+β₀)/α)`. -/
theorem measure_band_eq (𝒯 : Measure ℝ) {α α' β₀ : ℝ} (hα : 0 < α) (hα' : 0 < α') (r : ℝ) :
    𝒯 {t | α * r - β₀ ≤ t ∧ t ≤ α' * r} =
      (𝒯.map fun t => (t / α', (t + β₀) / α)) {p | p.1 ≤ r ∧ r ≤ p.2} := by
  have hm : Measurable fun t : ℝ => (t / α', (t + β₀) / α) :=
    (measurable_id.div_const _).prodMk ((measurable_id.add_const _).div_const _)
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 ≤ r ∧ r ≤ p.2} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_const measurable_snd)
  rw [Measure.map_apply hm hs]
  congr 1
  ext t
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [div_le_iff₀ hα', le_div_iff₀ hα]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The Tonelli bound of the band integral against a lifetime law with exponential moment. -/
theorem lintegral_band_le {𝒯 : Measure ℝ} {θτ Eτ : ℝ} (hL : LifetimeSide 𝒯 θτ Eτ)
    {γ eps χ v vhi : ℝ} (hγ : 0 < γ) (hγτ : 4 * γ ≤ θτ) (heps : 0 < eps) (hχ0 : 0 ≤ χ)
    (hχ : χ ≤ eps / 4) (hv : 0 < v) (hvhi : v ≤ vhi) (hveps : v ≤ eps ^ 2) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (γ * r)) *
        𝒯 {t | eps ^ 2 / (eps + χ) ^ 2 * r - v / (eps + χ) ^ 2 ≤ t ∧
          t ≤ eps ^ 2 / (eps - 2 * χ) ^ 2 * r} ≤
      ENNReal.ofReal (Real.exp γ * Eτ * (12 * χ / (θτ * eps) + vhi / eps ^ 2)) := by
  have := hL.prob
  have hθτ := hL.θpos
  have hεχ : 0 < eps + χ := by linarith
  have hεχ' : 0 < eps - 2 * χ := by linarith
  set α := eps ^ 2 / (eps + χ) ^ 2 with hα
  set α' := eps ^ 2 / (eps - 2 * χ) ^ 2 with hα'
  set β₀ := v / (eps + χ) ^ 2 with hβ₀
  have hα0 : 0 < α := by positivity
  have hα'0 : 0 < α' := by positivity
  have hm : Measurable fun t : ℝ => (t / α', (t + β₀) / α) :=
    (measurable_id.div_const _).prodMk ((measurable_id.add_const _).div_const _)
  simp_rw [measure_band_eq 𝒯 hα0 hα'0]
  have : SFinite (𝒯.map fun t : ℝ => (t / α', (t + β₀) / α)) := inferInstance
  refine (lintegral_exp_mul_measure_Icc_le hγ.le).trans ?_
  rw [lintegral_map (by fun_prop) hm]
  -- pointwise bound on `t ≥ 0`
  have hae : ∀ᵐ t ∂𝒯, 0 ≤ t := by
    have h0 := hL.nonneg
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with t ht
    simpa using ht
  have hpt : ∀ t : ℝ, 0 ≤ t →
      ENNReal.ofReal (max ((t + β₀) / α - t / α') 0 * Real.exp (γ * ((t + β₀) / α))) ≤
        ENNReal.ofReal (Real.exp γ * (12 * χ / (θτ * eps) + vhi / eps ^ 2) * Real.exp (θτ * t)) := by
    intro t ht
    refine ENNReal.ofReal_le_ofReal ?_
    have hinv : 1 / α - 1 / α' ≤ 6 * χ / eps := by
      rw [hα, hα', one_div_div, one_div_div]
      rw [show (eps + χ) ^ 2 / eps ^ 2 - (eps - 2 * χ) ^ 2 / eps ^ 2 =
        (6 * eps * χ - 3 * χ ^ 2) / eps ^ 2 by ring]
      rw [div_le_div_iff₀ (by positivity) heps]
      nlinarith
    have hβα : β₀ / α = v / eps ^ 2 := by rw [hβ₀, hα]; field_simp
    have hlen : (t + β₀) / α - t / α' ≤ 6 * χ / eps * t + vhi / eps ^ 2 := by
      have e : (t + β₀) / α - t / α' = t * (1 / α - 1 / α') + β₀ / α := by ring
      rw [e, hβα]
      have h1 : t * (1 / α - 1 / α') ≤ t * (6 * χ / eps) := mul_le_mul_of_nonneg_left hinv ht
      have h2 : v / eps ^ 2 ≤ vhi / eps ^ 2 := by gcongr
      linarith
    have hlen0 : 0 ≤ (t + β₀) / α - t / α' := by
      have e : (t + β₀) / α - t / α' = t * (1 / α - 1 / α') + β₀ / α := by ring
      rw [e]
      have : 0 ≤ 1 / α - 1 / α' := by
        rw [hα, hα', one_div_div, one_div_div, sub_nonneg]
        gcongr
        linarith
      positivity
    rw [max_eq_left hlen0]
    have hexp : Real.exp (γ * ((t + β₀) / α)) ≤ Real.exp γ * Real.exp (2 * γ * t) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h1 : 1 / α ≤ 2 := by
        rw [hα, one_div_div, div_le_iff₀ (by positivity)]
        nlinarith
      have h2 : β₀ / α ≤ 1 := by rw [hβα, div_le_one (by positivity)]; exact hveps
      have e : γ * ((t + β₀) / α) = γ * (t * (1 / α)) + γ * (β₀ / α) := by ring
      rw [e]
      have : γ * (t * (1 / α)) ≤ γ * (t * 2) := by gcongr
      have : γ * (β₀ / α) ≤ γ * 1 := by gcongr
      linarith
    -- `t e^{2γt} ≤ (2/θτ) e^{θτ t}` and `e^{2γ t} ≤ e^{θτ t}`
    have hte : t * Real.exp (2 * γ * t) ≤ 2 / θτ * Real.exp (θτ * t) := by
      have h1 : θτ / 2 * t + 1 ≤ Real.exp (θτ / 2 * t) := Real.add_one_le_exp _
      have h2 : t ≤ 2 / θτ * Real.exp (θτ / 2 * t) := by
        have : θτ / 2 * t ≤ Real.exp (θτ / 2 * t) := by linarith
        calc t = 2 / θτ * (θτ / 2 * t) := by field_simp
          _ ≤ 2 / θτ * Real.exp (θτ / 2 * t) := by gcongr
      have h3 : Real.exp (2 * γ * t) ≤ Real.exp (θτ / 2 * t) :=
        Real.exp_le_exp.2 (by nlinarith)
      calc t * Real.exp (2 * γ * t) ≤ 2 / θτ * Real.exp (θτ / 2 * t) * Real.exp (θτ / 2 * t) :=
            mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
        _ = 2 / θτ * Real.exp (θτ * t) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    have hee : Real.exp (2 * γ * t) ≤ Real.exp (θτ * t) := Real.exp_le_exp.2 (by nlinarith)
    have hvhi0 : 0 ≤ vhi := hv.le.trans hvhi
    calc ((t + β₀) / α - t / α') * Real.exp (γ * ((t + β₀) / α))
        ≤ (6 * χ / eps * t + vhi / eps ^ 2) * (Real.exp γ * Real.exp (2 * γ * t)) :=
          mul_le_mul hlen hexp (Real.exp_pos _).le
            (add_nonneg (by positivity) (div_nonneg hvhi0 (by positivity)))
      _ = Real.exp γ * (6 * χ / eps * (t * Real.exp (2 * γ * t)) +
            vhi / eps ^ 2 * Real.exp (2 * γ * t)) := by ring
      _ ≤ Real.exp γ * (6 * χ / eps * (2 / θτ * Real.exp (θτ * t)) +
            vhi / eps ^ 2 * Real.exp (θτ * t)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact add_le_add (mul_le_mul_of_nonneg_left hte (by positivity))
            (mul_le_mul_of_nonneg_left hee (div_nonneg hvhi0 (by positivity)))
      _ = Real.exp γ * (12 * χ / (θτ * eps) + vhi / eps ^ 2) * Real.exp (θτ * t) := by
          field_simp
          ring
  have hK0 : 0 ≤ Real.exp γ * (12 * χ / (θτ * eps) + vhi / eps ^ 2) := by
    have hvhi0 : 0 ≤ vhi := hv.le.trans hvhi
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg (by positivity) (div_nonneg hvhi0 (by positivity)))
  calc ∫⁻ t, ENNReal.ofReal (max ((t + β₀) / α - t / α') 0 * Real.exp (γ * ((t + β₀) / α))) ∂𝒯
      ≤ ∫⁻ t, ENNReal.ofReal (Real.exp γ * (12 * χ / (θτ * eps) + vhi / eps ^ 2)) *
          ENNReal.ofReal (Real.exp (θτ * t)) ∂𝒯 := by
        refine lintegral_mono_ae (hae.mono fun t ht => ?_)
        rw [← ENNReal.ofReal_mul hK0]
        exact hpt t ht
    _ = ENNReal.ofReal (Real.exp γ * (12 * χ / (θτ * eps) + vhi / eps ^ 2)) *
          ∫⁻ t, ENNReal.ofReal (Real.exp (θτ * t)) ∂𝒯 := lintegral_const_mul _ (by fun_prop)
    _ ≤ ENNReal.ofReal (Real.exp γ * (12 * χ / (θτ * eps) + vhi / eps ^ 2)) * ENNReal.ofReal Eτ := by
        gcongr
        exact hL.expMom
    _ = ENNReal.ofReal (Real.exp γ * Eτ * (12 * χ / (θτ * eps) + vhi / eps ^ 2)) := by
        rw [← ENNReal.ofReal_mul hK0]
        congr 1; ring

/-! ## The tail of `𝒯` -/

theorem LifetimeSide.tail_le {𝒯 : Measure ℝ} {θτ Eτ : ℝ} (hL : LifetimeSide 𝒯 θτ Eτ) (r : ℝ) :
    𝒯.real {t | r ≤ t} ≤ Eτ * Real.exp (-(θτ * r)) := by
  have := hL.prob
  have hθτ := hL.θpos
  have hmeas : MeasurableSet {t : ℝ | r ≤ t} := measurableSet_le measurable_const measurable_id
  have h1 : ENNReal.ofReal (Real.exp (θτ * r)) * 𝒯 {t | r ≤ t} ≤
      ∫⁻ t, ENNReal.ofReal (Real.exp (θτ * t)) ∂𝒯 := by
    rw [← lintegral_indicator_const hmeas]
    refine lintegral_mono fun t => ?_
    by_cases ht : t ∈ {t : ℝ | r ≤ t}
    · rw [Set.indicator_of_mem ht]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith [show r ≤ t from ht]))
    · rw [Set.indicator_of_notMem ht]; exact zero_le
  have h2 := h1.trans hL.expMom
  rw [← ofReal_measureReal, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_le_ofReal_iff'] at h2
  rcases h2 with h2 | h2
  · have : 𝒯.real {t | r ≤ t} ≤ Eτ / Real.exp (θτ * r) := by
      rw [le_div_iff₀ (Real.exp_pos _)]; linarith
    rw [Real.exp_neg]
    calc 𝒯.real {t | r ≤ t} ≤ Eτ / Real.exp (θτ * r) := this
      _ = Eτ * (Real.exp (θτ * r))⁻¹ := div_eq_mul_inv _ _
  · have hE0 : 0 ≤ Eτ := by
      have := hL.expMom
      have hpos : 0 < ∫⁻ t, ENNReal.ofReal (Real.exp (θτ * t)) ∂𝒯 := by
        rw [lintegral_pos_iff_support (by fun_prop)]
        have : Function.support (fun t : ℝ => ENNReal.ofReal (Real.exp (θτ * t))) = univ := by
          ext t; simp [Real.exp_pos]
        rw [this, measure_univ]; exact one_pos
      by_contra hneg
      rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.1 hneg))] at this
      exact absurd (this.trans_lt' hpos) (lt_irrefl _)
    have : 𝒯.real {t | r ≤ t} ≤ 0 := by
      have := mul_nonpos_iff.1 h2
      rcases this with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h (not_le.2 (Real.exp_pos _))
    exact this.trans (by positivity)

/-! ## The middle range: per-`r` sandwich -/

/-- The band of the middle range at `r`. -/
def bandSet (eps χ v r : ℝ) : Set ℝ :=
  {t | eps ^ 2 / (eps + χ) ^ 2 * r - v / (eps + χ) ^ 2 ≤ t ∧ t ≤ eps ^ 2 / (eps - 2 * χ) ^ 2 * r}

/-- The Bernstein input of the middle range: at every `k ∈ [k₁, n]` a deviation level `xB ≤ k/9`
with `8 xB²/k ≤ xD` and failure probability `≤ p₂`. -/
def BernsteinInput (ν : ProbabilityMeasure ℝ) (k₁ n : ℕ) (xD p₂ : ℝ) : Prop :=
  ∀ k : ℕ, k₁ ≤ k → k ≤ n → ∃ xB : ℝ, 0 ≤ xB ∧ xB ≤ (k : ℝ) / 9 ∧ 8 * xB ^ 2 / k ≤ xD ∧
    (iidLaw ν).real (walkBad xB k) ≤ p₂

/-- **Per-`r` sandwich on the middle range.** -/
theorem middle_pointwise_le (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo) {eps : ℝ}
    (heps : epsZero vhi (univBeta vlo κ₃) ≤ eps)
    {𝒯 : Measure ℝ} {θτ Eτ : ℝ} (hL : LifetimeSide 𝒯 θτ Eτ)
    {π : Measure ((ℕ → ℝ) × (ℕ → ℝ))} [IsProbabilityMeasure π]
    (h1 : π.map Prod.fst = iidLaw ν) (h2 : π.map Prod.snd = iidLaw gaussPM)
    {n k₁ : ℕ} (hk₁ : 1 ≤ k₁) {a pSA : ℝ} (ha : 0 ≤ a) (hSA : π.real (SAEvent (lawVar ν) a n) ≤ pSA)
    {xD p₂ : ℝ} (hxD : 0 ≤ xD) (hBern : BernsteinInput ν k₁ n xD p₂) {ρ : ℝ} (hρ : 0 < ρ)
    (hχ : 2 * (a + xD + 2 * Real.sqrt (lawVar ν) * ρ) < eps) {r : ℝ}
    (hr₁ : (k₁ : ℝ) * lawVar ν / eps ^ 2 ≤ r) (hr₂ : r < ((n : ℝ) + 1) * lawVar ν / eps ^ 2) :
    |cdf ((iidLaw ν).map (rawV eps ν)) r - cdf 𝒯 r| ≤
      𝒯.real (bandSet eps (a + xD + 2 * Real.sqrt (lawVar ν) * ρ) (lawVar ν) r) +
        (pSA + p₂ + p₂ + 2 * n * Real.exp (-ρ ^ 2 / 2)) := by
  have := hL.prob
  have hv0 : 0 < lawVar ν := hvlo.trans_le h.var_ge
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hepspos : 0 < eps := by linarith
  have hE : 0 < eps ^ 2 := by positivity
  set v := lawVar ν with hv
  set χ := a + xD + 2 * Real.sqrt v * ρ with hχdef
  have hχ0 : 0 ≤ χ := by positivity
  have hr0 : 0 ≤ r := le_trans (by positivity) hr₁
  set k := ⌊r * eps ^ 2 / v⌋₊ with hk
  have hkk₁ : k₁ ≤ k := by
    rw [hk]
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hv0]
    rw [div_le_iff₀ hE] at hr₁
    linarith
  have hkn : k ≤ n := by
    have hlt : r * eps ^ 2 / v < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_lt_iff₀ hv0]
      rw [lt_div_iff₀ hE] at hr₂
      linarith
    exact Nat.lt_succ_iff.1 ((Nat.floor_lt (by positivity)).2 hlt)
  have hk1 : 1 ≤ k := hk₁.trans hkk₁
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  obtain ⟨xB, hxB0, hxB9, hxBD, hB₂⟩ := hBern k hkk₁ hkn
  have hB₁ : (iidLaw ν).real (walkBad ((k : ℝ) / 9) k) ≤ p₂ := by
    refine (measureReal_mono ?_).trans hB₂
    rintro g ⟨t, ht, hlt⟩
    exact ⟨t, ht, lt_of_le_of_lt hxB9 hlt⟩
  have hχk : a + 8 * xB ^ 2 / k + 2 * Real.sqrt v * ρ ≤ χ := by
    rw [hχdef]
    linarith [hxBD]
  have hχk0 : 0 ≤ a + 8 * xB ^ 2 / k + 2 * Real.sqrt v * ρ := by positivity
  -- the two sandwich bounds, with the band monotonicity
  have hup := perInteger_upper (ν := ν) (π := π) (eps := eps) hk1 hkn hv0 ha hxB0 hepspos h1 h2
    hSA hB₁ hB₂ hL hρ
  have hχ' : 2 * (a + 8 * xB ^ 2 / k + 2 * Real.sqrt v * ρ) < eps := by
    rw [hχdef] at hχ; linarith
  have hlo := perInteger_lower (ν := ν) (π := π) (eps := eps) hk1 hkn hv0 ha hxB0 h1 h2 hSA hB₁
    hB₂ hL hρ hχ'
  -- `F_V(r) = 1 - P(T > k)`, `F_𝒯(r) = 1 - 𝒯(r, ∞)`
  have hFV := one_sub_cdf_rawV h hvlo heps hr0
  rw [← hk] at hFV
  have hFT := one_sub_cdf_eq_real_Ioi 𝒯 r
  set A := (iidLaw ν).real {g | (k : ℕ∞) < gapSegLen eps g} with hA
  set Bt := 𝒯.real (Ioi r) with hBt
  have hdiff : cdf ((iidLaw ν).map (rawV eps ν)) r - cdf 𝒯 r = Bt - A := by linarith
  rw [hdiff]
  -- band inclusions
  set α := eps ^ 2 / (eps + χ) ^ 2 with hα
  set α' := eps ^ 2 / (eps - 2 * χ) ^ 2 with hα'
  set β₀ := v / (eps + χ) ^ 2 with hβ₀
  have hεχ : 0 < eps + χ := by linarith
  have hεχ' : 0 < eps - 2 * χ := by linarith
  have hkr : (k : ℝ) ≤ r * eps ^ 2 / v := Nat.floor_le (by positivity)
  have hkr' : r * eps ^ 2 - v < v * k := by
    have := Nat.lt_floor_add_one (r * eps ^ 2 / v)
    rw [← hk, div_lt_iff₀ hv0] at this
    linarith
  have hkr'' : v * k ≤ r * eps ^ 2 := by
    rw [le_div_iff₀ hv0] at hkr; linarith
  have hα1 : α ≤ 1 := by
    rw [hα]
    exact div_le_one_of_le₀ (pow_le_pow_left₀ hepspos.le (by linarith) 2) (by positivity)
  have hα'1 : 1 ≤ α' := by
    rw [hα']
    exact (one_le_div (by positivity)).2 (pow_le_pow_left₀ hεχ'.le (by linarith) 2)
  have hβ0 : 0 ≤ β₀ := by positivity
  -- upper: `A ≤ 𝒯[a₊, ∞) + p_fail`, `𝒯[a₊,∞) - Bt ≤ 𝒯(band)`
  have hIup : 𝒯.real (Ici (v * k / (eps + χ) ^ 2)) - Bt ≤ 𝒯.real (bandSet eps χ v r) := by
    have hsub : Ici (v * k / (eps + χ) ^ 2) ⊆ bandSet eps χ v r ∪ Ioi r := by
      intro t ht
      by_cases htr : r < t
      · exact Or.inr htr
      · left
        refine ⟨?_, ?_⟩
        · -- `α r - β₀ ≤ v k/(ε+χ)² ≤ t`
          have : α * r - β₀ ≤ v * k / (eps + χ) ^ 2 := by
            rw [hα, hβ₀]
            have e : eps ^ 2 / (eps + χ) ^ 2 * r - v / (eps + χ) ^ 2 =
                (r * eps ^ 2 - v) / (eps + χ) ^ 2 := by ring
            rw [e]
            exact div_le_div_of_nonneg_right hkr'.le (by positivity)
          exact this.trans ht
        · have : t ≤ r := not_lt.1 htr
          have : r ≤ α' * r := le_mul_of_one_le_left hr0 hα'1
          linarith
    have := measureReal_mono hsub (μ := 𝒯)
    have := this.trans (measureReal_union_le _ _)
    linarith
  -- lower: `Bt - A ≤ 𝒯(r, a₋) + p_fail`, `𝒯(r,a₋) ≤ 𝒯(band)`
  have hIlo : Bt - 𝒯.real (Ici (v * k / (eps - 2 * χ) ^ 2)) ≤ 𝒯.real (bandSet eps χ v r) := by
    have hsub : Ioi r ⊆ bandSet eps χ v r ∪ Ici (v * k / (eps - 2 * χ) ^ 2) := by
      intro t ht
      by_cases hta : v * k / (eps - 2 * χ) ^ 2 ≤ t
      · exact Or.inr hta
      · left
        have hta' : t < v * k / (eps - 2 * χ) ^ 2 := not_le.1 hta
        refine ⟨?_, ?_⟩
        · have : (r : ℝ) < t := ht
          have : α * r ≤ r := mul_le_of_le_one_left hr0 hα1
          linarith
        · have : v * k / (eps - 2 * χ) ^ 2 ≤ α' * r := by
            rw [hα']
            have e : eps ^ 2 / (eps - 2 * χ) ^ 2 * r = r * eps ^ 2 / (eps - 2 * χ) ^ 2 := by ring
            rw [e]
            exact div_le_div_of_nonneg_right hkr'' (by positivity)
          exact hta'.le.trans this
    have := measureReal_mono hsub (μ := 𝒯)
    have := this.trans (measureReal_union_le _ _)
    linarith
  -- monotonicity in `χ`
  have hmono_up : 𝒯.real (Ici (v * k / (eps + (a + 8 * xB ^ 2 / k + 2 * Real.sqrt v * ρ)) ^ 2)) ≤
      𝒯.real (Ici (v * k / (eps + χ) ^ 2)) := by
    refine measureReal_mono (Ici_subset_Ici.2 ?_)
    gcongr
  have hmono_lo : 𝒯.real (Ici (v * k / (eps - 2 * χ) ^ 2)) ≤
      𝒯.real (Ici (v * k / (eps - 2 * (a + 8 * xB ^ 2 / k + 2 * Real.sqrt v * ρ)) ^ 2)) := by
    refine measureReal_mono (Ici_subset_Ici.2 ?_)
    have h0 : 0 < eps - 2 * (a + 8 * xB ^ 2 / k + 2 * Real.sqrt v * ρ) := by linarith
    gcongr
  rw [abs_le]
  constructor <;> linarith [hup, hlo, hIup, hIlo, hmono_up, hmono_lo]

/-! ## The main term -/

/-- The three pieces of the main term. -/
def mainBound (γ eps v vhi θτ Eτ r' χ pfail : ℝ) (k₁ n : ℕ) : ℝ :=
  (k₁ : ℝ) * v / eps ^ 2 * Real.exp (γ * ((k₁ : ℝ) * v / eps ^ 2)) +
    (Real.exp γ * Eτ * (12 * χ / (θτ * eps) + vhi / eps ^ 2) +
      pfail * (((n : ℝ) + 1) * v / eps ^ 2) * Real.exp (γ * (((n : ℝ) + 1) * v / eps ^ 2))) +
    (2 * cTail / r' * Real.exp (-(r' * (((n : ℝ) + 1) * v / eps ^ 2) / 2)) +
      2 * Eτ / θτ * Real.exp (-(θτ * (((n : ℝ) + 1) * v / eps ^ 2) / 2)))

/-- **The main term** (blueprint Theorem 8.7, "the main term"). -/
theorem main_term_le (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo) {eps : ℝ}
    (heps : epsZero vhi (univBeta vlo κ₃) ≤ eps)
    {𝒯 : Measure ℝ} {θτ Eτ : ℝ} (hL : LifetimeSide 𝒯 θτ Eτ) {γ : ℝ} (hγ : 0 < γ)
    (hγτ : 4 * γ ≤ θτ) (hγr : 2 * γ ≤ rPrime vlo vhi)
    {π : Measure ((ℕ → ℝ) × (ℕ → ℝ))} [IsProbabilityMeasure π]
    (h1 : π.map Prod.fst = iidLaw ν) (h2 : π.map Prod.snd = iidLaw gaussPM)
    {n k₁ : ℕ} (hk₁ : 1 ≤ k₁) (hk₁n : k₁ ≤ n) {a pSA : ℝ} (ha : 0 ≤ a) (hpSA : 0 ≤ pSA)
    (hSA : π.real (SAEvent (lawVar ν) a n) ≤ pSA)
    {xD p₂ : ℝ} (hxD : 0 ≤ xD) (hp₂ : 0 ≤ p₂) (hBern : BernsteinInput ν k₁ n xD p₂) {ρ : ℝ}
    (hρ : 0 < ρ) (hχ : a + xD + 2 * Real.sqrt (lawVar ν) * ρ ≤ eps / 4) :
    dEtaL γ (lawPM (iidLaw ν) (measurable_rawV eps ν)) ⟨𝒯, hL.prob⟩ ≤
      ENNReal.ofReal (mainBound γ eps (lawVar ν) vhi θτ Eτ (rPrime vlo vhi)
        (a + xD + 2 * Real.sqrt (lawVar ν) * ρ)
        (pSA + p₂ + p₂ + 2 * n * Real.exp (-ρ ^ 2 / 2)) k₁ n) := by
  have hTprob := hL.prob
  have hθτ := hL.θpos
  have hv0 : 0 < lawVar ν := hvlo.trans_le h.var_ge
  have hvhi : 0 < vhi := hvlo.trans_le (h.var_ge.trans h.var_le)
  have hr' := rPrime_pos hvlo hvhi
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hepspos : 0 < eps := by linarith
  have hE : 0 < eps ^ 2 := by positivity
  set v := lawVar ν with hv
  set χ := a + xD + 2 * Real.sqrt v * ρ with hχdef
  have hχ0 : 0 ≤ χ := by positivity
  set pfail := pSA + p₂ + p₂ + 2 * n * Real.exp (-ρ ^ 2 / 2) with hpf
  have hpf0 : 0 ≤ pfail := by positivity
  set r₁ := (k₁ : ℝ) * v / eps ^ 2 with hr₁
  set r₂ := ((n : ℝ) + 1) * v / eps ^ 2 with hr₂
  have hr₁0 : 0 < r₁ := by
    have : (0 : ℝ) < k₁ := by exact_mod_cast hk₁
    positivity
  have hr₁₂ : r₁ ≤ r₂ := by
    rw [hr₁, hr₂]
    gcongr
    have : (k₁ : ℝ) ≤ n := by exact_mod_cast hk₁n
    linarith
  have hveps : v ≤ eps ^ 2 := by
    have := h.sq_ge hvlo heps
    linarith
  set P := iidLaw ν with hP
  set μV := P.map (rawV eps ν) with hμV
  have : IsProbabilityMeasure μV := Measure.isProbabilityMeasure_map (measurable_rawV eps ν).aemeasurable
  have hFmeas : Measurable fun r : ℝ => ENNReal.ofReal (Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r|) :=
    ((measurable_const.mul measurable_id).exp.mul
      ((monotone_cdf μV).measurable.sub (monotone_cdf 𝒯).measurable).abs).ennreal_ofReal
  -- split the range
  have hsplit : Ioi (0 : ℝ) ⊆ Ioo 0 r₁ ∪ Ico r₁ r₂ ∪ Ici r₂ := by
    intro r hr
    rcases lt_or_ge r r₁ with h1 | h1
    · exact Or.inl (Or.inl ⟨hr, h1⟩)
    · rcases lt_or_ge r r₂ with h2 | h2
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inr h2
  unfold dEtaL
  change ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r|) ≤ _
  refine (lintegral_mono_set hsplit).trans ?_
  refine (lintegral_union_le _ _ _).trans ?_
  refine (add_le_add (lintegral_union_le _ _ _) le_rfl).trans ?_
  -- piece (i)
  have hpi : ∫⁻ r in Ioo (0 : ℝ) r₁, ENNReal.ofReal (Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r|) ≤
      ENNReal.ofReal (r₁ * Real.exp (γ * r₁)) := by
    calc ∫⁻ r in Ioo (0 : ℝ) r₁, ENNReal.ofReal (Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r|)
        ≤ ∫⁻ _ in Ioo (0 : ℝ) r₁, ENNReal.ofReal (Real.exp (γ * r₁)) := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
            (ae_of_all _ fun r (hr : r ∈ Ioo (0 : ℝ) r₁) => ?_))
          refine ENNReal.ofReal_le_ofReal ?_
          have hc1 : |cdf μV r - cdf 𝒯 r| ≤ 1 := by
            rw [abs_le]
            have := cdf_nonneg μV r; have := cdf_le_one μV r
            have := cdf_nonneg 𝒯 r; have := cdf_le_one 𝒯 r
            constructor <;> linarith
          calc Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r| ≤ Real.exp (γ * r) * 1 :=
                mul_le_mul_of_nonneg_left hc1 (Real.exp_pos _).le
            _ ≤ Real.exp (γ * r₁) := by
                rw [mul_one]; exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hr.2.le hγ.le)
      _ = ENNReal.ofReal (Real.exp (γ * r₁)) * volume (Ioo (0 : ℝ) r₁) := setLIntegral_const _ _
      _ = ENNReal.ofReal (r₁ * Real.exp (γ * r₁)) := by
          rw [Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  -- piece (ii)
  have hpii : ∫⁻ r in Ico r₁ r₂, ENNReal.ofReal (Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r|) ≤
      ENNReal.ofReal (Real.exp γ * Eτ * (12 * χ / (θτ * eps) + vhi / eps ^ 2) +
        pfail * r₂ * Real.exp (γ * r₂)) := by
    have hpt : ∀ r ∈ Ico r₁ r₂, ENNReal.ofReal (Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r|) ≤
        ENNReal.ofReal (Real.exp (γ * r)) * 𝒯 (bandSet eps χ v r) +
          ENNReal.ofReal (pfail * Real.exp (γ * r₂)) := by
      intro r hr
      have hmid := middle_pointwise_le h hvlo heps hL h1 h2 hk₁ ha hSA hxD hBern hρ
        (by linarith) hr.1 hr.2
      rw [← ofReal_measureReal, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hrr₂ : Real.exp (γ * r) ≤ Real.exp (γ * r₂) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hr.2.le hγ.le)
      calc Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r|
          ≤ Real.exp (γ * r) * (𝒯.real (bandSet eps χ v r) + pfail) :=
            mul_le_mul_of_nonneg_left hmid (Real.exp_pos _).le
        _ = Real.exp (γ * r) * 𝒯.real (bandSet eps χ v r) + pfail * Real.exp (γ * r) := by ring
        _ ≤ Real.exp (γ * r) * 𝒯.real (bandSet eps χ v r) + pfail * Real.exp (γ * r₂) := by
            gcongr
    have hband := lintegral_band_le hL hγ hγτ hepspos hχ0 hχ hv0 h.var_le hveps
    calc ∫⁻ r in Ico r₁ r₂, ENNReal.ofReal (Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r|)
        ≤ ∫⁻ r in Ico r₁ r₂, (ENNReal.ofReal (Real.exp (γ * r)) * 𝒯 (bandSet eps χ v r) +
            ENNReal.ofReal (pfail * Real.exp (γ * r₂))) :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ico).2 (ae_of_all _ hpt))
      _ = (∫⁻ r in Ico r₁ r₂, ENNReal.ofReal (Real.exp (γ * r)) * 𝒯 (bandSet eps χ v r)) +
            ∫⁻ _ in Ico r₁ r₂, ENNReal.ofReal (pfail * Real.exp (γ * r₂)) :=
          lintegral_add_right _ measurable_const
      _ ≤ (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (γ * r)) * 𝒯 (bandSet eps χ v r)) +
            ENNReal.ofReal (pfail * Real.exp (γ * r₂)) * ENNReal.ofReal r₂ := by
          gcongr
          · exact fun r (hr : r ∈ Ico r₁ r₂) => show (0 : ℝ) < r from lt_of_lt_of_le hr₁0 hr.1
          · rw [setLIntegral_const, Real.volume_Ico]
            gcongr
            linarith
      _ ≤ ENNReal.ofReal (Real.exp γ * Eτ * (12 * χ / (θτ * eps) + vhi / eps ^ 2)) +
            ENNReal.ofReal (pfail * Real.exp (γ * r₂)) * ENNReal.ofReal r₂ := by
          gcongr
          exact hband
      _ = ENNReal.ofReal (Real.exp γ * Eτ * (12 * χ / (θτ * eps) + vhi / eps ^ 2) +
            pfail * r₂ * Real.exp (γ * r₂)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add ?_ (by positivity)]
          · congr 1; ring
          · have hvhi0 : 0 ≤ vhi := hvhi.le
            have hE0 : 0 ≤ Eτ := by
              by_contra hneg
              have := hL.expMom
              rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.1 hneg))] at this
              have hpos : 0 < ∫⁻ t, ENNReal.ofReal (Real.exp (θτ * t)) ∂𝒯 := by
                rw [lintegral_pos_iff_support (by fun_prop)]
                have e : Function.support (fun t : ℝ => ENNReal.ofReal (Real.exp (θτ * t))) = univ := by
                  ext t; simp [Real.exp_pos]
                rw [e, measure_univ]; exact one_pos
              exact absurd (this.trans_lt' hpos) (lt_irrefl _)
            exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hE0)
              (add_nonneg (by positivity) (div_nonneg hvhi0 (by positivity)))
  -- piece (iii)
  have hpiii : ∫⁻ r in Ici r₂, ENNReal.ofReal (Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r|) ≤
      ENNReal.ofReal (2 * cTail / rPrime vlo vhi * Real.exp (-(rPrime vlo vhi * r₂ / 2)) +
        2 * Eτ / θτ * Real.exp (-(θτ * r₂ / 2))) := by
    have hr₂0 : 0 ≤ r₂ := by positivity
    have hpt : ∀ r ∈ Ioi r₂, ENNReal.ofReal (Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r|) ≤
        ENNReal.ofReal (Real.exp (γ * r)) * P {g | r ≤ rawV eps ν g} +
          ENNReal.ofReal (Real.exp (γ * r)) * 𝒯 {t | r ≤ t} := by
      intro r hr
      rw [← ofReal_measureReal, ← ofReal_measureReal, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have hV := one_sub_cdf_eq_real_Ioi μV r
      have hT := one_sub_cdf_eq_real_Ioi 𝒯 r
      have hV' : μV.real (Ioi r) ≤ P.real {g | r ≤ rawV eps ν g} := by
        rw [hμV, measureReal_def, Measure.map_apply (measurable_rawV eps ν) measurableSet_Ioi,
          ← measureReal_def]
        exact measureReal_mono fun g hg => le_of_lt (show r < rawV eps ν g from hg)
      have hT' : 𝒯.real (Ioi r) ≤ 𝒯.real {t | r ≤ t} :=
        measureReal_mono fun t ht => le_of_lt (show r < t from ht)
      have h1' := cdf_le_one μV r
      have h2' := cdf_le_one 𝒯 r
      have h3' := cdf_nonneg μV r
      have h4' := cdf_nonneg 𝒯 r
      rw [abs_le]
      constructor <;> linarith
    have htailV : ∀ r : ℝ, 0 < r → P.real {g | r ≤ rawV eps ν g} ≤
        cTail * Real.exp (-(rPrime vlo vhi * r)) := fun r hr => h.tail_rawV hvlo heps hr
    have htailT : ∀ r : ℝ, 0 < r → 𝒯.real {t | r ≤ t} ≤ Eτ * Real.exp (-(θτ * r)) :=
      fun r _ => hL.tail_le r
    have hE0 : 0 ≤ Eτ := by
      have := hL.tail_le 0
      have := measureReal_nonneg (μ := 𝒯) (s := {t | (0 : ℝ) ≤ t})
      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at *
      linarith
    have hfinV : ∀ r : ℝ, P {g | r ≤ rawV eps ν g} ≠ ⊤ := fun r => measure_ne_top _ _
    have hfinT : ∀ r : ℝ, 𝒯 {t | r ≤ t} ≠ ⊤ := fun r => measure_ne_top _ _
    have hIV := lintegral_Ioi_exp_mul_tail_le P (U := rawV eps ν) cTail_pos.le hr'
      (show γ ≤ rPrime vlo vhi / 2 by linarith) htailV hfinV hr₂0
    have hIT := lintegral_Ioi_exp_mul_tail_le 𝒯 (U := fun t => t) hE0 hθτ
      (show γ ≤ θτ / 2 by linarith) htailT hfinT hr₂0
    calc ∫⁻ r in Ici r₂, ENNReal.ofReal (Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r|)
        = ∫⁻ r in Ioi r₂, ENNReal.ofReal (Real.exp (γ * r) * |cdf μV r - cdf 𝒯 r|) := by
          rw [Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]
      _ ≤ ∫⁻ r in Ioi r₂, (ENNReal.ofReal (Real.exp (γ * r)) * P {g | r ≤ rawV eps ν g} +
            ENNReal.ofReal (Real.exp (γ * r)) * 𝒯 {t | r ≤ t}) :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hpt))
      _ = (∫⁻ r in Ioi r₂, ENNReal.ofReal (Real.exp (γ * r)) * P {g | r ≤ rawV eps ν g}) +
            ∫⁻ r in Ioi r₂, ENNReal.ofReal (Real.exp (γ * r)) * 𝒯 {t | r ≤ t} := by
          refine lintegral_add_right _ ?_
          have hanti : Antitone fun r : ℝ => 𝒯 {t | r ≤ t} := fun a b hab =>
            measure_mono fun t (ht : b ≤ t) => le_trans hab ht
          exact ((measurable_const.mul measurable_id).exp.ennreal_ofReal).mul hanti.measurable
      _ ≤ ENNReal.ofReal (2 * cTail / rPrime vlo vhi * Real.exp (-(rPrime vlo vhi * r₂ / 2))) +
            ENNReal.ofReal (2 * Eτ / θτ * Real.exp (-(θτ * r₂ / 2))) := add_le_add hIV hIT
      _ = _ := by
          rw [← ENNReal.ofReal_add (mul_nonneg (div_nonneg (by linarith [cTail_pos]) hr'.le)
            (Real.exp_pos _).le) (mul_nonneg (div_nonneg (by linarith) hθτ.le) (Real.exp_pos _).le)]
  calc _ ≤ ENNReal.ofReal (r₁ * Real.exp (γ * r₁)) +
        ENNReal.ofReal (Real.exp γ * Eτ * (12 * χ / (θτ * eps) + vhi / eps ^ 2) +
          pfail * r₂ * Real.exp (γ * r₂)) +
        ENNReal.ofReal (2 * cTail / rPrime vlo vhi * Real.exp (-(rPrime vlo vhi * r₂ / 2)) +
          2 * Eτ / θτ * Real.exp (-(θτ * r₂ / 2))) := add_le_add (add_le_add hpi hpii) hpiii
    _ = _ := by
        have hE0 : 0 ≤ Eτ := by
          have := hL.tail_le 0
          have := measureReal_nonneg (μ := 𝒯) (s := {t | (0 : ℝ) ≤ t})
          simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at *
          linarith
        have hvhi0 : 0 ≤ vhi := hvhi.le
        have hA0 : 0 ≤ Real.exp γ * Eτ * (12 * χ / (θτ * eps) + vhi / eps ^ 2) :=
          mul_nonneg (mul_nonneg (Real.exp_pos _).le hE0)
            (add_nonneg (by positivity) (div_nonneg hvhi0 (by positivity)))
        have hC0 : 0 ≤ 2 * cTail / rPrime vlo vhi * Real.exp (-(rPrime vlo vhi * r₂ / 2)) +
            2 * Eτ / θτ * Real.exp (-(θτ * r₂ / 2)) :=
          add_nonneg (mul_nonneg (div_nonneg (by linarith [cTail_pos]) hr'.le) (Real.exp_pos _).le)
            (mul_nonneg (div_nonneg (by linarith) hθτ.le) (Real.exp_pos _).le)
        rw [← ENNReal.ofReal_add (by positivity) (add_nonneg hA0 (by positivity)),
          ← ENNReal.ofReal_add (add_nonneg (by positivity) (add_nonneg hA0 (by positivity))) hC0]
        unfold mainBound
        rfl

end

end PGM
