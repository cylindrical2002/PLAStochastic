import PLAStochastic.Index.GEP.SurvivalBound.WordFunctional
import PLAStochastic.Index.GEP.RawDisc.MixtureLaws

/-!
# WP4 `SurvivalBound`: absolute bounds through the positive mixture, and large deviations

Source: `task-survival.md` (P3), `analytic-response.md` §5.

**Absolute values.**  For `b = ‖1 - z‖ + ‖z‖` and `t = ‖z‖ / b ∈ [0, 1]`, the coefficients satisfy
`‖(1-z)^{n-|S|} z^{|S|}‖ = b^n (1-t)^{n-|S|} t^{|S|}`, so the word expansion of the positive
mixture (`integral_iidLaw_mix`) gives

`‖surv_wint n H‖ ≤ b^n ∫ H' d(mixPM ν σ t)^{⊗n}`   whenever `‖H‖ ≤ H'`

(`surv_norm_wint_le_mix`).  The law `ρ̃ = mixPM ν σ t` is positive, has mean exactly one and the
exponential moment `ExpMom (θMix θ θσ) (BMix D θ A)` (`surv_mix_facts`).

**Large deviations** for iid positive mean-one gaps with `E e^{θ₁ X} ≤ B₁`, `C = 8 B₁/θ₁²`,
`lam0 = min(θ₁/4, 1/(16C))`, `c = bernsteinRate θ₁ B₁`, `κ = min(lam0/4, 9c/512)`:

* `surv_mgf_le`: `E e^{s S_k} ≤ exp(k (s + C s²))` for `0 ≤ s ≤ θ₁/2`;
* `surv_bad_integral_le` (bad slopes, `k ≥ 1`, `0 ≤ γ' ≤ κ/8`):
  `E[e^{γ' S_k} 1{S_k ≥ 3k/2 ∨ S_k ≤ 5k/8}] ≤ 3 e^{-κ k}`
  (upper tail by the moment generating function, lower tail by `iid_endpoint_bernstein`);
* `surv_short_integral_le` (short paths, `1 ≤ k ≤ 8ε`, `0 ≤ γ' ≤ lam0/8`):
  `E[e^{γ' S_k} 1{∃ t ≤ k, ε < |S_t - t|}] ≤ 2 e^{20 ε γ'} e^{-c ε/8} + e^{-10 ε lam0}`
  (`iid_maximal_bernstein` and the split at `S_k = 20ε`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

variable {D θ vlo vhi : ℝ}

/-! ## Absolute values through the positive mixture -/

theorem surv_b_pos (z : ℂ) : 1 ≤ ‖1 - z‖ + ‖z‖ := by
  have h := norm_sub_norm_le (1 : ℂ) z
  rw [norm_one] at h
  linarith

/-- The mixing parameter `t = ‖z‖ / (‖1 - z‖ + ‖z‖)` of the positive mixture. -/
def surv_tz (z : ℂ) : ℝ := ‖z‖ / (‖1 - z‖ + ‖z‖)

theorem surv_tz_mem (z : ℂ) : surv_tz z ∈ Icc (0 : ℝ) 1 := by
  have hb := surv_b_pos z
  unfold surv_tz
  refine ⟨div_nonneg (norm_nonneg _) (by linarith), ?_⟩
  rw [div_le_one (by linarith)]
  linarith [norm_nonneg (1 - z)]

theorem surv_wcoef_norm_eq (z : ℂ) {n : ℕ} {S : Finset ℕ} (hS : S.card ≤ n) :
    ‖surv_wcoef z n S‖ = (‖1 - z‖ + ‖z‖) ^ n * wordCoef (surv_tz z) n S := by
  have hb := surv_b_pos z
  have hb0 : (‖1 - z‖ + ‖z‖) ≠ 0 := by linarith
  have h1 : 1 - surv_tz z = ‖1 - z‖ / (‖1 - z‖ + ‖z‖) := by
    unfold surv_tz
    rw [eq_div_iff hb0, sub_mul, div_mul_cancel₀ _ hb0]
    ring
  rw [norm_surv_wcoef, wordCoef, h1, surv_tz, div_pow, div_pow, div_mul_div_comm, ← pow_add,
    Nat.sub_add_cancel hS, ← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero _ hb0)]

/-- **Absolute bound through the positive mixture**: if `‖H‖ ≤ H'` a.e. under every word law, with
`H'` measurable, reading the first `n` coordinates and integrable, then
`‖surv_wint n H‖ ≤ b^n ∫ H' d(mixPM ν σ t)^{⊗ℕ}`. -/
theorem surv_norm_wint_le_mix (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (n : ℕ)
    {H : (ℕ → ℝ) → ℂ} {H' : (ℕ → ℝ) → ℝ} (hH'm : Measurable H') (hdep : DepPrefix n H')
    (hint : ∀ S, Integrable H' (wordLaw ν σ S))
    (hle : ∀ S, ∀ᵐ g ∂(wordLaw ν σ S), ‖H g‖ ≤ H' g) :
    ‖surv_wint ν σ z n H‖ ≤
      (‖1 - z‖ + ‖z‖) ^ n * ∫ g, H' g ∂(iidLaw (mixPM ν σ (surv_tz z))) := by
  refine (norm_surv_wint_le ν σ z n H).trans ?_
  rw [integral_iidLaw_mix ν σ (surv_tz_mem z) hH'm hdep (fun S _ => hint S), Finset.mul_sum]
  refine Finset.sum_le_sum fun S hS => ?_
  have hcard : S.card ≤ n := by simpa using Finset.card_le_card (Finset.mem_powerset.1 hS)
  rw [surv_wcoef_norm_eq z hcard, mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
    (wordCoef_nonneg (surv_tz_mem z) n S)) (by positivity)
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => norm_nonneg _) (hint S)
    (hle S)

/-! ## The positive mixture law -/

/-- The positive mixture `mixPM ν σ t` is positive, has mean one and the exponential moment of
the class. -/
theorem surv_mix_facts (hθ : 0 < θ) (hvlo : 0 < vlo) {A θσ : ℝ} (hθσ : 0 < θσ)
    {ν σ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hσ : SigmaLaw A θσ σ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (mixPM ν σ t : Measure ℝ) (Iic 0) = 0 ∧ lawMean (mixPM ν σ t) = 1 ∧
      ExpMom (θMix θ θσ) (BMix D θ A) (mixPM ν σ t) := by
  refine ⟨mixPM_pos (hν.pos' hθ hvlo) hσ.pos t, ?_, expMom_mix hθ hvlo hν hσ ht⟩
  have hνi : Integrable (fun x : ℝ => x) (ν : Measure ℝ) :=
    (moments_of_cube (hν.pos' hθ hvlo) (hν.cube hθ hvlo).1).1
  have hσi : Integrable (fun x : ℝ => x) (σ : Measure ℝ) :=
    (moments_of_cube hσ.pos (hσ.cube hθσ).1).1
  have hνm : ∫ x, x ∂(ν : Measure ℝ) = 1 := hν.mean
  have hσm : ∫ x, x ∂(σ : Measure ℝ) = 1 := hσ.mean
  show ∫ x, x ∂(mixPM ν σ t : Measure ℝ) = 1
  rw [integral_mixPM ht hνi hσi, hνm, hσm]
  ring

/-- Exponential moments of the keys under every word law, at rates `l ≤ lamMix`. -/
theorem surv_integrable_exp_wordLaw (hθ : 0 < θ) (hvlo : 0 < vlo) {A θσ : ℝ} (hθσ : 0 < θσ)
    {ν σ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hσ : SigmaLaw A θσ σ) {l : ℝ}
    (hl0 : 0 ≤ l) (hl : l ≤ lamMix D θ A θσ) (S : Finset ℕ) (k : ℕ) :
    Integrable (fun g => Real.exp (l * gapKeys g k)) (wordLaw ν σ S) := by
  obtain ⟨⟨-, -, hν2⟩, ⟨-, -, hσ2⟩⟩ := lintegral_exp_le_two hθ hvlo hθσ hν hσ hl0 hl
  rw [wordLaw_eq_piLaw]
  refine rawAsm_integrable_exp_gapKeys (fun j => ?_) k
  by_cases hj : j ∈ S
  · simp only [hj, if_true]; exact hσ2
  · simp only [hj, if_false]; exact hν2

/-! ## Moment generating functions of the keys -/

/-- `E e^{s S_k} ≤ M^k` under the iid law when `E e^{s X} ≤ M`. -/
theorem surv_exp_gapKeys_le (ρ : ProbabilityMeasure ℝ) {s M : ℝ} (hM0 : 0 ≤ M)
    (hint : Integrable (fun x => Real.exp (s * x)) (ρ : Measure ℝ))
    (hM : ∫ x, Real.exp (s * x) ∂(ρ : Measure ℝ) ≤ M) (k : ℕ) :
    Integrable (fun g => Real.exp (s * gapKeys g k)) (iidLaw ρ) ∧
      ∫ g, Real.exp (s * gapKeys g k) ∂(iidLaw ρ) ≤ M ^ k := by
  have hl : ∫⁻ x, ENNReal.ofReal (Real.exp (s * x)) ∂(ρ : Measure ℝ) ≤ ENNReal.ofReal M := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hM
  have hL : ∫⁻ g, ENNReal.ofReal (Real.exp (s * gapKeys g k)) ∂(iidLaw ρ) ≤
      ENNReal.ofReal M ^ k :=
    lintegral_exp_gapKeys_le (ρ := fun _ => ρ) (fun _ => hl) k
  have hm : Measurable fun g : ℕ → ℝ => Real.exp (s * gapKeys g k) :=
    ((rawAsm_measurable_gapKeys k).const_mul s).exp
  have hi : Integrable (fun g => Real.exp (s * gapKeys g k)) (iidLaw ρ) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    exact lt_of_le_of_lt hL (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
    hm.aestronglyMeasurable]
  rw [← ENNReal.ofReal_pow hM0] at hL
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hL).trans_eq
    (ENNReal.toReal_ofReal (pow_nonneg hM0 k))

/-- `C = 8 B₁ / θ₁²`, the curvature of the moment generating function. -/
def surv_mgfC (θ₁ B₁ : ℝ) : ℝ := 8 * B₁ / θ₁ ^ 2

/-- `lam0 = min(θ₁/4, 1/(16 C))`, the tilt of the large-deviation bounds. -/
def surv_lam (θ₁ B₁ : ℝ) : ℝ := min (θ₁ / 4) (1 / (16 * surv_mgfC θ₁ B₁))

/-- `κ = min(lam0/4, 9c/512)`, the rate of the bad-slope bound. -/
def surv_rate (θ₁ B₁ : ℝ) : ℝ := min (surv_lam θ₁ B₁ / 4) (9 * bernsteinRate θ₁ B₁ / 512)

theorem surv_mgfC_pos {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) (hB₁ : 0 < B₁) : 0 < surv_mgfC θ₁ B₁ := by
  unfold surv_mgfC; positivity

theorem surv_lam_pos {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) (hB₁ : 0 < B₁) : 0 < surv_lam θ₁ B₁ := by
  have := surv_mgfC_pos hθ₁ hB₁
  unfold surv_lam
  exact lt_min (by positivity) (by positivity)

theorem surv_rate_pos {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) (hB₁ : 0 < B₁) : 0 < surv_rate θ₁ B₁ := by
  have := surv_lam_pos hθ₁ hB₁
  have := bernsteinRate_pos hθ₁ hB₁
  unfold surv_rate
  exact lt_min (by positivity) (by positivity)

theorem surv_lam_le_quarter (θ₁ B₁ : ℝ) : surv_lam θ₁ B₁ ≤ θ₁ / 4 := min_le_left _ _

/-- The tilted exponent: for `0 ≤ γ' ≤ lam0/8`, `s = γ' + lam0 ≤ θ₁/2` and `s + C s² ≤ 5 lam0 / 4`. -/
theorem surv_lam_mgf_le {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) (hB₁ : 0 < B₁) {γ' : ℝ} (hγ0 : 0 ≤ γ')
    (hγ : γ' ≤ surv_lam θ₁ B₁ / 8) :
    γ' + surv_lam θ₁ B₁ ≤ θ₁ / 2 ∧
      (γ' + surv_lam θ₁ B₁) + surv_mgfC θ₁ B₁ * (γ' + surv_lam θ₁ B₁) ^ 2 ≤
        5 * surv_lam θ₁ B₁ / 4 := by
  have hC := surv_mgfC_pos hθ₁ hB₁
  have hl := surv_lam_pos hθ₁ hB₁
  set C := surv_mgfC θ₁ B₁
  set lam0 := surv_lam θ₁ B₁ with hlam0
  have hl1 : lam0 ≤ θ₁ / 4 := min_le_left _ _
  have hl2 : lam0 ≤ 1 / (16 * C) := min_le_right _ _
  have hCl : C * lam0 ≤ 1 / 16 := by
    rw [le_div_iff₀ (by positivity)] at hl2
    linarith
  refine ⟨by linarith, ?_⟩
  have hs : γ' + lam0 ≤ 9 * lam0 / 8 := by linarith
  have hsq : C * (γ' + lam0) ^ 2 ≤ C * (9 * lam0 / 8) ^ 2 := by
    gcongr
  have he : C * (9 * lam0 / 8) ^ 2 = 81 / 64 * (C * lam0) * lam0 := by ring
  have h3 : 81 / 64 * (C * lam0) * lam0 ≤ 81 / 64 * (1 / 16) * lam0 := by
    gcongr
  linarith

/-- **Moment generating function of the keys**: `E e^{s S_k} ≤ exp(k (s + C s²))` for
`0 ≤ s ≤ θ₁/2`. -/
theorem surv_mgf_le {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) {ρ : ProbabilityMeasure ℝ}
    (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (hmean : lawMean ρ = 1) (hexp : ExpMom θ₁ B₁ ρ)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ θ₁ / 2) (k : ℕ) :
    Integrable (fun g => Real.exp (s * gapKeys g k)) (iidLaw ρ) ∧
      ∫ g, Real.exp (s * gapKeys g k) ∂(iidLaw ρ) ≤
        Real.exp (k * (s + surv_mgfC θ₁ B₁ * s ^ 2)) := by
  have hae : ∀ᵐ x ∂(ρ : Measure ℝ), 0 ≤ x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hpos] with x hx
    simp only [Set.mem_Iic, not_le] at hx
    exact hx.le
  have hX1 : Integrable (fun x : ℝ => x) (ρ : Measure ℝ) :=
    (moments_of_cube hpos (cube_of_expMom hpos hθ₁ hexp.integrable hexp.le).1).1
  have hXm : ∫ x, x ∂(ρ : Measure ℝ) ≤ 1 := hmean.le
  obtain ⟨hint, hle⟩ := integral_exp_mul_le_of_expMom (P := (ρ : Measure ℝ)) (X := fun x => x)
    hθ₁ hae hX1 hXm hexp.integrable hexp.le hs0 hs
  have h := surv_exp_gapKeys_le ρ (Real.exp_pos _).le hint hle k
  rw [← Real.exp_nat_mul] at h
  exact h

/-! ## Bad slopes -/

/-- **Large deviations of the bad slopes**: for `k ≥ 1` and `0 ≤ γ' ≤ κ/8`,
`E[e^{γ' S_k} 1{S_k ≥ 3k/2 ∨ S_k ≤ 5k/8}] ≤ 3 e^{-κ k}`. -/
theorem surv_bad_integral_le {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) {ρ : ProbabilityMeasure ℝ}
    (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (hmean : lawMean ρ = 1) (hexp : ExpMom θ₁ B₁ ρ)
    {k : ℕ} (hk : 1 ≤ k) {γ' : ℝ} (hγ0 : 0 ≤ γ') (hγ : γ' ≤ surv_rate θ₁ B₁ / 8) :
    ∫ g, {g : ℕ → ℝ | 3 * k / 2 ≤ gapKeys g k ∨ gapKeys g k ≤ 5 * k / 8}.indicator
      (fun g => Real.exp (γ' * gapKeys g k)) g ∂(iidLaw ρ) ≤
      3 * Real.exp (-(surv_rate θ₁ B₁ * k)) := by
  have hB₁ : 0 < B₁ := (integral_exp_pos hexp.integrable).trans_le hexp.le
  set lam0 := surv_lam θ₁ B₁ with hlam0
  set κ := surv_rate θ₁ B₁ with hκ
  set c := bernsteinRate θ₁ B₁ with hc
  have hlpos : 0 < lam0 := surv_lam_pos hθ₁ hB₁
  have hcpos : 0 < c := bernsteinRate_pos hθ₁ hB₁
  have hκ1 : κ ≤ lam0 / 4 := min_le_left _ _
  have hκ2 : κ ≤ 9 * c / 512 := min_le_right _ _
  have hgl : γ' ≤ lam0 / 8 := by linarith
  obtain ⟨hs1, hs2⟩ := surv_lam_mgf_le hθ₁ hB₁ hγ0 hgl
  obtain ⟨hint, hmgf⟩ := surv_mgf_le hθ₁ hpos hmean hexp (by positivity : 0 ≤ γ' + lam0) hs1 k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hS : Measurable fun g : ℕ → ℝ => gapKeys g k := rawAsm_measurable_gapKeys k
  have hset : MeasurableSet {g : ℕ → ℝ | gapKeys g k ≤ 5 * k / 8} :=
    measurableSet_le hS measurable_const
  set A := {g : ℕ → ℝ | 3 * k / 2 ≤ gapKeys g k ∨ gapKeys g k ≤ 5 * k / 8} with hA
  set B := {g : ℕ → ℝ | gapKeys g k ≤ 5 * k / 8} with hB
  -- the pointwise bound
  have hpt : ∀ g, A.indicator (fun g => Real.exp (γ' * gapKeys g k)) g ≤
      Real.exp (-(3 * lam0 * k / 2)) * Real.exp ((γ' + lam0) * gapKeys g k) +
        B.indicator (fun _ => Real.exp (5 * γ' * k / 8)) g := by
    intro g
    have h1 : 0 ≤ Real.exp (-(3 * lam0 * k / 2)) * Real.exp ((γ' + lam0) * gapKeys g k) := by
      positivity
    have h2 : 0 ≤ B.indicator (fun _ => Real.exp (5 * γ' * k / 8)) g :=
      Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) g
    by_cases hg : g ∈ A
    · rw [Set.indicator_of_mem hg]
      have hg' : 3 * k / 2 ≤ gapKeys g k ∨ gapKeys g k ≤ 5 * k / 8 := hg
      rcases hg' with hg' | hg'
      · have h3 : Real.exp (γ' * gapKeys g k) ≤
            Real.exp (-(3 * lam0 * k / 2)) * Real.exp ((γ' + lam0) * gapKeys g k) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          have := mul_le_mul_of_nonneg_left hg' hlpos.le
          linarith
        linarith
      · have hgB : g ∈ B := hg'
        rw [Set.indicator_of_mem hgB]
        have h3 : Real.exp (γ' * gapKeys g k) ≤ Real.exp (5 * γ' * k / 8) := by
          refine Real.exp_le_exp.2 ?_
          have := mul_le_mul_of_nonneg_left hg' hγ0
          linarith
        linarith
    · rw [Set.indicator_of_notMem hg]
      exact add_nonneg h1 h2
  have hint2 : Integrable (fun g => Real.exp (-(3 * lam0 * k / 2)) *
      Real.exp ((γ' + lam0) * gapKeys g k) +
        B.indicator (fun _ => Real.exp (5 * γ' * k / 8)) g) (iidLaw ρ) :=
    (hint.const_mul _).add ((integrable_const _).indicator hset)
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun g =>
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) g) hint2
    (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_add (hint.const_mul _) ((integrable_const _).indicator hset), integral_const_mul,
    integral_indicator_const _ hset, smul_eq_mul]
  -- the upper tail
  have hA' : Real.exp (-(3 * lam0 * k / 2)) * ∫ g, Real.exp ((γ' + lam0) * gapKeys g k) ∂(iidLaw ρ) ≤
      Real.exp (-(κ * k)) := by
    calc Real.exp (-(3 * lam0 * k / 2)) * ∫ g, Real.exp ((γ' + lam0) * gapKeys g k) ∂(iidLaw ρ)
        ≤ Real.exp (-(3 * lam0 * k / 2)) *
          Real.exp (k * ((γ' + lam0) + surv_mgfC θ₁ B₁ * (γ' + lam0) ^ 2)) := by gcongr
      _ ≤ Real.exp (-(κ * k)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have h1 := mul_le_mul_of_nonneg_left hs2 hkpos.le
        have h2 := mul_le_mul_of_nonneg_right hκ1 hkpos.le
        linarith
  -- the lower tail
  have hB' : (iidLaw ρ).real B * Real.exp (5 * γ' * k / 8) ≤ 2 * Real.exp (-(κ * k)) := by
    have hsub : B ⊆ {g | 3 * k / 8 ≤ |gapKeys g k - k|} := by
      intro g hg
      have hg' : gapKeys g k ≤ 5 * k / 8 := hg
      show 3 * k / 8 ≤ |gapKeys g k - k|
      calc (3 * k / 8 : ℝ) ≤ k - gapKeys g k := by linarith
        _ ≤ |k - gapKeys g k| := le_abs_self _
        _ = |gapKeys g k - k| := abs_sub_comm _ _
    have hP := iid_endpoint_bernstein hθ₁ hpos hmean hexp k hk (d := 3 * k / 8) (by positivity)
    have hmin : min ((3 * (k : ℝ) / 8) ^ 2 / k) (3 * (k : ℝ) / 8) = 9 * k / 64 := by
      have e : (3 * k / 8 : ℝ) ^ 2 / k = 9 * k / 64 := by
        field_simp
        ring
      rw [e]
      exact min_eq_left (by linarith)
    rw [hmin] at hP
    calc (iidLaw ρ).real B * Real.exp (5 * γ' * k / 8)
        ≤ (iidLaw ρ).real {g | 3 * k / 8 ≤ |gapKeys g k - k|} * Real.exp (5 * γ' * k / 8) :=
          mul_le_mul_of_nonneg_right (measureReal_mono hsub (measure_ne_top _ _))
            (Real.exp_pos _).le
      _ ≤ 2 * Real.exp (-(c / 4 * (9 * k / 64))) * Real.exp (5 * γ' * k / 8) := by gcongr
      _ = 2 * Real.exp (-(c / 4 * (9 * k / 64)) + 5 * γ' * k / 8) := by
          rw [mul_assoc, ← Real.exp_add]
      _ ≤ 2 * Real.exp (-(κ * k)) := by
          gcongr
          have h1 := mul_le_mul_of_nonneg_right hγ hkpos.le
          have h2 := mul_le_mul_of_nonneg_right hκ2 hkpos.le
          have h3 := mul_pos hcpos hkpos
          linarith
  linarith

/-! ## Short paths -/

/-- The event `{∃ t ≤ k, ε < |S_t - t|}` of a large deviation from the line of slope one. -/
def surv_ld' (eps : ℝ) (k : ℕ) : Set (ℕ → ℝ) := {g | ∃ t ≤ k, eps < |gapKeys g t - t|}

theorem surv_measurableSet_ld' (eps : ℝ) (k : ℕ) : MeasurableSet (surv_ld' eps k) := by
  have e : surv_ld' eps k =
      ⋃ t ∈ Finset.range (k + 1), {g : ℕ → ℝ | eps < |gapKeys g t - t|} := by
    ext g
    simp only [surv_ld', Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop,
      Nat.lt_succ_iff]
  rw [e]
  exact Finset.measurableSet_biUnion _ fun t _ =>
    measurableSet_lt measurable_const ((rawAsm_measurable_gapKeys t).sub_const _).abs

theorem surv_depPrefix_ld' (eps : ℝ) (k : ℕ) :
    DepPrefix k (fun g => (surv_ld' eps k).indicator (fun _ => (1 : ℝ)) g) := by
  intro g g' hgg
  have hkeys : ∀ t ≤ k, gapKeys g t = gapKeys g' t := fun t ht =>
    Finset.sum_congr rfl fun s hs => hgg s (by have := Finset.mem_range.1 hs; omega)
  have hmem : g ∈ surv_ld' eps k ↔ g' ∈ surv_ld' eps k := by
    simp only [surv_ld', Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht, h⟩; exact ⟨t, ht, by rwa [← hkeys t ht]⟩
    · rintro ⟨t, ht, h⟩; exact ⟨t, ht, by rwa [hkeys t ht]⟩
  show (surv_ld' eps k).indicator (fun _ => (1 : ℝ)) g =
    (surv_ld' eps k).indicator (fun _ => (1 : ℝ)) g'
  by_cases hg : g ∈ surv_ld' eps k
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.1 hg)]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hmem.2 h))]

/-- **Large deviations of the short paths**: for `1 ≤ k ≤ 8ε`, `ε ≥ 1` and `0 ≤ γ' ≤ lam0/8`,
`E[e^{γ' S_k} 1{∃ t ≤ k, ε < |S_t - t|}] ≤ 2 e^{20 ε γ'} e^{-c ε / 8} + e^{-10 ε lam0}`. -/
theorem surv_short_integral_le {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) {ρ : ProbabilityMeasure ℝ}
    (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (hmean : lawMean ρ = 1) (hexp : ExpMom θ₁ B₁ ρ)
    {eps : ℝ} (heps : 1 ≤ eps) {k : ℕ} (hk1 : 1 ≤ k) (hk : (k : ℝ) ≤ 8 * eps) {γ' : ℝ}
    (hγ0 : 0 ≤ γ') (hγ : γ' ≤ surv_lam θ₁ B₁ / 8) :
    ∫ g, (surv_ld' eps k).indicator (fun g => Real.exp (γ' * gapKeys g k)) g ∂(iidLaw ρ) ≤
      2 * Real.exp (20 * eps * γ') * Real.exp (-(bernsteinRate θ₁ B₁ * eps / 8)) +
        Real.exp (-(10 * eps * surv_lam θ₁ B₁)) := by
  have hB₁ : 0 < B₁ := (integral_exp_pos hexp.integrable).trans_le hexp.le
  set lam0 := surv_lam θ₁ B₁ with hlam0
  set c := bernsteinRate θ₁ B₁ with hc
  have hlpos : 0 < lam0 := surv_lam_pos hθ₁ hB₁
  have hcpos : 0 < c := bernsteinRate_pos hθ₁ hB₁
  obtain ⟨hs1, hs2⟩ := surv_lam_mgf_le hθ₁ hB₁ hγ0 hγ
  obtain ⟨hint, hmgf⟩ := surv_mgf_le hθ₁ hpos hmean hexp (by positivity : 0 ≤ γ' + lam0) hs1 k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have heps0 : 0 < eps := by linarith
  have hset := surv_measurableSet_ld' eps k
  set A := surv_ld' eps k with hA
  -- the pointwise bound
  have hpt : ∀ g, A.indicator (fun g => Real.exp (γ' * gapKeys g k)) g ≤
      A.indicator (fun _ => Real.exp (20 * eps * γ')) g +
        Real.exp (-(20 * eps * lam0)) * Real.exp ((γ' + lam0) * gapKeys g k) := by
    intro g
    have h1 : 0 ≤ Real.exp (-(20 * eps * lam0)) * Real.exp ((γ' + lam0) * gapKeys g k) := by
      positivity
    have h2 : 0 ≤ A.indicator (fun _ => Real.exp (20 * eps * γ')) g :=
      Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) g
    by_cases hg : g ∈ A
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
      rcases le_or_gt (gapKeys g k) (20 * eps) with hS | hS
      · have h3 : Real.exp (γ' * gapKeys g k) ≤ Real.exp (20 * eps * γ') := by
          refine Real.exp_le_exp.2 ?_
          have := mul_le_mul_of_nonneg_left hS hγ0
          linarith
        linarith
      · have h3 : Real.exp (γ' * gapKeys g k) ≤
            Real.exp (-(20 * eps * lam0)) * Real.exp ((γ' + lam0) * gapKeys g k) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          have := mul_le_mul_of_nonneg_left hS.le hlpos.le
          linarith
        have := Real.exp_pos (20 * eps * γ')
        linarith
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
      linarith
  have hint2 : Integrable (fun g => A.indicator (fun _ => Real.exp (20 * eps * γ')) g +
      Real.exp (-(20 * eps * lam0)) * Real.exp ((γ' + lam0) * gapKeys g k)) (iidLaw ρ) :=
    ((integrable_const _).indicator hset).add (hint.const_mul _)
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun g =>
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) g) hint2
    (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_add ((integrable_const _).indicator hset) (hint.const_mul _), integral_const_mul,
    integral_indicator_const _ hset, smul_eq_mul]
  -- the maximal inequality
  have hA' : (iidLaw ρ).real A * Real.exp (20 * eps * γ') ≤
      2 * Real.exp (20 * eps * γ') * Real.exp (-(c * eps / 8)) := by
    have hP := iid_maximal_bernstein hθ₁ hpos hmean hexp k hk1 (x := eps) heps0
    have hmin : eps / 8 ≤ min (eps ^ 2 / k) eps := by
      refine le_min ?_ (by linarith)
      rw [le_div_iff₀ hkpos]
      nlinarith [mul_le_mul_of_nonneg_left hk heps0.le]
    have hP' : (iidLaw ρ).real A ≤ 2 * Real.exp (-(c * eps / 8)) := by
      refine hP.trans ?_
      gcongr
      have := mul_le_mul_of_nonneg_left hmin hcpos.le
      linarith
    calc (iidLaw ρ).real A * Real.exp (20 * eps * γ')
        ≤ 2 * Real.exp (-(c * eps / 8)) * Real.exp (20 * eps * γ') := by gcongr
      _ = 2 * Real.exp (20 * eps * γ') * Real.exp (-(c * eps / 8)) := by ring
  -- the moment generating function
  have hB' : Real.exp (-(20 * eps * lam0)) * ∫ g, Real.exp ((γ' + lam0) * gapKeys g k) ∂(iidLaw ρ) ≤
      Real.exp (-(10 * eps * lam0)) := by
    calc Real.exp (-(20 * eps * lam0)) * ∫ g, Real.exp ((γ' + lam0) * gapKeys g k) ∂(iidLaw ρ)
        ≤ Real.exp (-(20 * eps * lam0)) *
          Real.exp (k * ((γ' + lam0) + surv_mgfC θ₁ B₁ * (γ' + lam0) ^ 2)) := by gcongr
      _ ≤ Real.exp (-(10 * eps * lam0)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have h1 := mul_le_mul_of_nonneg_left hs2 hkpos.le
        have h2 := mul_le_mul_of_nonneg_right hk (by positivity : (0 : ℝ) ≤ 5 * lam0 / 4)
        linarith
  linarith

end

end PGM
