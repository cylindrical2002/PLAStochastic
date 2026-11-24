import PLAStochastic.Index.GEP.SurvivalBound.Constants
import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.RegularClass
import PLAStochastic.Index.GEP.DirectTerm.OfSurvivalBound

/-!
# WP4: `survivalBound : SurvivalBound` and `directTerm : DirectTerm`

Source: `research/2026-09-30-lean-gep-direct-term/task-survival.md` (P4),
`progress-surv.md` (总装).

Constants.  From the class row bound `norm_kRow_le_class` (`GEPKillClass`) we get `c₁ > 0`; set
`c' = min(c₁/8, 1)` and the output weight `γ = c'/8`.  For a direction class `(A, θσ)` the row
bound gives a radius `r₁`; with `θ₁ = θMix θ θσ`, `B₁ = BMix D θ A`, `κ = surv_rate θ₁ B₁`,
`λ₀ = surv_lam θ₁ B₁`, `c_B = bernsteinRate θ₁ B₁`, `l_m = lamMix D θ A θσ`:

* `r = min(r₁, 1/3, κ/4, c_B/256, 5λ₀/16)`;
* `e₀ = max(1, c'/(8 m))`, `m = min(κ/8, λ₀/8, l_m)`, so that `γ' = γ/ε² ≤ m` for `ε ≥ e₀`;
* `K₁ = 3√(4D+1) e^{c₁/8} + 1`, `K₂ = 3√(20D+1) + 1`, `K₃ = K₁²(3eDK₁+1)e^{1/2}`,
  `K_s = 9K₂ + 110`, `K = 9eK_s + 1152 e^{1/2} K₃ (4/(3c'))⁵ + 3(1 + 2/κ)`, `p = 13`;
* `B_k = K_s ε e · e^{-k/(8ε)} + K₃ ε³ (k+1)⁴ e^{-6γ'k} + 3 e^{-κk/2}`.

The three regimes: `k = 0` (`surv_cSurv_zero_le`), `1 ≤ k ≤ 8ε` (`surv_short_bound`) and
`k ≥ 8ε` (`surv_long_bound`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

variable {D θ vlo vhi : ℝ}

/-! ## The three regimes -/

/-- **The short regime** `1 ≤ k ≤ 8ε`: `‖cSurv‖ ≤ (9 K₂ + 110) ε`. -/
theorem surv_case_short (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) {A θσ : ℝ} (hθσ : 0 < θσ)
    {c₁ : ℝ} (hc₁ : 0 ≤ c₁) {ν σ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hσ : SigmaLaw A θσ σ) {z : ℂ} (hz3 : ‖z‖ ≤ 1 / 3) {r : ℝ} (hzr : ‖z‖ ≤ r)
    (hrcB : 16 * r ≤ bernsteinRate (θMix θ θσ) (BMix D θ A) / 16)
    (hrlam : 16 * r ≤ 5 * surv_lam (θMix θ θσ) (BMix D θ A))
    (hcls : ∀ α w β a : ℝ, 1 ≤ w → 1 / 2 ≤ |a| → ∀ φ : ℝ → ℂ, Measurable φ →
      (∀ y, ‖φ y‖ ≤ 1) → ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ,
        ‖kRow (Icc α (α + w)) ν σ z β a n φ y‖ ≤
          3 * Real.sqrt (2 * D * w) * Real.exp (-(c₁ * ((n : ℝ) - 1) / (2 * w ^ 2))) + ‖z‖ ^ n)
    {eps : ℝ} (heps : 1 ≤ eps) {γ' : ℝ} (hγ0 : 0 ≤ γ') (hγε : γ' * eps ≤ 1 / 8)
    (hγlam : γ' ≤ surv_lam (θMix θ θσ) (BMix D θ A) / 8) (hγlm : γ' ≤ lamMix D θ A θσ)
    {G : ℝ → ℝ} (hG : Measurable G) (hGb : ∀ y, 0 ≤ y → |G y| ≤ Real.exp (γ' * y)) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : (k : ℝ) ≤ 8 * eps) :
    ‖cSurv eps ν σ z k G‖ ≤ (9 * (3 * Real.sqrt (20 * D + 1) + 1) + 110) * eps := by
  have hθ₁ : 0 < θMix θ θσ := θMix_pos hθ hθσ
  have hmix := surv_mix_facts hθ hvlo hθσ hν hσ (surv_tz_mem z)
  have hint : ∀ S, Integrable (fun g => Real.exp (γ' * gapKeys g k)) (wordLaw ν σ S) := fun S =>
    surv_integrable_exp_wordLaw hθ hvlo hθσ hν hσ hγ0 hγlm S k
  have hRow := surv_rowBound_free hD heps ν σ z hz3 hcls hc₁ hk1
  have h := surv_short_bound ν σ z heps hk1 hk (hν.pos' hθ hvlo) hσ.pos hG hγ0 hGb hint hRow hθ₁
    hmix hγlam
  refine h.trans ?_
  have heps0 : 0 < eps := by linarith
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hzr
  set K₂ := 3 * Real.sqrt (20 * D + 1) + 1 with hK₂
  have hK₂ : 0 ≤ K₂ := by positivity
  -- the main term
  have hE9 : Real.exp (γ' * (9 * eps)) ≤ 9 := by
    calc Real.exp (γ' * (9 * eps)) ≤ Real.exp 2 := Real.exp_le_exp.2 (by nlinarith)
      _ = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3 ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le surv_exp_one_le_three 2
      _ = 9 := by norm_num
  have hmain : Real.exp (γ' * (9 * eps)) * (K₂ * eps) ≤ 9 * K₂ * eps := by
    have := mul_le_mul_of_nonneg_right hE9 (mul_nonneg hK₂ heps0.le)
    linarith
  -- the error term
  have hbk : (‖1 - z‖ + ‖z‖) ^ k ≤ Real.exp (16 * r * eps) :=
    (surv_b_pow_le hzr k).trans (Real.exp_le_exp.2 (by nlinarith))
  have hA : Real.exp (20 * eps * γ') ≤ 27 := by
    calc Real.exp (20 * eps * γ') ≤ Real.exp 3 := Real.exp_le_exp.2 (by nlinarith)
      _ = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_pos _).le surv_exp_one_le_three 3
      _ = 27 := by norm_num
  have hB : (‖1 - z‖ + ‖z‖) ^ k * Real.exp (-(bernsteinRate (θMix θ θσ) (BMix D θ A) * eps / 8)) ≤
      1 := by
    calc _ ≤ Real.exp (16 * r * eps) *
          Real.exp (-(bernsteinRate (θMix θ θσ) (BMix D θ A) * eps / 8)) :=
          mul_le_mul_of_nonneg_right hbk (Real.exp_pos _).le
      _ ≤ 1 := by
          rw [← Real.exp_add, Real.exp_le_one_iff]
          nlinarith
  have hC : (‖1 - z‖ + ‖z‖) ^ k * Real.exp (-(10 * eps * surv_lam (θMix θ θσ) (BMix D θ A))) ≤
      1 := by
    calc _ ≤ Real.exp (16 * r * eps) *
          Real.exp (-(10 * eps * surv_lam (θMix θ θσ) (BMix D θ A))) :=
          mul_le_mul_of_nonneg_right hbk (Real.exp_pos _).le
      _ ≤ 1 := by
          rw [← Real.exp_add, Real.exp_le_one_iff]
          nlinarith
  have hbk0 : 0 ≤ (‖1 - z‖ + ‖z‖) ^ k := by positivity
  have hAX : Real.exp (20 * eps * γ') * ((‖1 - z‖ + ‖z‖) ^ k *
      Real.exp (-(bernsteinRate (θMix θ θσ) (BMix D θ A) * eps / 8))) ≤ 27 * 1 :=
    mul_le_mul hA hB (by positivity) (by norm_num)
  have herr : (‖1 - z‖ + ‖z‖) ^ k *
      (2 * (2 * Real.exp (20 * eps * γ') *
        Real.exp (-(bernsteinRate (θMix θ θσ) (BMix D θ A) * eps / 8)) +
          Real.exp (-(10 * eps * surv_lam (θMix θ θσ) (BMix D θ A))))) ≤ 110 := by
    have e : (‖1 - z‖ + ‖z‖) ^ k *
        (2 * (2 * Real.exp (20 * eps * γ') *
          Real.exp (-(bernsteinRate (θMix θ θσ) (BMix D θ A) * eps / 8)) +
            Real.exp (-(10 * eps * surv_lam (θMix θ θσ) (BMix D θ A))))) =
        2 * (2 * (Real.exp (20 * eps * γ') * ((‖1 - z‖ + ‖z‖) ^ k *
          Real.exp (-(bernsteinRate (θMix θ θσ) (BMix D θ A) * eps / 8)))) +
            (‖1 - z‖ + ‖z‖) ^ k * Real.exp (-(10 * eps * surv_lam (θMix θ θσ) (BMix D θ A)))) := by
      ring
    rw [e]
    linarith
  have h110 : (110 : ℝ) ≤ 110 * eps := by linarith
  linarith

/-- **The long regime** `8ε ≤ k`: `‖cSurv‖ ≤ K₃ (k+1)⁴ ε³ e^{-6γ'k} + 3 e^{-κk/2}`. -/
theorem surv_case_long (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) {A θσ : ℝ} (hθσ : 0 < θσ)
    {c₁ : ℝ} (hc₁ : 0 < c₁) {ν σ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hσ : SigmaLaw A θσ σ) {z : ℂ} (hz3 : ‖z‖ ≤ 1 / 3) {r : ℝ} (hzr : ‖z‖ ≤ r)
    (hrκ : 2 * r ≤ surv_rate (θMix θ θσ) (BMix D θ A) / 2)
    (hcls : ∀ α w β a : ℝ, 1 ≤ w → 1 / 2 ≤ |a| → ∀ φ : ℝ → ℂ, Measurable φ →
      (∀ y, ‖φ y‖ ≤ 1) → ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ,
        ‖kRow (Icc α (α + w)) ν σ z β a n φ y‖ ≤
          3 * Real.sqrt (2 * D * w) * Real.exp (-(c₁ * ((n : ℝ) - 1) / (2 * w ^ 2))) + ‖z‖ ^ n)
    {eps : ℝ} (heps : 1 ≤ eps) {γ' : ℝ} (hγ0 : 0 < γ') (hγ1 : 8 * γ' ≤ 1)
    (hq : 8 * γ' ≤ c₁ / (8 * eps ^ 2)) (hγε : 4 * γ' * eps ≤ 1 / 2)
    (hγκ : γ' ≤ surv_rate (θMix θ θσ) (BMix D θ A) / 8) (hγlm : γ' ≤ lamMix D θ A θσ)
    {G : ℝ → ℝ} (hG : Measurable G) (hGb : ∀ y, 0 ≤ y → |G y| ≤ Real.exp (γ' * y)) {k : ℕ}
    (hk : 8 * eps ≤ k) :
    ‖cSurv eps ν σ z k G‖ ≤
      (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) ^ 2 *
        (3 * Real.exp 1 * D * (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) + 1) *
          Real.exp (1 / 2) * ((k : ℝ) + 1) ^ 4 * eps ^ 3 * Real.exp (-(6 * γ' * k)) +
        3 * Real.exp (-(surv_rate (θMix θ θσ) (BMix D θ A) / 2 * k)) := by
  have hθ₁ : 0 < θMix θ θσ := θMix_pos hθ hθσ
  have hmix := surv_mix_facts hθ hvlo hθσ hν hσ (surv_tz_mem z)
  have hint : ∀ S, Integrable (fun g => Real.exp (γ' * gapKeys g k)) (wordLaw ν σ S) := fun S =>
    surv_integrable_exp_wordLaw hθ hvlo hθσ hν hσ hγ0.le hγlm S k
  obtain ⟨f, hf, hf0, hfD, hνf⟩ := hν.kill_density_le hθ
  have hνac : (ν : Measure ℝ) ≪ volume := by
    rw [hνf]; exact withDensity_absolutelyContinuous _ _
  have heps0 : 0 < eps := by linarith
  set K₁ := 3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1 with hK₁
  have hK₁ : 1 ≤ K₁ := by
    have : 0 ≤ 3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) := by positivity
    linarith
  have hRB := surv_rowBound hD hc₁ heps hγ0 hγ1 hq ν σ z hz3 hcls
  have hRBpos : ∀ n : ℕ, 0 < K₁ * eps * Real.exp (-(8 * γ')) ^ n := fun n => by positivity
  have h := surv_long_bound ν σ z heps hk hνac hσ.ac (hν.pos' hθ hvlo) hσ.pos hf hf0 hD hfD hνf hG
    hγ0.le hGb hint (RB := fun n => K₁ * eps * Real.exp (-(8 * γ')) ^ n) hRBpos hRB hθ₁ hmix hγκ
  refine h.trans (add_le_add (surv_sum_goodB_le heps hγ0 hγε hD hK₁ hz3 k) ?_)
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hzr
  have hkr : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc (‖1 - z‖ + ‖z‖) ^ k * (3 * Real.exp (-(surv_rate (θMix θ θσ) (BMix D θ A) * k)))
      ≤ Real.exp (2 * r * k) * (3 * Real.exp (-(surv_rate (θMix θ θσ) (BMix D θ A) * k))) :=
        mul_le_mul_of_nonneg_right (surv_b_pow_le hzr k) (by positivity)
    _ = 3 * Real.exp (2 * r * k + -(surv_rate (θMix θ θσ) (BMix D θ A) * k)) := by
        rw [Real.exp_add]; ring
    _ ≤ 3 * Real.exp (-(surv_rate (θMix θ θσ) (BMix D θ A) / 2 * k)) := by
        gcongr
        nlinarith

/-! ## The survival bound -/

/-- The rate `γ' = c'/(8ε²)` and its elementary bounds, for `ε ≥ max(1, c'/(8m))`. -/
theorem surv_gamma_facts {c' c₁ m eps : ℝ} (hc'0 : 0 < c') (hc'1 : c' ≤ 1) (hc'c : c' ≤ c₁ / 8)
    (hm0 : 0 < m) (heps1 : 1 ≤ eps) (he0 : c' / (8 * m) ≤ eps) :
    0 < c' / 8 / eps ^ 2 ∧ 8 * (c' / 8 / eps ^ 2) ≤ 1 ∧
      8 * (c' / 8 / eps ^ 2) ≤ c₁ / (8 * eps ^ 2) ∧ 4 * (c' / 8 / eps ^ 2) * eps ≤ 1 / 2 ∧
        c' / 8 / eps ^ 2 ≤ m := by
  have heps0 : 0 < eps := by linarith
  have heps2 : eps ≤ eps ^ 2 := by nlinarith
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩
  · have : c' / 8 / eps ^ 2 ≤ c' / 8 / 1 :=
      div_le_div_of_nonneg_left (by positivity) one_pos (by nlinarith)
    linarith
  · have e : 8 * (c' / 8 / eps ^ 2) = c' / eps ^ 2 := by field_simp
    rw [e, ← div_div]
    exact div_le_div_of_nonneg_right hc'c (by positivity)
  · have e : 4 * (c' / 8 / eps ^ 2) * eps = c' / (2 * eps) := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  · have h1 : c' / 8 ≤ m * eps := by
      rw [div_le_iff₀ (by positivity)] at he0
      linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- **The majorant is summable with `∑ B ≤ K ε¹³`.** -/
theorem surv_tsum_B_le {Ks K₃ κ c' eps γ' : ℝ} (hKs : 0 ≤ Ks) (hK₃ : 0 ≤ K₃) (hκ : 0 < κ)
    (hc' : 0 < c') (heps1 : 1 ≤ eps) (hγ' : γ' = c' / 8 / eps ^ 2) (hγ'0 : 0 < γ')
    (hα1 : 6 * γ' ≤ 1) :
    Summable (fun k : ℕ => Ks * eps * Real.exp 1 * Real.exp (-(1 / (8 * eps) * k)) +
      K₃ * eps ^ 3 * (((k : ℝ) + 1) ^ 4 * Real.exp (-(6 * γ' * k))) +
        3 * Real.exp (-(κ / 2 * k))) ∧
    ∑' k : ℕ, (Ks * eps * Real.exp 1 * Real.exp (-(1 / (8 * eps) * k)) +
      K₃ * eps ^ 3 * (((k : ℝ) + 1) ^ 4 * Real.exp (-(6 * γ' * k))) +
        3 * Real.exp (-(κ / 2 * k))) ≤
      (9 * Real.exp 1 * Ks + 1152 * Real.exp (1 / 2) * K₃ * (4 / (3 * c')) ^ 5 +
        3 * (1 + 2 / κ)) * eps ^ 13 := by
  have heps0 : 0 < eps := by linarith
  have hα0 : 0 < 6 * γ' := by positivity
  obtain ⟨hs1, ht1⟩ := surv_tsum_exp_neg (β := 1 / (8 * eps)) (by positivity)
  obtain ⟨hs2, ht2⟩ := surv_tsum_poly hα0 hα1
  obtain ⟨hs3, ht3⟩ := surv_tsum_exp_neg (β := κ / 2) (by positivity)
  refine ⟨((hs1.mul_left _).add (hs2.mul_left _)).add (hs3.mul_left _), ?_⟩
  rw [((hs1.mul_left _).add (hs2.mul_left _)).tsum_add (hs3.mul_left _),
    (hs1.mul_left _).tsum_add (hs2.mul_left _), tsum_mul_left, tsum_mul_left, tsum_mul_left]
  have hinv : ((6 * γ')⁻¹) ^ 5 = (4 / (3 * c')) ^ 5 * eps ^ 10 := by
    rw [hγ']
    field_simp
    ring
  have hε13 : eps ^ 2 ≤ eps ^ 13 := pow_le_pow_right₀ heps1 (by norm_num)
  have hε13' : eps ^ 13 = eps ^ 3 * eps ^ 10 := by ring
  have hε13'' : (1 : ℝ) ≤ eps ^ 13 := one_le_pow₀ heps1
  have h1 : Ks * eps * Real.exp 1 * ∑' k : ℕ, Real.exp (-(1 / (8 * eps) * k)) ≤
      9 * Real.exp 1 * Ks * eps ^ 13 := by
    have : 1 + 1 / (1 / (8 * eps)) = 1 + 8 * eps := by rw [one_div_one_div]
    rw [this] at ht1
    calc Ks * eps * Real.exp 1 * ∑' k : ℕ, Real.exp (-(1 / (8 * eps) * k))
        ≤ Ks * eps * Real.exp 1 * (1 + 8 * eps) := by gcongr
      _ ≤ Ks * eps * Real.exp 1 * (9 * eps) := by gcongr; linarith
      _ = 9 * Real.exp 1 * Ks * eps ^ 2 := by ring
      _ ≤ 9 * Real.exp 1 * Ks * eps ^ 13 := by gcongr
  have h2 : K₃ * eps ^ 3 * ∑' k : ℕ, ((k : ℝ) + 1) ^ 4 * Real.exp (-(6 * γ' * k)) ≤
      1152 * Real.exp (1 / 2) * K₃ * (4 / (3 * c')) ^ 5 * eps ^ 13 := by
    calc K₃ * eps ^ 3 * ∑' k : ℕ, ((k : ℝ) + 1) ^ 4 * Real.exp (-(6 * γ' * k))
        ≤ K₃ * eps ^ 3 * (1152 * Real.exp (1 / 2) * ((6 * γ')⁻¹) ^ 5) := by gcongr
      _ = 1152 * Real.exp (1 / 2) * K₃ * (4 / (3 * c')) ^ 5 * eps ^ 13 := by
          rw [hinv, hε13']; ring
  have h3 : 3 * ∑' k : ℕ, Real.exp (-(κ / 2 * k)) ≤ 3 * (1 + 2 / κ) * eps ^ 13 := by
    have : 1 + 1 / (κ / 2) = 1 + 2 / κ := by rw [one_div_div]
    rw [this] at ht3
    have h0 : 0 ≤ 3 * (1 + 2 / κ) := by positivity
    calc 3 * ∑' k : ℕ, Real.exp (-(κ / 2 * k)) ≤ 3 * (1 + 2 / κ) := by gcongr
      _ = 3 * (1 + 2 / κ) * 1 := (mul_one _).symm
      _ ≤ 3 * (1 + 2 / κ) * eps ^ 13 := mul_le_mul_of_nonneg_left hε13'' h0
  linarith

/-- **The pointwise majorant** in the three regimes. -/
theorem surv_B_pointwise (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) {A θσ : ℝ} (hθσ : 0 < θσ)
    {c₁ : ℝ} (hc₁ : 0 < c₁) {ν σ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hσ : SigmaLaw A θσ σ) {z : ℂ} {r : ℝ} (hzr : ‖z‖ ≤ r) (hr3 : r ≤ 1 / 3)
    (hrκ : r ≤ surv_rate (θMix θ θσ) (BMix D θ A) / 4)
    (hrcB : r ≤ bernsteinRate (θMix θ θσ) (BMix D θ A) / 256)
    (hrlam : r ≤ 5 * surv_lam (θMix θ θσ) (BMix D θ A) / 16)
    (hcls : ∀ α w β a : ℝ, 1 ≤ w → 1 / 2 ≤ |a| → ∀ φ : ℝ → ℂ, Measurable φ →
      (∀ y, ‖φ y‖ ≤ 1) → ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ,
        ‖kRow (Icc α (α + w)) ν σ z β a n φ y‖ ≤
          3 * Real.sqrt (2 * D * w) * Real.exp (-(c₁ * ((n : ℝ) - 1) / (2 * w ^ 2))) + ‖z‖ ^ n)
    {eps : ℝ} (heps1 : 1 ≤ eps) {γ' : ℝ} (hγ'0 : 0 < γ') (hγ'1 : 8 * γ' ≤ 1)
    (hγ'q : 8 * γ' ≤ c₁ / (8 * eps ^ 2)) (hγ'ε : 4 * γ' * eps ≤ 1 / 2)
    (hγ'κ : γ' ≤ surv_rate (θMix θ θσ) (BMix D θ A) / 8)
    (hγ'lam : γ' ≤ surv_lam (θMix θ θσ) (BMix D θ A) / 8) (hγ'lm : γ' ≤ lamMix D θ A θσ)
    {G : ℝ → ℝ} (hG : Measurable G) (hGb : ∀ y, 0 ≤ y → |G y| ≤ Real.exp (γ' * y)) (k : ℕ) :
    ‖cSurv eps ν σ z k G‖ ≤
      (9 * (3 * Real.sqrt (20 * D + 1) + 1) + 110) * eps * Real.exp 1 *
          Real.exp (-(1 / (8 * eps) * k)) +
        (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) ^ 2 *
          (3 * Real.exp 1 * D * (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) + 1) *
            Real.exp (1 / 2) * eps ^ 3 * (((k : ℝ) + 1) ^ 4 * Real.exp (-(6 * γ' * k))) +
        3 * Real.exp (-(surv_rate (θMix θ θσ) (BMix D θ A) / 2 * k)) := by
  have heps0 : 0 < eps := by linarith
  have hz3 : ‖z‖ ≤ 1 / 3 := hzr.trans hr3
  have hγ'ε' : γ' * eps ≤ 1 / 8 := by linarith
  have hKs1 : (1 : ℝ) ≤ 9 * (3 * Real.sqrt (20 * D + 1) + 1) + 110 := by
    have : 0 ≤ Real.sqrt (20 * D + 1) := Real.sqrt_nonneg _
    linarith
  have hT1 : 0 ≤ (9 * (3 * Real.sqrt (20 * D + 1) + 1) + 110) * eps * Real.exp 1 *
      Real.exp (-(1 / (8 * eps) * k)) := by positivity
  have hT2 : 0 ≤ (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) ^ 2 *
      (3 * Real.exp 1 * D * (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) + 1) *
        Real.exp (1 / 2) * eps ^ 3 * (((k : ℝ) + 1) ^ 4 * Real.exp (-(6 * γ' * k))) := by
    positivity
  have hT3 : 0 ≤ 3 * Real.exp (-(surv_rate (θMix θ θσ) (BMix D θ A) / 2 * k)) := by positivity
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have h := surv_cSurv_zero_le eps ν σ z G
    have hG0 : |G 0| ≤ 1 := by simpa using hGb 0 le_rfl
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    have hT1' : 1 ≤ (9 * (3 * Real.sqrt (20 * D + 1) + 1) + 110) * eps * Real.exp 1 *
        Real.exp (-(1 / (8 * eps) * ((0 : ℕ) : ℝ))) := by
      simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hKs1 heps1) he1
    linarith
  · rcases le_or_gt (k : ℝ) (8 * eps) with hk | hk
    · -- the short regime
      have h := surv_case_short hD hθ hvlo hθσ hc₁.le hν hσ hz3 hzr (by linarith) (by linarith)
        hcls heps1 hγ'0.le hγ'ε' hγ'lam hγ'lm hG hGb hkpos hk
      have hT1' : (9 * (3 * Real.sqrt (20 * D + 1) + 1) + 110) * eps ≤
          (9 * (3 * Real.sqrt (20 * D + 1) + 1) + 110) * eps * Real.exp 1 *
            Real.exp (-(1 / (8 * eps) * k)) := by
        rw [mul_assoc ((9 * (3 * Real.sqrt (20 * D + 1) + 1) + 110) * eps), ← Real.exp_add]
        refine le_mul_of_one_le_right (by positivity) (Real.one_le_exp ?_)
        have : 1 / (8 * eps) * (k : ℝ) ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
          exact hk
        linarith
      linarith
    · -- the long regime
      have h := surv_case_long hD hθ hvlo hθσ hc₁ hν hσ hz3 hzr (by linarith) hcls heps1 hγ'0
        hγ'1 hγ'q hγ'ε hγ'κ hγ'lm hG hGb hk.le
      have e : (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) ^ 2 *
          (3 * Real.exp 1 * D * (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) + 1) *
            Real.exp (1 / 2) * ((k : ℝ) + 1) ^ 4 * eps ^ 3 * Real.exp (-(6 * γ' * k)) =
          (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) ^ 2 *
          (3 * Real.exp 1 * D * (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) + 1) *
            Real.exp (1 / 2) * eps ^ 3 * (((k : ℝ) + 1) ^ 4 * Real.exp (-(6 * γ' * k))) := by
        ring
      rw [e] at h
      linarith

/-- **`SurvivalBound`** (`GEPRawDefs`): the complex survival integrals along
`ν_z = (1 - z) ν + z σ` have a summable majorant on a fixed disc, uniformly in the regular
class, with `∑ B ≤ K ε¹³`. -/
theorem survivalBound : SurvivalBound := by
  intro D θ vlo vhi hD hθ hvlo hvhi
  obtain ⟨c₁, hc₁, hcls⟩ := norm_kRow_le_class D θ vlo vhi hD hθ hvlo hvhi
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = min (c₁ / 8) 1 := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by rw [hc']; exact lt_min (by positivity) one_pos
  have hc'1 : c' ≤ 1 := by rw [hc']; exact min_le_right _ _
  have hc'c : c' ≤ c₁ / 8 := by rw [hc']; exact min_le_left _ _
  refine ⟨c' / 8, by positivity, fun A θσ hθσ => ?_⟩
  obtain ⟨r₁, hr₁, hrow⟩ := hcls A θσ hθσ
  -- the mixture constants
  have hθ₁ : 0 < θMix θ θσ := θMix_pos hθ hθσ
  have hB₁ : 0 < BMix D θ A := BMix_pos hD hθ A
  have hκ0 : 0 < surv_rate (θMix θ θσ) (BMix D θ A) := surv_rate_pos hθ₁ hB₁
  have hlam0 : 0 < surv_lam (θMix θ θσ) (BMix D θ A) := surv_lam_pos hθ₁ hB₁
  have hcB0 : 0 < bernsteinRate (θMix θ θσ) (BMix D θ A) := bernsteinRate_pos hθ₁ hB₁
  have hlm0 : 0 < lamMix D θ A θσ := lamMix_pos hθ hθσ
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = min (surv_rate (θMix θ θσ) (BMix D θ A) / 8)
    (min (surv_lam (θMix θ θσ) (BMix D θ A) / 8) (lamMix D θ A θσ)) := ⟨_, rfl⟩
  have hm0 : 0 < m := by
    rw [hm]; exact lt_min (by positivity) (lt_min (by positivity) hlm0)
  have hmκ : m ≤ surv_rate (θMix θ θσ) (BMix D θ A) / 8 := by rw [hm]; exact min_le_left _ _
  have hmlam : m ≤ surv_lam (θMix θ θσ) (BMix D θ A) / 8 := by
    rw [hm]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hmlm : m ≤ lamMix D θ A θσ := by rw [hm]; exact (min_le_right _ _).trans (min_le_right _ _)
  -- the radius
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (min r₁ (1 / 3)) (min (surv_rate (θMix θ θσ) (BMix D θ A) / 4)
    (min (bernsteinRate (θMix θ θσ) (BMix D θ A) / 256)
      (5 * surv_lam (θMix θ θσ) (BMix D θ A) / 16))) := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hr]
    exact lt_min (lt_min hr₁ (by norm_num)) (lt_min (by positivity) (lt_min (by positivity)
      (by positivity)))
  have hrr₁ : r ≤ r₁ := by rw [hr]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hr3 : r ≤ 1 / 3 := by rw [hr]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hrκ : r ≤ surv_rate (θMix θ θσ) (BMix D θ A) / 4 := by
    rw [hr]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hrcB : r ≤ bernsteinRate (θMix θ θσ) (BMix D θ A) / 256 := by
    rw [hr]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrlam : r ≤ 5 * surv_lam (θMix θ θσ) (BMix D θ A) / 16 := by
    rw [hr]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the constants
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = 3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1 := ⟨_, rfl⟩
  obtain ⟨K₃, hK₃⟩ : ∃ K₃ : ℝ,
    K₃ = K₁ ^ 2 * (3 * Real.exp 1 * D * K₁ + 1) * Real.exp (1 / 2) := ⟨_, rfl⟩
  obtain ⟨Ks, hKs⟩ : ∃ Ks : ℝ, Ks = 9 * (3 * Real.sqrt (20 * D + 1) + 1) + 110 := ⟨_, rfl⟩
  have hK₁0 : 0 < K₁ := by rw [hK₁]; positivity
  have hK₃0 : 0 < K₃ := by rw [hK₃]; positivity
  have hKs0 : 0 ≤ Ks := by rw [hKs]; positivity
  obtain ⟨e0, he0⟩ : ∃ e0 : ℝ, e0 = max 1 (c' / (8 * m)) := ⟨_, rfl⟩
  refine ⟨r, 9 * Real.exp 1 * Ks + 1152 * Real.exp (1 / 2) * K₃ * (4 / (3 * c')) ^ 5 +
    3 * (1 + 2 / surv_rate (θMix θ θσ) (BMix D θ A)), e0, 13, hr0,
    fun eps heps ν σ hν hσ G hG hGb => ?_⟩
  -- facts at this `ε`
  have heps1 : 1 ≤ eps := le_trans (by rw [he0]; exact le_max_left _ _) heps
  have he0m : c' / (8 * m) ≤ eps := le_trans (by rw [he0]; exact le_max_right _ _) heps
  obtain ⟨γ', hγ'⟩ : ∃ γ' : ℝ, γ' = c' / 8 / eps ^ 2 := ⟨_, rfl⟩
  have hfacts := surv_gamma_facts hc'0 hc'1 hc'c hm0 heps1 he0m
  rw [← hγ'] at hfacts
  obtain ⟨hγ'0, hγ'1, hγ'q, hγ'ε, hγ'm⟩ := hfacts
  have hGb' : ∀ y, 0 ≤ y → |G y| ≤ Real.exp (γ' * y) := fun y hy => by
    have := hGb y hy
    rw [hγ']
    rwa [show c' / 8 * y / eps ^ 2 = c' / 8 / eps ^ 2 * y by ring] at this
  obtain ⟨hsum, htsum⟩ := surv_tsum_B_le hKs0 hK₃0.le hκ0 hc'0 heps1 hγ' hγ'0 (by linarith)
  refine ⟨_, hsum, htsum, fun z hz k => ?_⟩
  have hzlt : ‖z‖ < r := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact hz
  have h := surv_B_pointwise hD hθ hvlo hθσ hc₁ hν hσ hzlt.le hr3 hrκ hrcB hrlam
    (hrow ν σ hν hσ z (hzlt.trans_le hrr₁)) heps1 hγ'0 hγ'1 hγ'q hγ'ε (hγ'm.trans hmκ)
    (hγ'm.trans hmlam) (hγ'm.trans hmlm) hG hGb' k
  rw [← hKs, ← hK₁, ← hK₃] at h
  exact h

/-- **`DirectTerm`** (`GEPResponseDefs`), through `SurvivalBound → RawDisc → DirectTerm`. -/
theorem directTerm : DirectTerm := directTerm_of_survivalBound survivalBound

end

end PGM
