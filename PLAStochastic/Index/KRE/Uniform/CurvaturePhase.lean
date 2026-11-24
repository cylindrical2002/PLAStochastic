import PLAStochastic.Index.KRE.Uniform.LayerPhases

/-!
# The curvature phase of the uniform two-phase height

Steps 2–4 of the proof of `thm:uniform` (Section 4 of
`research/2026-09-24-re-curvature-uniform/tex/main.tex`) after the noise phase, with
`s_ℓ = n / Δ_ℓ`, `D = effDelta n δ` and `A = log (ε / D)`.

* Upper count (`curvUp_layer`, `reHeight_le_curvPhase`): on a curvature layer with
  `z = D s / ε ≤ 1` the next layer has at most `2 (C_u + C_0) ≤ 2 ε` keys, so the run stops
  within two layers; with `z > 1`, `s_{ℓ+1} ≤ G √z`, i.e. the potential
  `W = ε s / (D G²)` satisfies `W_{ℓ+1} ≤ √W_ℓ`, while `log W > A` as long as `z > 1`
  (`exists_stop_of_halving`).  Hence `H ≤ m + log₂ (Y / A + 1) + 3`.
* Lower count (`curvLow_layer`, `lt_reHeight_curvPhase`): for `δ = D > 0`, on a curvature layer with
  `Δ ≥ Y²` and `s ≥ K_L` all three entries of `lem:curv`(a) are at least `c₅ √(δ s / ε)`.
  While `δ s / ε ≥ K₂` the layer does not terminate and `W = b² ε s / δ` satisfies
  `√W_ℓ ≤ W_{ℓ+1}`; the run stops only once `log W < 3 A`.  Starting from `s_m⁴ ≥ n` this
  gives `H > m + 1 + log₂ (Y / A) - 4`.
* Band layers (`band_layer_segs`): for `δ¹⁶ n > 1` a band layer has `M ≥ 2` and
  `(M - 1)⁴ ≥ n`, so it does not terminate and the next layer has `s⁴ ≥ n`; the layer after a
  noise layer has `s⁴ ≥ n` as well (`le_div_reDelta_uEnd_pow`).

Nothing here is probabilistic.
-/

namespace PGM

noncomputable section

/-! ## Real-variable steps -/

theorem rpow_two_thirds_pow_three {x : ℝ} (hx : 0 ≤ x) : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx,
    show (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem rpow_one_third_pow_three {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, show (1 / 3 : ℝ) * ((3 : ℕ) : ℝ) = 1 by norm_num,
    Real.rpow_one]

/-- Upper step of `W = ε s / (D G²)`: `s' ≤ G √(D s / ε)` gives `W' ≤ √W`. -/
theorem sqrt_step_up {ε D G s s' : ℝ} (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (h : s' ≤ G * Real.sqrt (D * s / ε)) :
    ε * s' / (D * G ^ 2) ≤ Real.sqrt (ε * s / (D * G ^ 2)) := by
  have hε' := hε.ne'
  have hD' := hD.ne'
  have hG' := hG.ne'
  have hkey : Real.sqrt (ε * s / (D * G ^ 2)) = ε / (D * G) * Real.sqrt (D * s / ε) := by
    rw [show ε * s / (D * G ^ 2) = (ε / (D * G)) ^ 2 * (D * s / ε) by field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hkey]
  calc ε * s' / (D * G ^ 2) ≤ ε * (G * Real.sqrt (D * s / ε)) / (D * G ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h hε.le) (by positivity)
    _ = ε / (D * G) * Real.sqrt (D * s / ε) := by field_simp

/-- Lower step of `W = b² ε s / δ`: `c √(δ s / ε) / 2 ≤ s'` and `b c ≥ 2` give `√W ≤ W'`. -/
theorem sqrt_step_low {ε δ b c s s' : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hb : 0 < b)
    (hbc : 2 ≤ b * c) (h : c * Real.sqrt (δ * s / ε) / 2 ≤ s') :
    Real.sqrt (b ^ 2 * ε * s / δ) ≤ b ^ 2 * ε * s' / δ := by
  have hε' := hε.ne'
  have hδ' := hδ.ne'
  have hkey : Real.sqrt (b ^ 2 * ε * s / δ) = b * ε / δ * Real.sqrt (δ * s / ε) := by
    rw [show b ^ 2 * ε * s / δ = (b * ε / δ) ^ 2 * (δ * s / ε) by field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hkey]
  have hz := Real.sqrt_nonneg (δ * s / ε)
  calc b * ε / δ * Real.sqrt (δ * s / ε) ≤ (b * c / 2) * (b * ε / δ * Real.sqrt (δ * s / ε)) :=
        le_mul_of_one_le_left (by positivity) (by linarith)
    _ = b ^ 2 * ε * (c * Real.sqrt (δ * s / ε) / 2) / δ := by field_simp
    _ ≤ b ^ 2 * ε * s' / δ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (by positivity)) hδ.le

/-- **Halving potential.**  If `ω_{j+1} ≤ ω_j / 2` and `ω_j > A > 0` before a stop, and
    `ω_0 ≤ B + A`, a stop occurs within `⌈log₂ (B / A + 1)⌉` steps. -/
theorem exists_stop_of_halving {ω : ℕ → ℝ} {S : ℕ → Prop} {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hstep : ∀ j, ¬ S j → ω (j + 1) ≤ ω j / 2) (hbig : ∀ j, ¬ S j → A < ω j)
    (h0 : ω 0 ≤ B + A) : ∃ j ≤ ⌈Real.logb 2 (B / A + 1)⌉₊, S j := by
  set J := ⌈Real.logb 2 (B / A + 1)⌉₊ with hJ
  have hx : 1 ≤ B / A + 1 := by have := div_nonneg hB hA.le; linarith
  have hpow : B / A + 1 ≤ 2 ^ J := by
    calc B / A + 1 = (2 : ℝ) ^ (Real.logb 2 (B / A + 1)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
      _ ≤ (2 : ℝ) ^ (J : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = 2 ^ J := Real.rpow_natCast 2 J
  by_contra hne
  push Not at hne
  have hind : ∀ j ≤ J, ω j ≤ ω 0 / 2 ^ j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := hstep j (hne j (by omega))
      have h2 := ih (by omega)
      calc ω (j + 1) ≤ ω j / 2 := h1
        _ ≤ ω 0 / 2 ^ j / 2 := by linarith
        _ = ω 0 / 2 ^ (j + 1) := by rw [pow_succ, div_div]
  have h1 := hind J le_rfl
  have h2 := hbig J (hne J le_rfl)
  have h3 : ω 0 / 2 ^ J ≤ A := by
    rw [div_le_iff₀ (by positivity)]
    have h4 := mul_le_mul_of_nonneg_left hpow hA.le
    rw [mul_add, mul_div_cancel₀ _ hA.ne', mul_one] at h4
    linarith
  linarith

section Run

variable {eps : ℝ} {p : ℕ → ℝ} {n : ℕ} {δ cN CN Cu C0 c1 c2 c3 KL : ℝ}

/-! ## The upper count -/

/-- **One curvature layer, upper count** (`lem:curv`(b)).  With `z = D s_ℓ / ε`: if `z ≤ 1`
    and `G ≤ 2 ε`, the next layer is one segment and `H ≤ ℓ + 2`; if `1 < z`, then
    `s_{ℓ+1} ≤ G √z`. -/
theorem curvUp_layer (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (heps : 1 ≤ eps) (hn : 1 ≤ n) (hCu : 0 < Cu) (hC0 : 0 ≤ C0) {G : ℝ}
    (hG : 2 * (Cu + C0) ≤ G) {ℓ : ℕ} (h2 : 2 ≤ reSize eps p n ℓ) (hC : UCurv eps p n δ ℓ) :
    (effDelta n δ * ((n : ℝ) / reDelta eps p n ℓ) / eps ≤ 1 → G ≤ 2 * eps →
        reHeight eps p n ≤ ℓ + 2) ∧
      (1 < effDelta n δ * ((n : ℝ) / reDelta eps p n ℓ) / eps →
        (n : ℝ) / reDelta eps p n (ℓ + 1) ≤
          G * Real.sqrt (effDelta n δ * ((n : ℝ) / reDelta eps p n ℓ) / eps)) := by
  have hM := hF.curvUp ℓ h2 hC
  have hs := div_reDelta_succ_le (p := p) heps hn ℓ
  have hN := (reSize_succ_bounds (p := p) heps hn ℓ).2
  set z := effDelta n δ * ((n : ℝ) / reDelta eps p n ℓ) / eps with hz
  have hsq0 := Real.sqrt_nonneg z
  constructor
  · intro hz1 hGε
    have hsq : Real.sqrt z ≤ 1 := Real.sqrt_le_one.2 hz1
    have h1 : Cu * Real.sqrt z ≤ Cu := mul_le_of_le_one_right hCu.le hsq
    have hN' : (reSize eps p n (ℓ + 1) : ℝ) ≤ 2 * eps := by
      have : (reSize eps p n (ℓ + 1) : ℝ) ≤ 2 * reSegs eps p n ℓ := by exact_mod_cast hN
      linarith
    exact reHeight_le_add_two heps hn hN'
  · intro hz1
    have hsq : 1 ≤ Real.sqrt z := Real.one_le_sqrt.2 hz1.le
    have h1 : C0 ≤ C0 * Real.sqrt z := le_mul_of_one_le_right hC0 hsq
    have h3 : 2 * (Cu + C0) * Real.sqrt z ≤ G * Real.sqrt z :=
      mul_le_mul_of_nonneg_right hG hsq0
    nlinarith

/-- **Curvature phase, upper bound** (Step 3).  From a curvature layer `m ≥ 1`, with
    `1 ≤ G`, `2 (C_u + C_0) ≤ G` and `G² ≤ ε`: `H ≤ m + log₂ (Y / log (ε / D) + 1) + 3`. -/
theorem reHeight_le_curvPhase (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (heps : 1 < eps) (hn : 1 ≤ n) (hδ1 : δ ≤ 1) (hCu : 0 < Cu) (hC0 : 0 ≤ C0) {G : ℝ}
    (hG1 : 1 ≤ G) (hG : 2 * (Cu + C0) ≤ G) (hGε : G ^ 2 ≤ eps) {m : ℕ} (hm1 : 1 ≤ m)
    (hmC : UCurv eps p n δ m) :
    (reHeight eps p n : ℝ) ≤
      m + Real.logb 2 (Real.log n / Real.log (eps / effDelta n δ) + 1) + 3 := by
  have hD0 : 0 < effDelta n δ := effDelta_pos' hn δ
  have hD1 : effDelta n δ ≤ 1 := effDelta_le_one' hn hδ1
  have hε0 : 0 < eps := by linarith
  have hlogε : 0 < Real.log eps := Real.log_pos heps
  have hA : Real.log eps ≤ Real.log (eps / effDelta n δ) := by
    rw [Real.log_div hε0.ne' hD0.ne']
    have := Real.log_nonpos hD0.le hD1
    linarith
  have hApos : 0 < Real.log (eps / effDelta n δ) := lt_of_lt_of_le hlogε hA
  have hGpos : 0 < G := by linarith
  have hlogG : 2 * Real.log G ≤ Real.log eps := by
    have := Real.log_le_log (by positivity) hGε
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hGeps : G ≤ 2 * eps := by nlinarith
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hY0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hs : ∀ ℓ, 0 < (n : ℝ) / reDelta eps p n ℓ := fun ℓ =>
    div_pos hN0 (reDelta_pos heps.le hn ℓ)
  have hW : ∀ ℓ, 0 < eps * ((n : ℝ) / reDelta eps p n ℓ) / (effDelta n δ * G ^ 2) :=
    fun ℓ => div_pos (mul_pos hε0 (hs ℓ)) (mul_pos hD0 (pow_pos hGpos 2))
  have hC : ∀ ℓ, m ≤ ℓ → UCurv eps p n δ ℓ := fun ℓ hℓ => hmC.mono heps.le hn hℓ
  have h2of : ∀ ℓ, reSize eps p n ℓ ≠ 1 → 2 ≤ reSize eps p n ℓ := fun ℓ h1 => by
    have := one_le_reSize (p := p) heps.le hn ℓ
    omega
  -- a stop: `N_ℓ = 1` or `z ≤ 1`
  have hstop : ∀ ℓ, m ≤ ℓ → (reSize eps p n ℓ = 1 ∨
      effDelta n δ * ((n : ℝ) / reDelta eps p n ℓ) / eps ≤ 1) → reHeight eps p n ≤ ℓ + 2 := by
    intro ℓ hℓ h
    by_cases h1 : reSize eps p n ℓ = 1
    · exact (reHeight_le (by omega) h1).trans (by omega)
    exact (curvUp_layer hF heps.le hn hCu hC0 hG (h2of ℓ h1) (hC ℓ hℓ)).1
      (h.resolve_left h1) hGeps
  obtain ⟨j, hj, hSj⟩ := exists_stop_of_halving
    (ω := fun j => Real.log (eps * ((n : ℝ) / reDelta eps p n (m + j)) / (effDelta n δ * G ^ 2)))
    (S := fun j => reSize eps p n (m + j) = 1 ∨
      effDelta n δ * ((n : ℝ) / reDelta eps p n (m + j)) / eps ≤ 1)
    hApos hY0 (fun j hSj => by
      show Real.log (eps * ((n : ℝ) / reDelta eps p n (m + j + 1)) / (effDelta n δ * G ^ 2)) ≤
        Real.log (eps * ((n : ℝ) / reDelta eps p n (m + j)) / (effDelta n δ * G ^ 2)) / 2
      push Not at hSj
      have hs' := (curvUp_layer hF heps.le hn hCu hC0 hG (h2of _ hSj.1)
        (hC (m + j) (by omega))).2 hSj.2
      have h1 := sqrt_step_up hε0 hD0 hGpos hs'
      calc Real.log (eps * ((n : ℝ) / reDelta eps p n (m + j + 1)) / (effDelta n δ * G ^ 2))
          ≤ Real.log (Real.sqrt (eps * ((n : ℝ) / reDelta eps p n (m + j)) /
              (effDelta n δ * G ^ 2))) := Real.log_le_log (hW _) h1
        _ = _ := Real.log_sqrt (hW _).le)
    (fun j hSj => by
      show Real.log (eps / effDelta n δ) <
        Real.log (eps * ((n : ℝ) / reDelta eps p n (m + j)) / (effDelta n δ * G ^ 2))
      push Not at hSj
      have hz := hSj.2
      set s := (n : ℝ) / reDelta eps p n (m + j) with hsdef
      have hsgt : eps / effDelta n δ < s := by
        rw [div_lt_iff₀ hD0]
        rw [one_lt_div hε0] at hz
        linarith
      have hWgt : (eps / effDelta n δ / G) ^ 2 < eps * s / (effDelta n δ * G ^ 2) := by
        rw [show (eps / effDelta n δ / G) ^ 2 = eps * (eps / effDelta n δ) /
          (effDelta n δ * G ^ 2) by field_simp]
        exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hsgt hε0)
          (mul_pos hD0 (pow_pos hGpos 2))
      have h1 := Real.log_lt_log (by positivity) hWgt
      rw [Real.log_pow, Real.log_div (by positivity) hGpos.ne'] at h1
      push_cast at h1
      linarith)
    (by
      show Real.log (eps * ((n : ℝ) / reDelta eps p n (m + 0)) / (effDelta n δ * G ^ 2)) ≤
        Real.log n + Real.log (eps / effDelta n δ)
      rw [Nat.add_zero]
      have h1 : (n : ℝ) / reDelta eps p n m ≤ n :=
        div_le_self hN0.le (by exact_mod_cast one_le_reDelta heps.le hn m)
      have h2 : eps * ((n : ℝ) / reDelta eps p n m) / (effDelta n δ * G ^ 2) ≤
          eps / effDelta n δ * n := by
        rw [div_le_iff₀ (mul_pos hD0 (pow_pos hGpos 2))]
        have hG2 : 1 ≤ G ^ 2 := one_le_pow₀ hG1
        have e : eps / effDelta n δ * n * (effDelta n δ * G ^ 2) = eps * n * G ^ 2 := by
          field_simp
        rw [e]
        calc eps * ((n : ℝ) / reDelta eps p n m) ≤ eps * n := mul_le_mul_of_nonneg_left h1 hε0.le
          _ = eps * n * 1 := by ring
          _ ≤ eps * n * G ^ 2 := mul_le_mul_of_nonneg_left hG2 (by positivity)
      have h3 := Real.log_le_log (hW m) h2
      rw [Real.log_mul (by positivity) hN0.ne'] at h3
      linarith)
  have hH := hstop (m + j) (by omega) hSj
  have hjJ : (j : ℝ) ≤ ⌈Real.logb 2 (Real.log n / Real.log (eps / effDelta n δ) + 1)⌉₊ := by
    exact_mod_cast hj
  have hlb : 0 ≤ Real.logb 2 (Real.log n / Real.log (eps / effDelta n δ) + 1) := by
    apply Real.logb_nonneg one_lt_two
    have := div_nonneg hY0 hApos.le
    linarith
  have hceil := Nat.ceil_lt_add_one hlb
  have hH' : (reHeight eps p n : ℝ) ≤ m + j + 2 := by exact_mod_cast hH
  linarith

/-! ## The lower count -/

/-- **One curvature layer, lower count** (`lem:curv`(a)).  For `δ = D > 0`, on a curvature
    layer with `Δ_ℓ ≥ Y²` and `s_ℓ ≥ K_L`, `c₅ √(δ s_ℓ / ε) ≤ M_{ℓ+1}` whenever
    `c₅ ≤ c₁, c₂, c₃`: the curvature condition makes the second and third entries at least
    `c₂ √(δ s / ε)` and `c₃ √(δ s / ε)`. -/
theorem curvLow_layer (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (heps : 1 ≤ eps) (hn : 1 ≤ n) (hY : 1 ≤ Real.log n) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : effDelta n δ = δ) {c₅ : ℝ} (hc₅ : 0 ≤ c₅) (h51 : c₅ ≤ c1) (h52 : c₅ ≤ c2)
    (h53 : c₅ ≤ c3) {ℓ : ℕ} (h2 : 2 ≤ reSize eps p n ℓ) (hC : UCurv eps p n δ ℓ)
    (hΔY : Real.log n ^ 2 ≤ (reDelta eps p n ℓ : ℝ)) (hKL : KL ≤ (n : ℝ) / reDelta eps p n ℓ) :
    c₅ * Real.sqrt (δ * ((n : ℝ) / reDelta eps p n ℓ) / eps) ≤ reSegs eps p n ℓ := by
  have hlow := hF.curvLow hδ0 ℓ h2 hΔY hKL
  have hs1 := one_lt_div_reDelta (p := p) heps hn h2
  unfold UCurv at hC
  rw [hD] at hC
  have hΔ := reDelta_pos (p := p) heps hn ℓ
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hε0 : 0 < eps := by linarith
  set Δ : ℝ := ((reDelta eps p n ℓ : ℕ) : ℝ) with hΔdef
  set s : ℝ := (n : ℝ) / Δ with hsdef
  set Y := Real.log n with hYdef
  set z : ℝ := δ * s / eps with hzdef
  have hY0 : 0 < Y := by linarith
  have hz0 : 0 ≤ z := by positivity
  have hzs : z ≤ s := by
    rw [hzdef, div_le_iff₀ hε0]
    have h := mul_le_mul_of_nonneg_right (show δ ≤ eps by linarith) (show 0 ≤ s by linarith)
    linarith
  -- `z³ ≤ δ⁴ n² / Y⁴` from the curvature condition
  have e : z ^ 3 * (eps ^ 3 * Δ ^ 3) = δ ^ 3 * (n : ℝ) ^ 3 := by
    rw [hzdef, hsdef]
    field_simp
  have hz3 : z ^ 3 ≤ δ ^ 4 * (n : ℝ) ^ 2 / Y ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hpos : 0 < eps ^ 3 * Δ ^ 3 := by positivity
    have hY2 : Y ^ 2 ≤ Y ^ 4 := pow_le_pow_right₀ hY (by norm_num)
    have h1 : z ^ 3 * Y ^ 4 * (eps ^ 3 * Δ ^ 3) ≤ δ ^ 4 * (n : ℝ) ^ 2 * (eps ^ 3 * Δ ^ 3) := by
      calc z ^ 3 * Y ^ 4 * (eps ^ 3 * Δ ^ 3) = δ ^ 3 * (n : ℝ) ^ 2 * (n * Y ^ 4) := by
            rw [show z ^ 3 * Y ^ 4 * (eps ^ 3 * Δ ^ 3) = z ^ 3 * (eps ^ 3 * Δ ^ 3) * Y ^ 4 by
              ring, e]
            ring
        _ ≤ δ ^ 3 * (n : ℝ) ^ 2 * (δ * eps ^ 3 * Δ ^ 3) :=
            mul_le_mul_of_nonneg_left hC (by positivity)
        _ = δ ^ 4 * (n : ℝ) ^ 2 * (eps ^ 3 * Δ ^ 3) := by ring
    have h4 := le_of_mul_le_mul_right h1 hpos
    calc z ^ 3 * Y ^ 2 ≤ z ^ 3 * Y ^ 4 := mul_le_mul_of_nonneg_left hY2 (by positivity)
      _ ≤ δ ^ 4 * (n : ℝ) ^ 2 := h4
  -- the second entry
  have hT0 : 0 ≤ δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ) := by positivity
  have hT3 : (δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ)) ^ 3 = δ ^ 2 * ((n : ℝ) / Y) := by
    rw [mul_pow, rpow_two_thirds_pow_three hδ0.le, rpow_one_third_pow_three (by positivity)]
  have hsqT : Real.sqrt z ≤ δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) hT0
    calc Real.sqrt z ^ 6 = (Real.sqrt z ^ 2) ^ 3 := by ring
      _ = z ^ 3 := by rw [Real.sq_sqrt hz0]
      _ ≤ δ ^ 4 * (n : ℝ) ^ 2 / Y ^ 2 := hz3
      _ = ((δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ)) ^ 3) ^ 2 := by
          rw [hT3]; field_simp
      _ = (δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ)) ^ 6 := by ring
  -- the third entry
  have hsqs : Real.sqrt z ≤ s := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hsq0 := Real.sqrt_nonneg z
  refine le_trans (le_min (le_min ?_ ?_) ?_) hlow
  · exact mul_le_mul_of_nonneg_right h51 hsq0
  · calc c₅ * Real.sqrt z ≤ c2 * Real.sqrt z := mul_le_mul_of_nonneg_right h52 hsq0
      _ ≤ c2 * (δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqT (by linarith)
      _ = c2 * δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ) := by ring
  · calc c₅ * Real.sqrt z ≤ c3 * Real.sqrt z := mul_le_mul_of_nonneg_right h53 hsq0
      _ ≤ c3 * s := mul_le_mul_of_nonneg_left hsqs (by linarith)

/-- **Curvature phase, lower bound** (Step 4).  For `δ = D > 0`, from a nontrivial curvature
    layer `m ≥ 1` with `Δ_m ≥ Y²` and `s_m⁴ ≥ n`, and constants with `c₅ ≤ c₁, c₂, c₃`,
    `0 < K_L ≤ K₂`, `16 ≤ c₅² K₂`, `1 ≤ b`, `2 ≤ b c₅`, `b² K₂ ≤ ε`:
    `m + 1 + log₂ (Y / log (ε / δ)) - 4 < H`. -/
theorem lt_reHeight_curvPhase (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (heps : 1 < eps) (hn2 : 2 ≤ n) (hY : 1 ≤ Real.log n) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : effDelta n δ = δ) (hKL : 0 < KL) {c₅ K₂ b : ℝ} (hc₅ : 0 < c₅) (h51 : c₅ ≤ c1)
    (h52 : c₅ ≤ c2) (h53 : c₅ ≤ c3) (hK₂ : KL ≤ K₂) (hK₂' : 16 ≤ c₅ ^ 2 * K₂) (hb : 1 ≤ b)
    (hbc : 2 ≤ b * c₅) (hbK : b ^ 2 * K₂ ≤ eps) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : 2 ≤ reSize eps p n m)
    (hmC : UCurv eps p n δ m) (hmY : Real.log n ^ 2 ≤ (reDelta eps p n m : ℝ))
    (hms : (n : ℝ) ≤ ((n : ℝ) / reDelta eps p n m) ^ 4) :
    (m : ℝ) + 1 + Real.logb 2 (Real.log n / Real.log (eps / δ)) - 4 < reHeight eps p n := by
  have hn : 1 ≤ n := by omega
  have hε0 : 0 < eps := by linarith
  have hlogε : 0 < Real.log eps := Real.log_pos heps
  have hA : Real.log eps ≤ Real.log (eps / δ) := by
    rw [Real.log_div hε0.ne' hδ0.ne']
    have := Real.log_nonpos hδ0.le hδ1
    linarith
  have hApos : 0 < Real.log (eps / δ) := lt_of_lt_of_le hlogε hA
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hY0 : 0 < Real.log n := by linarith
  have hK₂0 : 0 < K₂ := hKL.trans_le hK₂
  have hb0 : 0 < b := by linarith
  have hs : ∀ ℓ, 0 < (n : ℝ) / reDelta eps p n ℓ := fun ℓ =>
    div_pos hN0 (reDelta_pos heps.le hn ℓ)
  have hW : ∀ ℓ, 0 < b ^ 2 * eps * ((n : ℝ) / reDelta eps p n ℓ) / δ := fun ℓ =>
    div_pos (mul_pos (mul_pos (pow_pos hb0 2) hε0) (hs ℓ)) hδ0
  -- one step while `δ s / ε ≥ K₂`
  have hstep : ∀ ℓ, m ≤ ℓ → 2 ≤ reSize eps p n ℓ →
      K₂ ≤ δ * ((n : ℝ) / reDelta eps p n ℓ) / eps →
      2 ≤ reSize eps p n (ℓ + 1) ∧
        Real.log (b ^ 2 * eps * ((n : ℝ) / reDelta eps p n ℓ) / δ) / 2 ≤
          Real.log (b ^ 2 * eps * ((n : ℝ) / reDelta eps p n (ℓ + 1)) / δ) := by
    intro ℓ hℓ h2 hz
    have hzs : δ * ((n : ℝ) / reDelta eps p n ℓ) / eps ≤ (n : ℝ) / reDelta eps p n ℓ := by
      rw [div_le_iff₀ hε0]
      have h := mul_le_mul_of_nonneg_right (show δ ≤ eps by linarith) (hs ℓ).le
      linarith
    have hM := curvLow_layer hF heps.le hn hY hδ0 hδ1 hD hc₅.le h51 h52 h53 h2
      (hmC.mono heps.le hn hℓ) (hmY.trans (reDelta_le_of_le heps.le hn hℓ))
      (by linarith)
    set z := δ * ((n : ℝ) / reDelta eps p n ℓ) / eps with hzdef
    have hz0 : 0 ≤ z := by linarith
    have h4 : 4 ≤ c₅ * Real.sqrt z := by
      apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity)
      rw [mul_pow, Real.sq_sqrt hz0]
      nlinarith
    have hM4 : (4 : ℝ) ≤ reSegs eps p n ℓ := h4.trans hM
    have hN1 := (reSize_succ_bounds (p := p) heps.le hn ℓ).1
    have hM2 : 2 ≤ reSegs eps p n ℓ := by
      exact_mod_cast (show (2 : ℝ) ≤ (reSegs eps p n ℓ : ℝ) by linarith)
    refine ⟨le_trans hM2 hN1, ?_⟩
    have hs' := reSegs_sub_one_lt (p := p) heps.le hn ℓ
    have hs'' : c₅ * Real.sqrt z / 2 ≤ (n : ℝ) / reDelta eps p n (ℓ + 1) := by linarith
    have h1 := sqrt_step_low hε0 hδ0 hb0 hbc hs''
    calc Real.log (b ^ 2 * eps * ((n : ℝ) / reDelta eps p n ℓ) / δ) / 2
        = Real.log (Real.sqrt (b ^ 2 * eps * ((n : ℝ) / reDelta eps p n ℓ) / δ)) :=
          (Real.log_sqrt (hW ℓ).le).symm
      _ ≤ _ := Real.log_le_log (Real.sqrt_pos.2 (hW ℓ)) h1
  -- a stop: `log W < 3 A`
  have hstop : ∀ ℓ, ¬ K₂ ≤ δ * ((n : ℝ) / reDelta eps p n ℓ) / eps →
      Real.log (b ^ 2 * eps * ((n : ℝ) / reDelta eps p n ℓ) / δ) < 3 * Real.log (eps / δ) := by
    intro ℓ hz
    push Not at hz
    have hslt : (n : ℝ) / reDelta eps p n ℓ < K₂ * eps / δ := by
      rw [div_lt_iff₀ hε0] at hz
      rw [lt_div_iff₀ hδ0]
      linarith
    have hWlt : b ^ 2 * eps * ((n : ℝ) / reDelta eps p n ℓ) / δ < b ^ 2 * K₂ * (eps / δ) ^ 2 := by
      rw [show b ^ 2 * K₂ * (eps / δ) ^ 2 = b ^ 2 * eps * (K₂ * eps / δ) / δ by
        field_simp]
      exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hslt (by positivity)) hδ0
    have h1 := Real.log_lt_log (hW ℓ) hWlt
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    have h2 := Real.log_le_log (by positivity) hbK
    push_cast at h1
    linarith
  -- the initial potential is at least `Y / 4`
  have hW0 : Real.log n / 4 ≤ Real.log (b ^ 2 * eps * ((n : ℝ) / reDelta eps p n m) / δ) := by
    have h1 : (n : ℝ) / reDelta eps p n m ≤ b ^ 2 * eps * ((n : ℝ) / reDelta eps p n m) / δ := by
      rw [le_div_iff₀ hδ0]
      have hb2 : 1 ≤ b ^ 2 := one_le_pow₀ hb
      have hbe : δ ≤ b ^ 2 * eps := by nlinarith
      nlinarith [hs m]
    have h2 := Real.log_le_log (hs m) h1
    have h3 := Real.log_le_log hN0 hms
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  -- the first stop exists
  have hex : ∃ j, ¬ K₂ ≤ δ * ((n : ℝ) / reDelta eps p n (m + j)) / eps := by
    by_contra hne
    push Not at hne
    have hall : ∀ j, 2 ≤ reSize eps p n (m + j) := by
      intro j
      induction j with
      | zero => simpa using hm2
      | succ j ih => exact (hstep (m + j) (by omega) ih (hne j)).1
    have h1 := hall (reHeight eps p n)
    rw [reSize_eq_one_of_reHeight_le heps.le hn (by omega)] at h1
    omega
  classical
  set J := Nat.find hex with hJ
  have hJs : ¬ K₂ ≤ δ * ((n : ℝ) / reDelta eps p n (m + J)) / eps := Nat.find_spec hex
  have hind : ∀ j ≤ J, 2 ≤ reSize eps p n (m + j) ∧
      Real.log (b ^ 2 * eps * ((n : ℝ) / reDelta eps p n m) / δ) / 2 ^ j ≤
        Real.log (b ^ 2 * eps * ((n : ℝ) / reDelta eps p n (m + j)) / δ) := by
    intro j
    induction j with
    | zero => intro _; simpa using hm2
    | succ j ih =>
      intro hj
      obtain ⟨h2, h3⟩ := ih (by omega)
      have hcont : K₂ ≤ δ * ((n : ℝ) / reDelta eps p n (m + j)) / eps := by
        have := Nat.find_min hex (show j < J by omega)
        push Not at this
        exact this
      obtain ⟨h4, h5⟩ := hstep (m + j) (by omega) h2 hcont
      refine ⟨h4, ?_⟩
      calc Real.log (b ^ 2 * eps * ((n : ℝ) / reDelta eps p n m) / δ) / 2 ^ (j + 1)
          = Real.log (b ^ 2 * eps * ((n : ℝ) / reDelta eps p n m) / δ) / 2 ^ j / 2 := by
            rw [pow_succ (2 : ℝ) j, div_div]
        _ ≤ Real.log (b ^ 2 * eps * ((n : ℝ) / reDelta eps p n (m + j)) / δ) / 2 := by
            linarith
        _ ≤ _ := h5
  obtain ⟨hJ2, hJW⟩ := hind J le_rfl
  have hJlt := hstop (m + J) hJs
  have hHJ : m + J < reHeight eps p n := (lt_reHeight_iff heps.le hn (by omega)).2 hJ2
  have hratio : Real.log n / Real.log (eps / δ) < 12 * 2 ^ J := by
    rw [div_lt_iff₀ hApos]
    have h1 : Real.log n / 4 / 2 ^ J < 3 * Real.log (eps / δ) := by
      have : Real.log n / 4 / 2 ^ J ≤
          Real.log (b ^ 2 * eps * ((n : ℝ) / reDelta eps p n m) / δ) / 2 ^ J :=
        div_le_div_of_nonneg_right hW0 (by positivity)
      linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith
  have hlog := logb_lt_add_four (div_pos hY0 hApos) hratio
  have hHJ' : (m : ℝ) + J + 1 ≤ reHeight eps p n := by exact_mod_cast hHJ
  linarith

/-! ## Band layers and the end of the noise phase -/

/-- **Band layers are nonterminal** (Step 4).  For `δ = D > 0` with `δ¹⁶ n > 1`, a nontrivial
    layer with `Δ_ℓ ≥ Y²` that is not curvature-dominated has `M_{ℓ+1} ≥ 2` and
    `(M_{ℓ+1} - 1)⁴ ≥ n`: all three entries of `lem:curv`(a) are at least `2 n^{1/4}`. -/
theorem band_layer_segs (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (heps : 1 ≤ eps) (hn : 1 ≤ n) (hY : 1 ≤ Real.log n) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : effDelta n δ = δ) (hδn : 1 < δ ^ 16 * n) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hc3 : 0 < c3) (hKLn : KL ^ 12 * Real.log n ^ 16 ≤ (n : ℝ) ^ 7)
    (h1n : 16 ^ 6 * Real.log n ^ 16 ≤ c1 ^ 24 * n) (h2n : 16 ^ 6 * Real.log n ^ 8 ≤ c2 ^ 24 * n)
    (h3n : 4096 * Real.log n ^ 16 ≤ c3 ^ 12 * (n : ℝ) ^ 4) {ℓ : ℕ}
    (h2 : 2 ≤ reSize eps p n ℓ) (hnC : ¬ UCurv eps p n δ ℓ)
    (hΔY : Real.log n ^ 2 ≤ (reDelta eps p n ℓ : ℝ)) :
    2 ≤ reSegs eps p n ℓ ∧ (n : ℝ) ≤ ((reSegs eps p n ℓ : ℝ) - 1) ^ 4 := by
  unfold UCurv at hnC
  rw [hD, not_le] at hnC
  have hΔ := reDelta_pos (p := p) heps hn ℓ
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hε0 : 0 < eps := by linarith
  have hY0 : 0 < Real.log n := by linarith
  set Δ : ℝ := ((reDelta eps p n ℓ : ℕ) : ℝ) with hΔdef
  set s : ℝ := (n : ℝ) / Δ with hsdef
  set Y := Real.log n with hYdef
  set z : ℝ := δ * s / eps with hzdef
  have hs0 : 0 < s := div_pos hN0 hΔ
  have hz0 : 0 ≤ z := by positivity
  have hzs : z ≤ s := by
    rw [hzdef, div_le_iff₀ hε0]
    have h := mul_le_mul_of_nonneg_right (show δ ≤ eps by linarith) hs0.le
    linarith
  -- `z³ > δ⁴ n² / Y⁴` and `z¹² > n⁷ / Y¹⁶`
  have e : z ^ 3 * (eps ^ 3 * Δ ^ 3) = δ ^ 3 * (n : ℝ) ^ 3 := by
    rw [hzdef, hsdef]
    field_simp
  have hz3 : δ ^ 4 * (n : ℝ) ^ 2 / Y ^ 4 < z ^ 3 := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : δ ^ 4 * (n : ℝ) ^ 2 * (eps ^ 3 * Δ ^ 3) < z ^ 3 * Y ^ 4 * (eps ^ 3 * Δ ^ 3) := by
      calc δ ^ 4 * (n : ℝ) ^ 2 * (eps ^ 3 * Δ ^ 3) =
            δ ^ 3 * (n : ℝ) ^ 2 * (δ * eps ^ 3 * Δ ^ 3) := by ring
        _ < δ ^ 3 * (n : ℝ) ^ 2 * (n * Y ^ 4) := mul_lt_mul_of_pos_left hnC (by positivity)
        _ = z ^ 3 * Y ^ 4 * (eps ^ 3 * Δ ^ 3) := by
            rw [show z ^ 3 * Y ^ 4 * (eps ^ 3 * Δ ^ 3) = z ^ 3 * (eps ^ 3 * Δ ^ 3) * Y ^ 4 by
              ring, e]
            ring
    exact lt_of_mul_lt_mul_right h1 (by positivity)
  have hz12 : (n : ℝ) ^ 7 / Y ^ 16 < z ^ 12 := by
    have h1 : (δ ^ 4 * (n : ℝ) ^ 2 / Y ^ 4) ^ 4 < (z ^ 3) ^ 4 :=
      pow_lt_pow_left₀ hz3 (by positivity) (by norm_num)
    have h2 : (n : ℝ) ^ 7 < δ ^ 16 * (n : ℝ) ^ 8 := by
      have := mul_lt_mul_of_pos_right hδn (pow_pos hN0 7)
      calc (n : ℝ) ^ 7 = 1 * (n : ℝ) ^ 7 := by ring
        _ < δ ^ 16 * n * (n : ℝ) ^ 7 := this
        _ = δ ^ 16 * (n : ℝ) ^ 8 := by ring
    calc (n : ℝ) ^ 7 / Y ^ 16 < δ ^ 16 * (n : ℝ) ^ 8 / Y ^ 16 :=
          div_lt_div_of_pos_right h2 (by positivity)
      _ = (δ ^ 4 * (n : ℝ) ^ 2 / Y ^ 4) ^ 4 := by ring
      _ < (z ^ 3) ^ 4 := h1
      _ = z ^ 12 := by ring
  have hKL' : KL ≤ s := by
    have h1 : KL ^ 12 ≤ (n : ℝ) ^ 7 / Y ^ 16 := by rw [le_div_iff₀ (by positivity)]; exact hKLn
    exact (lt_of_pow_lt_pow_left₀ 12 hz0 (h1.trans_lt hz12)).le.trans hzs
  have hlow : min (min (c1 * Real.sqrt z) (c2 * δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ)))
      (c3 * s) ≤ reSegs eps p n ℓ := hF.curvLow hδ0 ℓ h2 hΔY hKL'
  -- every entry `E` has `16 n ≤ E⁴`
  have hE1 : 16 * (n : ℝ) ≤ (c1 * Real.sqrt z) ^ 4 := by
    have e1 : (c1 * Real.sqrt z) ^ 4 = c1 ^ 4 * z ^ 2 := by
      rw [mul_pow, show Real.sqrt z ^ 4 = (Real.sqrt z ^ 2) ^ 2 by ring, Real.sq_sqrt hz0]
    rw [e1]
    apply le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (by positivity)
    have h1 : (16 * (n : ℝ)) ^ 6 ≤ c1 ^ 24 * ((n : ℝ) ^ 7 / Y ^ 16) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right h1n (pow_nonneg hN0.le 6)
      calc (16 * (n : ℝ)) ^ 6 * Y ^ 16 = 16 ^ 6 * Y ^ 16 * (n : ℝ) ^ 6 := by ring
        _ ≤ c1 ^ 24 * n * (n : ℝ) ^ 6 := this
        _ = c1 ^ 24 * (n : ℝ) ^ 7 := by ring
    calc (16 * (n : ℝ)) ^ 6 ≤ c1 ^ 24 * ((n : ℝ) ^ 7 / Y ^ 16) := h1
      _ ≤ c1 ^ 24 * z ^ 12 := mul_le_mul_of_nonneg_left hz12.le (by positivity)
      _ = (c1 ^ 4 * z ^ 2) ^ 6 := by ring
  have hE2 : 16 * (n : ℝ) ≤ (c2 * δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ)) ^ 4 := by
    have hT3 : (c2 * δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ)) ^ 3 =
        c2 ^ 3 * (δ ^ 2 * ((n : ℝ) / Y)) := by
      rw [mul_pow, mul_pow, rpow_two_thirds_pow_three hδ0.le,
        rpow_one_third_pow_three (by positivity)]
      ring
    apply le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (by positivity)
    have h1 : (16 * (n : ℝ)) ^ 6 ≤ c2 ^ 24 * ((n : ℝ) ^ 7 / Y ^ 8) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right h2n (pow_nonneg hN0.le 6)
      calc (16 * (n : ℝ)) ^ 6 * Y ^ 8 = 16 ^ 6 * Y ^ 8 * (n : ℝ) ^ 6 := by ring
        _ ≤ c2 ^ 24 * n * (n : ℝ) ^ 6 := this
        _ = c2 ^ 24 * (n : ℝ) ^ 7 := by ring
    have h2 : (n : ℝ) ^ 7 ≤ δ ^ 16 * (n : ℝ) ^ 8 := by
      have := mul_le_mul_of_nonneg_right hδn.le (pow_nonneg hN0.le 7)
      calc (n : ℝ) ^ 7 = 1 * (n : ℝ) ^ 7 := by ring
        _ ≤ δ ^ 16 * n * (n : ℝ) ^ 7 := this
        _ = δ ^ 16 * (n : ℝ) ^ 8 := by ring
    calc (16 * (n : ℝ)) ^ 6 ≤ c2 ^ 24 * ((n : ℝ) ^ 7 / Y ^ 8) := h1
      _ ≤ c2 ^ 24 * (δ ^ 16 * (n : ℝ) ^ 8 / Y ^ 8) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 (by positivity))
            (by positivity)
      _ = ((c2 * δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ)) ^ 3) ^ 8 := by
          rw [hT3]; field_simp
      _ = ((c2 * δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ)) ^ 4) ^ 6 := by ring
  have hE3 : 16 * (n : ℝ) ≤ (c3 * s) ^ 4 := by
    have h1 : 16 * (n : ℝ) ≤ (c3 * z) ^ 4 := by
      apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
      have h2 : (16 * (n : ℝ)) ^ 3 ≤ c3 ^ 12 * ((n : ℝ) ^ 7 / Y ^ 16) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_right h3n (pow_nonneg hN0.le 3)
        calc (16 * (n : ℝ)) ^ 3 * Y ^ 16 = 4096 * Y ^ 16 * (n : ℝ) ^ 3 := by ring
          _ ≤ c3 ^ 12 * (n : ℝ) ^ 4 * (n : ℝ) ^ 3 := this
          _ = c3 ^ 12 * (n : ℝ) ^ 7 := by ring
      calc (16 * (n : ℝ)) ^ 3 ≤ c3 ^ 12 * ((n : ℝ) ^ 7 / Y ^ 16) := h2
        _ ≤ c3 ^ 12 * z ^ 12 := mul_le_mul_of_nonneg_left hz12.le (by positivity)
        _ = ((c3 * z) ^ 4) ^ 3 := by ring
    exact h1.trans (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left hzs hc3.le) 4)
  set E := min (min (c1 * Real.sqrt z) (c2 * δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ)))
    (c3 * s) with hEdef
  have hE0 : 0 ≤ E := le_min (le_min (by positivity) (by positivity)) (by positivity)
  have hE4 : 16 * (n : ℝ) ≤ E ^ 4 := by
    rcases min_choice (min (c1 * Real.sqrt z)
      (c2 * δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ))) (c3 * s) with h | h
    · rw [hEdef, h]
      rcases min_choice (c1 * Real.sqrt z)
        (c2 * δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Y) ^ (1 / 3 : ℝ)) with h' | h'
      · rw [h']; exact hE1
      · rw [h']; exact hE2
    · rw [hEdef, h]; exact hE3
  have hE2' : 2 ≤ E := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hE0
    linarith
  have hM2 : (2 : ℝ) ≤ reSegs eps p n ℓ := hE2'.trans hlow
  refine ⟨by exact_mod_cast hM2, ?_⟩
  have h1 : E / 2 ≤ (reSegs eps p n ℓ : ℝ) - 1 := by linarith
  calc (n : ℝ) ≤ E ^ 4 / 16 := by linarith
    _ = (E / 2) ^ 4 := by ring
    _ ≤ ((reSegs eps p n ℓ : ℝ) - 1) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4

/-- **Size after the noise phase** (Step 4, case `ℓ₂ = p`).  For `δ = D > 0` with `δ¹⁶ n > 1`
    and `C_N²⁴ ≤ n`, the first non-noise layer has `s_p⁴ ≥ n`: the last noise layer has
    `δ ε³ Δ³ ≤ n / Y⁴` and `Δ_p ≤ C_N ε² Δ²`. -/
theorem le_div_reDelta_uEnd_pow (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (hCN : 0 < CN) (heps : 1 ≤ eps) (hn : 1 ≤ n) (hY : 1 ≤ Real.log n) (hδ0 : 0 < δ)
    (hD : effDelta n δ = δ) (hδn : 1 < δ ^ 16 * n) (hCNn : CN ^ 24 ≤ n)
    (hP1 : 1 ≤ uEnd eps p n δ) :
    (n : ℝ) ≤ ((n : ℝ) / reDelta eps p n (uEnd eps p n δ)) ^ 4 := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, uEnd eps p n δ = ℓ + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hP1).symm⟩
  have hN := UNoise_of_lt_uEnd (p := p) (δ := δ) (show ℓ < uEnd eps p n δ by omega)
  have hup := (hF.noise ℓ hN.1 hN.2.1 hN.2.2).2.1
  have hc := hN.2.1
  rw [hD] at hc
  rw [hℓ]
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hε0 : 0 ≤ eps := by linarith
  have ha0 := (reDelta_pos (p := p) heps hn ℓ).le
  have hb0 := reDelta_pos (p := p) heps hn (ℓ + 1)
  set a : ℝ := ((reDelta eps p n ℓ : ℕ) : ℝ) with hadef
  set b : ℝ := ((reDelta eps p n (ℓ + 1) : ℕ) : ℝ) with hbdef
  have h1 : eps ^ 3 * a ^ 3 ≤ n / δ := by
    rw [le_div_iff₀ hδ0]
    have h2 : (n : ℝ) / Real.log n ^ 4 ≤ n := div_le_self hN0.le (one_le_pow₀ hY)
    nlinarith
  have h2 : b ^ 12 ≤ CN ^ 12 * ((n : ℝ) / δ) ^ 8 := by
    calc b ^ 12 ≤ (CN * eps ^ 2 * a ^ 2) ^ 12 := pow_le_pow_left₀ hb0.le hup 12
      _ = CN ^ 12 * (eps ^ 3 * a ^ 3) ^ 8 := by ring
      _ ≤ CN ^ 12 * ((n : ℝ) / δ) ^ 8 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 8) (by positivity)
  have h3 : CN ^ 12 < δ ^ 8 * n := by
    apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
    have := mul_lt_mul_of_pos_right hδn hN0
    calc (CN ^ 12) ^ 2 = CN ^ 24 := by ring
      _ ≤ (n : ℝ) := hCNn
      _ = 1 * (n : ℝ) := by ring
      _ < δ ^ 16 * n * n := this
      _ = (δ ^ 8 * n) ^ 2 := by ring
  have h4 : CN ^ 12 * ((n : ℝ) / δ) ^ 8 ≤ (n : ℝ) ^ 9 := by
    rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
    calc CN ^ 12 * (n : ℝ) ^ 8 ≤ δ ^ 8 * n * (n : ℝ) ^ 8 :=
          mul_le_mul_of_nonneg_right h3.le (by positivity)
      _ = (n : ℝ) ^ 9 * δ ^ 8 := by ring
  have h5 : b ^ 4 ≤ (n : ℝ) ^ 3 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
    calc (b ^ 4) ^ 3 = b ^ 12 := by ring
      _ ≤ (n : ℝ) ^ 9 := h2.trans h4
      _ = ((n : ℝ) ^ 3) ^ 3 := by ring
  rw [div_pow, le_div_iff₀ (by positivity)]
  calc (n : ℝ) * b ^ 4 ≤ n * (n : ℝ) ^ 3 := mul_le_mul_of_nonneg_left h5 hN0.le
    _ = (n : ℝ) ^ 4 := by ring

end Run

end

end PGM
