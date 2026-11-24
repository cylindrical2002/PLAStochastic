import PLAStochastic.Index.GRE.PreciseHeightDefs

/-!
# Layer phases of the uniform two-phase height

Deterministic preliminaries of `PLAStochastic.Index.KRE.Uniform.HeightRecursion` (Section 4 of `thm:uniform`,
`research/2026-09-24-re-curvature-uniform/tex/main.tex`).  Notation: `Y = log n`,
`D = effDelta n δ`, `s_ℓ = n / Δ_ℓ`.

* Lattice facts in real form: `s_ℓ ≤ N_ℓ < s_ℓ + 1`, `M_{ℓ+1} - 1 < s_{ℓ+1} ≤ 2 M_{ℓ+1}`, and
  a layer of at most `2 ε + 1` keys is one segment (the constant line), so
  `N_{ℓ+1} ≤ 2 ε` gives `H ≤ ℓ + 2`.
* The phases: `UNoise` (`𝖭`) and the curvature condition `UCurv` (`𝖢` when `N_ℓ ≥ 2`); the
  first non-noise layer `uEnd` (TeX `p`) and the first layer from `p` on that is a singleton or
  curvature-dominated, `uCurvStart` (TeX `ℓ₂`).  The layers in between are band layers.
* The noise phase: the doubling bracket `(c_N ε²)^(2^ℓ - 1) ≤ Δ_ℓ ≤ (C_N ε²)^(2^ℓ - 1)` for
  `ℓ ≤ p`, `n < Δ_p⁴`, `log₂ (Y / log ε) - 4 < p ≤ log₂ (Y / log ε) + 1`, and at most three
  band layers: `uCurvStart ≤ uEnd + 3`.

Nothing here is probabilistic.
-/

namespace PGM

noncomputable section

section Run

variable {eps : ℝ} {p : ℕ → ℝ} {n : ℕ}

/-! ## Lattice facts -/

/-- A list of `K ≤ 2 eps + 1` keys is one ALG-OPT segment: the constant line `eps` fits it. -/
theorem finSegCount_eq_one_of_small {P : ℕ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (h : (K : ℝ) - 1 ≤ 2 * eps) : finSegCount eps P K = 1 := by
  refine le_antisymm ?_ (one_le_finSegCount P hK)
  refine finSegCount_le_of_partition (m := 1) (c := fun i => i * K) ⟨by simp, by simp, ?_, ?_⟩
  · intro i hi
    obtain rfl : i = 0 := by omega
    simp only [zero_mul, zero_add, one_mul]
    omega
  · intro i hi
    obtain rfl : i = 0 := by omega
    show prefixAffineFeasible eps (shiftSeq P (0 * K)) ((0 + 1) * K - 0 * K)
    refine ⟨0, eps, fun j hj => ?_⟩
    simp only [zero_mul, zero_add, one_mul, Nat.sub_zero] at hj ⊢
    exact constantLine_covers_of_bound h j hj

/-- `M_{ℓ+1} = 1` makes layer `ℓ + 1` a singleton. -/
theorem reSize_succ_eq_one_of_reSegs (heps : 1 ≤ eps) (hn : 1 ≤ n) {ℓ : ℕ}
    (h : reSegs eps p n ℓ = 1) : reSize eps p n (ℓ + 1) = 1 := by
  have h1 := one_le_reSize (p := p) heps hn ℓ
  rw [reSize_succ, reStep, h, Nat.div_one, Nat.ceilDiv_eq_add_pred_div]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- If `N_{ℓ+1} ≤ 2 eps`, layer `ℓ + 1` is one segment, so `H ≤ ℓ + 2`. -/
theorem reHeight_le_add_two (heps : 1 ≤ eps) (hn : 1 ≤ n) {ℓ : ℕ}
    (h : (reSize eps p n (ℓ + 1) : ℝ) ≤ 2 * eps) : reHeight eps p n ≤ ℓ + 2 := by
  have h1 := one_le_reSize (p := p) heps hn (ℓ + 1)
  have hM : reSegs eps p n (ℓ + 1) = 1 := finSegCount_eq_one_of_small h1 (by linarith)
  exact reHeight_le (by omega) (reSize_succ_eq_one_of_reSegs heps hn hM)

theorem reDelta_pos (heps : 1 ≤ eps) (hn : 1 ≤ n) (ℓ : ℕ) : (0 : ℝ) < reDelta eps p n ℓ := by
  exact_mod_cast one_le_reDelta heps hn ℓ

/-- `s_ℓ ≤ N_ℓ`. -/
theorem div_reDelta_le_reSize (heps : 1 ≤ eps) (hn : 1 ≤ n) (ℓ : ℕ) :
    (n : ℝ) / reDelta eps p n ℓ ≤ reSize eps p n ℓ := by
  rw [div_le_iff₀ (reDelta_pos heps hn ℓ)]
  exact_mod_cast (re_cover heps hn ℓ).2

/-- `N_ℓ - 1 < s_ℓ`. -/
theorem reSize_sub_one_lt_div (heps : 1 ≤ eps) (hn : 1 ≤ n) (ℓ : ℕ) :
    (reSize eps p n ℓ : ℝ) - 1 < n / reDelta eps p n ℓ := by
  have h1 := one_le_reSize (p := p) heps hn ℓ
  have h2 : ((reSize eps p n ℓ - 1 : ℕ) : ℝ) * reDelta eps p n ℓ < n := by
    exact_mod_cast (re_cover heps hn ℓ).1
  rw [Nat.cast_sub h1, Nat.cast_one] at h2
  rw [lt_div_iff₀ (reDelta_pos heps hn ℓ)]
  exact h2

/-- `s_{ℓ+1} ≤ 2 M_{ℓ+1}`. -/
theorem div_reDelta_succ_le (heps : 1 ≤ eps) (hn : 1 ≤ n) (ℓ : ℕ) :
    (n : ℝ) / reDelta eps p n (ℓ + 1) ≤ 2 * reSegs eps p n ℓ := by
  have h1 := div_reDelta_le_reSize (p := p) heps hn (ℓ + 1)
  have h2 : (reSize eps p n (ℓ + 1) : ℝ) ≤ 2 * reSegs eps p n ℓ := by
    exact_mod_cast (reSize_succ_bounds heps hn ℓ).2
  linarith

/-- `M_{ℓ+1} - 1 < s_{ℓ+1}`. -/
theorem reSegs_sub_one_lt (heps : 1 ≤ eps) (hn : 1 ≤ n) (ℓ : ℕ) :
    (reSegs eps p n ℓ : ℝ) - 1 < n / reDelta eps p n (ℓ + 1) := by
  have h1 := reSize_sub_one_lt_div (p := p) heps hn (ℓ + 1)
  have h2 : (reSegs eps p n ℓ : ℝ) ≤ reSize eps p n (ℓ + 1) := by
    exact_mod_cast (reSize_succ_bounds heps hn ℓ).1
  linarith

/-- On a nontrivial layer `1 < s_ℓ`. -/
theorem one_lt_div_reDelta (heps : 1 ≤ eps) (hn : 1 ≤ n) {ℓ : ℕ}
    (h2 : 2 ≤ reSize eps p n ℓ) : 1 < (n : ℝ) / reDelta eps p n ℓ := by
  rw [one_lt_div (reDelta_pos heps hn ℓ)]
  exact_mod_cast reDelta_lt heps hn h2

/-! ## The effective curvature size -/

theorem effDelta_pos' (hn : 1 ≤ n) (δ : ℝ) : 0 < effDelta n δ := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_max_of_lt_right (by positivity)

theorem effDelta_le_one' (hn : 1 ≤ n) {δ : ℝ} (hδ1 : δ ≤ 1) : effDelta n δ ≤ 1 := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact max_le hδ1 (by rw [div_le_one (by positivity)]; exact one_le_pow₀ this)

/-! ## The phases -/

/-- Layer `ℓ` is noise-dominated (`𝖭`): `N_ℓ ≥ 2`, `D ε³ Δ³ ≤ n / Y⁴` and `ε² Δ² ≤ n / Y²`. -/
def UNoise (eps : ℝ) (p : ℕ → ℝ) (n : ℕ) (δ : ℝ) (ℓ : ℕ) : Prop :=
  2 ≤ reSize eps p n ℓ ∧
    effDelta n δ * eps ^ 3 * (reDelta eps p n ℓ : ℝ) ^ 3 ≤ n / Real.log n ^ 4 ∧
    eps ^ 2 * (reDelta eps p n ℓ : ℝ) ^ 2 ≤ n / Real.log n ^ 2

/-- The curvature condition `n Y⁴ ≤ D ε³ Δ_ℓ³` (`𝖢` on a layer with `N_ℓ ≥ 2`). -/
def UCurv (eps : ℝ) (p : ℕ → ℝ) (n : ℕ) (δ : ℝ) (ℓ : ℕ) : Prop :=
  (n : ℝ) * Real.log n ^ 4 ≤ effDelta n δ * eps ^ 3 * (reDelta eps p n ℓ : ℝ) ^ 3

/-- The first layer that is not noise-dominated (TeX `p`). -/
def uEnd (eps : ℝ) (p : ℕ → ℝ) (n : ℕ) (δ : ℝ) : ℕ := sInf {ℓ | ¬ UNoise eps p n δ ℓ}

/-- The first layer from `uEnd` on that is a singleton or curvature-dominated (TeX `ℓ₂`). -/
def uCurvStart (eps : ℝ) (p : ℕ → ℝ) (n : ℕ) (δ : ℝ) : ℕ :=
  sInf {ℓ | uEnd eps p n δ ≤ ℓ ∧ (reSize eps p n ℓ = 1 ∨ UCurv eps p n δ ℓ)}

variable {δ : ℝ}

theorem not_UNoise_uEnd (heps : 1 ≤ eps) (hn : 1 ≤ n) : ¬ UNoise eps p n δ (uEnd eps p n δ) := by
  have hne : ({ℓ | ¬ UNoise eps p n δ ℓ} : Set ℕ).Nonempty :=
    ⟨reHeight eps p n, fun h => by have := h.1; rw [reSize_reHeight heps hn] at this; omega⟩
  exact Nat.sInf_mem hne

theorem UNoise_of_lt_uEnd {ℓ : ℕ} (h : ℓ < uEnd eps p n δ) : UNoise eps p n δ ℓ := by
  by_contra h'
  exact absurd (Nat.sInf_le (show ℓ ∈ {ℓ | ¬ UNoise eps p n δ ℓ} from h')) (not_le.2 h)

theorem UCurv.mono (heps : 1 ≤ eps) (hn : 1 ≤ n) {ℓ ℓ' : ℕ} (h : UCurv eps p n δ ℓ)
    (hle : ℓ ≤ ℓ') : UCurv eps p n δ ℓ' := by
  unfold UCurv at *
  refine h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (reDelta_pos heps hn ℓ).le (reDelta_le_of_le heps hn hle) 3) ?_)
  exact mul_nonneg (effDelta_pos' hn δ).le (pow_nonneg (by linarith) 3)

theorem uCurvStart_mem (heps : 1 ≤ eps) (hn : 1 ≤ n) :
    uEnd eps p n δ ≤ uCurvStart eps p n δ ∧
      (reSize eps p n (uCurvStart eps p n δ) = 1 ∨ UCurv eps p n δ (uCurvStart eps p n δ)) := by
  have hne : ({ℓ | uEnd eps p n δ ≤ ℓ ∧ (reSize eps p n ℓ = 1 ∨ UCurv eps p n δ ℓ)} :
      Set ℕ).Nonempty :=
    ⟨uEnd eps p n δ + reHeight eps p n, by omega,
      Or.inl (reSize_eq_one_of_reHeight_le heps hn (by omega))⟩
  exact Nat.sInf_mem hne

/-- The layers between `uEnd` and `uCurvStart` are nontrivial and not curvature-dominated. -/
theorem band_of_lt_uCurvStart (heps : 1 ≤ eps) (hn : 1 ≤ n) {ℓ : ℕ} (h1 : uEnd eps p n δ ≤ ℓ)
    (h2 : ℓ < uCurvStart eps p n δ) : 2 ≤ reSize eps p n ℓ ∧ ¬ UCurv eps p n δ ℓ := by
  have hnot : ¬ (uEnd eps p n δ ≤ ℓ ∧ (reSize eps p n ℓ = 1 ∨ UCurv eps p n δ ℓ)) :=
    fun hmem => absurd (Nat.sInf_le (show ℓ ∈ {ℓ | uEnd eps p n δ ≤ ℓ ∧
      (reSize eps p n ℓ = 1 ∨ UCurv eps p n δ ℓ)} from hmem)) (not_le.2 h2)
  obtain ⟨h1', h2'⟩ := not_or.1 (not_and.1 hnot h1)
  have := one_le_reSize (p := p) heps hn ℓ
  exact ⟨by omega, h2'⟩

/-! ## The noise phase -/

section Facts

variable {cN CN Cu C0 c1 c2 c3 KL : ℝ}

theorem two_le_reSize_uEnd (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (hn2 : 2 ≤ n) : 2 ≤ reSize eps p n (uEnd eps p n δ) := by
  rcases Nat.eq_zero_or_pos (uEnd eps p n δ) with h0 | hpos
  · rw [h0]; exact hn2
  · obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, uEnd eps p n δ = ℓ + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have hN := UNoise_of_lt_uEnd (p := p) (δ := δ) (show ℓ < uEnd eps p n δ by omega)
    rw [hℓ]
    exact (hF.noise ℓ hN.1 hN.2.1 hN.2.2).2.2

theorem two_pow_sub_one_succ (ℓ : ℕ) : 2 ^ (ℓ + 1) - 1 = (2 ^ ℓ - 1) * 2 + 1 := by
  have := Nat.one_le_two_pow (n := ℓ)
  rw [pow_succ]
  omega

/-- The upper doubling bracket `Δ_ℓ ≤ (C_N ε²)^(2^ℓ - 1)` on the noise phase. -/
theorem reDelta_le_noise (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (hCN : 0 < CN) (heps : 1 ≤ eps) (hn : 1 ≤ n) :
    ∀ ℓ ≤ uEnd eps p n δ, (reDelta eps p n ℓ : ℝ) ≤ (CN * eps ^ 2) ^ (2 ^ ℓ - 1)
  | 0, _ => by simp
  | ℓ + 1, h => by
    have hN := UNoise_of_lt_uEnd (p := p) (δ := δ) (show ℓ < uEnd eps p n δ by omega)
    have ih := reDelta_le_noise hF hCN heps hn ℓ (by omega)
    have h1 := (hF.noise ℓ hN.1 hN.2.1 hN.2.2).2.1
    have hx : 0 ≤ CN * eps ^ 2 := mul_nonneg hCN.le (sq_nonneg _)
    have hΔ := (reDelta_pos (p := p) heps hn ℓ).le
    calc (reDelta eps p n (ℓ + 1) : ℝ) ≤ CN * eps ^ 2 * (reDelta eps p n ℓ : ℝ) ^ 2 := h1
      _ ≤ CN * eps ^ 2 * ((CN * eps ^ 2) ^ (2 ^ ℓ - 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΔ ih 2) hx
      _ = (CN * eps ^ 2) ^ (2 ^ (ℓ + 1) - 1) := by rw [two_pow_sub_one_succ]; ring

/-- The lower doubling bracket `(c_N ε²)^(2^ℓ - 1) ≤ Δ_ℓ` on the noise phase. -/
theorem noise_le_reDelta (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (hcN : 0 < cN) (heps : 1 ≤ eps) (hn : 1 ≤ n) :
    ∀ ℓ ≤ uEnd eps p n δ, (cN * eps ^ 2) ^ (2 ^ ℓ - 1) ≤ (reDelta eps p n ℓ : ℝ)
  | 0, _ => by simp
  | ℓ + 1, h => by
    have hN := UNoise_of_lt_uEnd (p := p) (δ := δ) (show ℓ < uEnd eps p n δ by omega)
    have ih := noise_le_reDelta hF hcN heps hn ℓ (by omega)
    have h1 := (hF.noise ℓ hN.1 hN.2.1 hN.2.2).1
    have hx : 0 ≤ cN * eps ^ 2 := mul_nonneg hcN.le (sq_nonneg _)
    calc (cN * eps ^ 2) ^ (2 ^ (ℓ + 1) - 1) =
          cN * eps ^ 2 * ((cN * eps ^ 2) ^ (2 ^ ℓ - 1)) ^ 2 := by
          rw [two_pow_sub_one_succ]; ring
      _ ≤ cN * eps ^ 2 * (reDelta eps p n ℓ : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg hx _) ih 2) hx
      _ ≤ reDelta eps p n (ℓ + 1) := h1

/-- The noise phase ends above `n^{1/4}`: `n < Δ_p⁴`. -/
theorem lt_reDelta_uEnd_pow (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (heps : 1 ≤ eps) (hn2 : 2 ≤ n) (hY : 1 ≤ Real.log n) (hδ1 : δ ≤ 1)
    (hbig : Real.log n ^ 16 * eps ^ 12 ≤ n) :
    (n : ℝ) < (reDelta eps p n (uEnd eps p n δ) : ℝ) ^ 4 := by
  have hn : 1 ≤ n := by omega
  have hnot := not_UNoise_uEnd (p := p) (δ := δ) heps hn
  have h2 := two_le_reSize_uEnd hF hn2
  by_contra hle
  push Not at hle
  apply hnot
  set Δ : ℝ := ((reDelta eps p n (uEnd eps p n δ) : ℕ) : ℝ)
  set Y := Real.log n
  have hΔ : 0 ≤ Δ := (reDelta_pos heps hn _).le
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hD1 := effDelta_le_one' hn hδ1
  have hD0 := (effDelta_pos' hn δ).le
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ eps := by linarith
  have he3 : 0 ≤ eps ^ 3 := pow_nonneg hε0 3
  have hΔ3 : 0 ≤ Δ ^ 3 := pow_nonneg hΔ 3
  have hY4 : 0 < Y ^ 4 := pow_pos hY0 4
  refine ⟨h2, ?_, ?_⟩
  · rw [le_div_iff₀ hY4]
    have h1 : eps ^ 3 * Δ ^ 3 * Y ^ 4 ≤ n := by
      apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hN.le
      calc (eps ^ 3 * Δ ^ 3 * Y ^ 4) ^ 4 = (Y ^ 16 * eps ^ 12) * (Δ ^ 4) ^ 3 := by ring
        _ ≤ (n : ℝ) * (n : ℝ) ^ 3 :=
            mul_le_mul hbig (pow_le_pow_left₀ (pow_nonneg hΔ 4) hle 3)
              (pow_nonneg (pow_nonneg hΔ 4) 3) hN.le
        _ = (n : ℝ) ^ 4 := by ring
    have h3 : effDelta n δ * (eps ^ 3 * Δ ^ 3 * Y ^ 4) ≤ 1 * (eps ^ 3 * Δ ^ 3 * Y ^ 4) :=
      mul_le_mul_of_nonneg_right hD1 (mul_nonneg (mul_nonneg he3 hΔ3) hY4.le)
    calc effDelta n δ * eps ^ 3 * Δ ^ 3 * Y ^ 4 = effDelta n δ * (eps ^ 3 * Δ ^ 3 * Y ^ 4) := by
          ring
      _ ≤ (n : ℝ) := by linarith
  · rw [le_div_iff₀ (pow_pos hY0 2)]
    apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hN.le
    have hε4 : eps ^ 4 ≤ eps ^ 12 := pow_le_pow_right₀ heps (by norm_num)
    have hY16 : Y ^ 4 ≤ Y ^ 16 := pow_le_pow_right₀ hY (by norm_num)
    have h4 : eps ^ 4 * Y ^ 4 ≤ n := by
      calc eps ^ 4 * Y ^ 4 ≤ eps ^ 12 * Y ^ 16 :=
            mul_le_mul hε4 hY16 (pow_nonneg hY0.le 4) (pow_nonneg hε0 12)
        _ = Y ^ 16 * eps ^ 12 := by ring
        _ ≤ (n : ℝ) := hbig
    calc (eps ^ 2 * Δ ^ 2 * Y ^ 2) ^ 2 = (eps ^ 4 * Y ^ 4) * Δ ^ 4 := by ring
      _ ≤ (n : ℝ) * n := mul_le_mul h4 hle (pow_nonneg hΔ 4) hN.le
      _ = (n : ℝ) ^ 2 := by ring

theorem one_le_uEnd (hn : 1 ≤ n)
    (hΔ : (n : ℝ) < (reDelta eps p n (uEnd eps p n δ) : ℝ) ^ 4) : 1 ≤ uEnd eps p n δ := by
  by_contra h
  have h0 : uEnd eps p n δ = 0 := by omega
  rw [h0, reDelta_zero] at hΔ
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num at hΔ
  linarith

/-- `log₂ x < j + 4` when `x < 12 · 2^j`. -/
theorem logb_lt_add_four {x : ℝ} {j : ℕ} (hx : 0 < x) (h : x < 12 * 2 ^ j) :
    Real.logb 2 x < j + 4 := by
  have h1 : Real.logb 2 x < Real.logb 2 (12 * 2 ^ j) := Real.logb_lt_logb one_lt_two hx h
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
    Real.logb_self_eq_one one_lt_two, mul_one] at h1
  have h12 : Real.logb 2 12 < 4 := by
    rw [Real.logb_lt_iff_lt_rpow one_lt_two (by norm_num),
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  linarith

/-- `j ≤ log₂ x` when `2^j ≤ x`. -/
theorem natCast_le_logb {x : ℝ} {j : ℕ} (h : (2 : ℝ) ^ j ≤ x) : (j : ℝ) ≤ Real.logb 2 x := by
  have h1 := Real.logb_le_logb_of_le one_lt_two (by positivity) h
  rwa [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at h1

/-- **Length of the noise phase, lower bound**: `log₂ (Y / log ε) < p + 4`. -/
theorem logb_lt_uEnd (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (hCN : 0 < CN) (heps : 1 < eps) (hn2 : 2 ≤ n) (hCNe : CN ≤ eps) (hCN1 : 1 ≤ CN * eps ^ 2)
    (hΔ : (n : ℝ) < (reDelta eps p n (uEnd eps p n δ) : ℝ) ^ 4) :
    Real.logb 2 (Real.log n / Real.log eps) < uEnd eps p n δ + 4 := by
  set P := uEnd eps p n δ
  have hn : 1 ≤ n := by omega
  have hbr := reDelta_le_noise hF hCN heps.le hn P le_rfl
  have hlogε : 0 < Real.log eps := Real.log_pos heps
  have hN1 : (1 : ℝ) < n := by exact_mod_cast hn2
  have hY : 0 < Real.log n := Real.log_pos hN1
  have hlogx : Real.log (CN * eps ^ 2) ≤ 3 * Real.log eps := by
    rw [show (3 : ℝ) * Real.log eps = ((3 : ℕ) : ℝ) * Real.log eps by norm_num, ← Real.log_pow]
    apply Real.log_le_log (by linarith)
    calc CN * eps ^ 2 ≤ eps * eps ^ 2 := mul_le_mul_of_nonneg_right hCNe (sq_nonneg _)
      _ = eps ^ 3 := by ring
  have hlogx0 : 0 ≤ Real.log (CN * eps ^ 2) := Real.log_nonneg hCN1
  have h1 : Real.log (reDelta eps p n P) ≤ (2 : ℝ) ^ P * (3 * Real.log eps) := by
    calc Real.log (reDelta eps p n P) ≤ Real.log ((CN * eps ^ 2) ^ (2 ^ P - 1)) :=
          Real.log_le_log (reDelta_pos heps.le hn P) hbr
      _ = ((2 ^ P - 1 : ℕ) : ℝ) * Real.log (CN * eps ^ 2) := Real.log_pow _ _
      _ ≤ (2 : ℝ) ^ P * Real.log (CN * eps ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hlogx0
          have : ((2 ^ P - 1 : ℕ) : ℝ) ≤ ((2 ^ P : ℕ) : ℝ) := Nat.cast_le.2 (Nat.sub_le _ _)
          exact_mod_cast this
      _ ≤ (2 : ℝ) ^ P * (3 * Real.log eps) := mul_le_mul_of_nonneg_left hlogx (by positivity)
  have h2 : Real.log n < 4 * Real.log (reDelta eps p n P) := by
    have := Real.log_lt_log (by positivity) hΔ
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have h3 : Real.log n / Real.log eps < 12 * 2 ^ P := by
    rw [div_lt_iff₀ hlogε]
    nlinarith
  exact logb_lt_add_four (div_pos hY hlogε) h3

/-- **Length of the noise phase, upper bound**: `p ≤ log₂ (Y / log ε) + 1`. -/
theorem uEnd_le_logb (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (hcN : 0 < cN) (heps : 1 < eps) (hn : 1 ≤ n) (hcNe : eps ≤ cN * eps ^ 2)
    (hX : 2 * Real.log eps ≤ Real.log n) (hY : 1 ≤ Real.log n) (hP1 : 1 ≤ uEnd eps p n δ) :
    (uEnd eps p n δ : ℝ) ≤ Real.logb 2 (Real.log n / Real.log eps) + 1 := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, uEnd eps p n δ = ℓ + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hP1).symm⟩
  have hN := UNoise_of_lt_uEnd (p := p) (δ := δ) (show ℓ < uEnd eps p n δ by omega)
  have hbr := noise_le_reDelta hF hcN heps.le hn ℓ (by omega)
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hΔ := reDelta_pos (p := p) heps.le hn ℓ
  have hsq : (reDelta eps p n ℓ : ℝ) ^ 2 ≤ n := by
    have h1 := hN.2.2
    have h2 : (n : ℝ) / Real.log n ^ 2 ≤ n := div_le_self hN0.le (one_le_pow₀ hY)
    have h3 : (reDelta eps p n ℓ : ℝ) ^ 2 ≤ eps ^ 2 * (reDelta eps p n ℓ : ℝ) ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ heps.le)
    linarith
  have hlogΔ : 2 * Real.log (reDelta eps p n ℓ) ≤ Real.log n := by
    have := Real.log_le_log (by positivity) hsq
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hlogx : Real.log eps ≤ Real.log (cN * eps ^ 2) := Real.log_le_log (by linarith) hcNe
  have hlogε : 0 < Real.log eps := Real.log_pos heps
  have hx : 0 < cN * eps ^ 2 := by
    have : 0 < eps ^ 2 := by positivity
    exact mul_pos hcN this
  have h1 : ((2 ^ ℓ - 1 : ℕ) : ℝ) * Real.log eps ≤ Real.log (reDelta eps p n ℓ) := by
    calc ((2 ^ ℓ - 1 : ℕ) : ℝ) * Real.log eps ≤
          ((2 ^ ℓ - 1 : ℕ) : ℝ) * Real.log (cN * eps ^ 2) :=
          mul_le_mul_of_nonneg_left hlogx (Nat.cast_nonneg _)
      _ = Real.log ((cN * eps ^ 2) ^ (2 ^ ℓ - 1)) := (Real.log_pow _ _).symm
      _ ≤ Real.log (reDelta eps p n ℓ) := Real.log_le_log (pow_pos hx _) hbr
  have hcast : ((2 ^ ℓ - 1 : ℕ) : ℝ) = (2 : ℝ) ^ ℓ - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  rw [hcast] at h1
  have h2 : (2 : ℝ) ^ ℓ ≤ Real.log n / Real.log eps := by
    rw [le_div_iff₀ hlogε]
    nlinarith
  have := natCast_le_logb h2
  rw [hℓ]
  push_cast
  linarith

/-- From `p` on, a nontrivial layer is not noise-dominated. -/
theorem not_noise_of_uEnd_le (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (heps : 1 ≤ eps) (hn2 : 2 ≤ n) {ℓ : ℕ} (hℓ : uEnd eps p n δ ≤ ℓ) :
    (n : ℝ) / Real.log n ^ 4 < effDelta n δ * eps ^ 3 * (reDelta eps p n ℓ : ℝ) ^ 3 ∨
      (n : ℝ) / Real.log n ^ 2 < eps ^ 2 * (reDelta eps p n ℓ : ℝ) ^ 2 := by
  have hn : 1 ≤ n := by omega
  by_contra h
  push Not at h
  apply not_UNoise_uEnd (p := p) (δ := δ) heps hn
  have hmono := reDelta_le_of_le (p := p) heps hn hℓ
  have hΔ := (reDelta_pos (p := p) heps hn (uEnd eps p n δ)).le
  refine ⟨two_le_reSize_uEnd hF hn2, le_trans ?_ h.1, le_trans ?_ h.2⟩
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΔ hmono 3)
      (mul_nonneg (effDelta_pos' hn δ).le (pow_nonneg (by linarith) 3))
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΔ hmono 2) (sq_nonneg _)

/-- **At most three band layers**: `ℓ₂ ≤ p + 3`.  A nonterminal band layer multiplies `Δ` by
    at least `n^{1/4}`, `n < Δ_p⁴`, and a nontrivial layer has `Δ < n`. -/
theorem uCurvStart_le (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (heps : 1 ≤ eps) (hn2 : 2 ≤ n)
    (hΔ : (n : ℝ) < (reDelta eps p n (uEnd eps p n δ) : ℝ) ^ 4) :
    uCurvStart eps p n δ ≤ uEnd eps p n δ + 3 := by
  have hn : 1 ≤ n := by omega
  set P := uEnd eps p n δ with hP
  by_contra hQ
  push Not at hQ
  have hB : ∀ i ≤ 3, 2 ≤ reSize eps p n (P + i) ∧ ¬ UCurv eps p n δ (P + i) := fun i hi =>
    band_of_lt_uCurvStart heps hn (by omega) (by omega)
  have hN0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : ∀ i ≤ 2, (n : ℝ) ≤ (reStep eps p n (P + i) : ℝ) ^ 4 := by
    intro i hi
    obtain ⟨h2, hC⟩ := hB i (by omega)
    rcases hF.band (P + i) h2 (not_noise_of_uEnd_le hF heps hn2 (by omega)) (not_le.1 hC)
      with hM | hd
    · exfalso
      have h1 := reSize_succ_eq_one_of_reSegs heps hn hM
      have h2' := (hB (i + 1) (by omega)).1
      rw [← Nat.add_assoc] at h2'
      omega
    · calc (n : ℝ) = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
        _ ≤ (reStep eps p n (P + i) : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) hd 4
  have hlt : (reDelta eps p n (P + 3) : ℝ) < n := by
    exact_mod_cast reDelta_lt heps hn (hB 3 le_rfl).1
  have heq : (reDelta eps p n (P + 3) : ℝ) = reStep eps p n (P + 2) *
      (reStep eps p n (P + 1) * (reStep eps p n P * reDelta eps p n P)) := by
    rw [show P + 3 = P + 2 + 1 from rfl, reDelta_succ, show P + 2 = P + 1 + 1 from rfl,
      reDelta_succ, reDelta_succ]
    push_cast
    ring
  have h4 : (reDelta eps p n (P + 3) : ℝ) ^ 4 < (n : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hlt (Nat.cast_nonneg _) (by norm_num)
  rw [heq] at h4
  have ha := hd 2 (by norm_num)
  have hb := hd 1 (by norm_num)
  have hc := hd 0 (by norm_num)
  rw [Nat.add_zero] at hc
  set a : ℝ := ((reStep eps p n (P + 2) : ℕ) : ℝ)
  set b : ℝ := ((reStep eps p n (P + 1) : ℕ) : ℝ)
  set c : ℝ := ((reStep eps p n P : ℕ) : ℝ)
  set Δ : ℝ := ((reDelta eps p n P : ℕ) : ℝ)
  have e1 : (n : ℝ) * n < c ^ 4 * Δ ^ 4 :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left hΔ hN0)
      (mul_le_mul_of_nonneg_right hc (by positivity))
  have e2 : (n : ℝ) * (n * n) < b ^ 4 * (c ^ 4 * Δ ^ 4) :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left e1 hN0)
      (mul_le_mul_of_nonneg_right hb (by positivity))
  have e3 : (n : ℝ) * (n * (n * n)) < a ^ 4 * (b ^ 4 * (c ^ 4 * Δ ^ 4)) :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left e2 hN0)
      (mul_le_mul_of_nonneg_right ha (by positivity))
  have e4 : (a * (b * (c * Δ))) ^ 4 = a ^ 4 * (b ^ 4 * (c ^ 4 * Δ ^ 4)) := by ring
  have e5 : (n : ℝ) ^ 4 = n * (n * (n * n)) := by ring
  linarith

end Facts

end Run

end

end PGM
