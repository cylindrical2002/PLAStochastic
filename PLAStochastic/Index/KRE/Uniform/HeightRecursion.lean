import PLAStochastic.Index.KRE.Uniform.CurvaturePhase

/-!
# The deterministic height recursion of `thm:uniform`

Section 4 of `research/2026-09-24-re-curvature-uniform/tex/main.tex` ("Proof of
`thm:uniform`"), deterministically: from the per-layer bounds of its Section 3, packaged as
`UniformLayerFacts`, the ALG-RE height satisfies `|H - twoPhase n ε δ| ≤ 8`
(`abs_reHeight_sub_twoPhase_le`) once `n` and `ε` are large in the sense of five explicit
conditions depending only on the eight constants; along `n → ∞`, `ε → ∞`,
`log ε = o(log n)` these hold eventually, uniformly in the keys and in `δ ∈ [0, 1]`
(`twoPhase_of_layerFacts`).

With `Φ₁ = log₂ (Y / log ε)`, `Φ₂` the second term of `twoPhase` and `p = uEnd`:
`Φ₁ - 4 < p ≤ Φ₁ + 1` and `H ≥ p + 1` (noise phase); at most three band layers, so the first
singleton-or-curvature layer is `ℓ₂ ≤ p + 3`; from there the upper curvature count gives
`H ≤ ℓ₂ + Φ₂ + 4` (`log₂ (Y / log (ε / D) + 1) ≤ Φ₂ + 1`,
`logb_div_log_effDelta_le`).  If `Φ₂ > 4` then `δ > n^{-1/16}`, so `D = δ`, the band layers do
not terminate, `ℓ₂` is a curvature layer with `s⁴ ≥ n`, and the lower curvature count gives
`H > ℓ₂ + Φ₂ - 3`.

Nothing here is probabilistic.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

/-- The upper curvature count stays below the second term of `twoPhase` plus one:
    `log₂ (Y / log (ε / D) + 1) ≤ Φ₂ + 1`.  For `δ ≥ n⁻³`, `D = δ` and
    `log₂ (x + 1) ≤ max 0 (log₂ x) + 1`; for `δ < n⁻³`, `log (ε / D) ≥ 3 Y`. -/
theorem logb_div_log_effDelta_le {n : ℕ} {eps δ : ℝ} (hn2 : 2 ≤ n) (heps : 1 < eps)
    (hδ1 : δ ≤ 1) :
    Real.logb 2 (Real.log n / Real.log (eps / effDelta n δ) + 1) ≤
      (if δ = 0 then 0 else max 0 (Real.logb 2 (Real.log n / Real.log (eps / δ)))) + 1 := by
  have hN1 : (1 : ℝ) < n := by exact_mod_cast hn2
  have hN0 : (0 : ℝ) < n := by linarith
  have hY : 0 < Real.log n := Real.log_pos hN1
  have hε0 : 0 < eps := by linarith
  have hlogε : 0 < Real.log eps := Real.log_pos heps
  have hΦ0 : 0 ≤ (if δ = 0 then 0 else max 0 (Real.logb 2 (Real.log n / Real.log (eps / δ)))) := by
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _
  by_cases hδn : 1 / (n : ℝ) ^ 3 ≤ δ
  · have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hδn
    have hD : effDelta n δ = δ := max_eq_left hδn
    rw [hD, if_neg hδpos.ne']
    have hA : 0 < Real.log (eps / δ) := by
      rw [Real.log_div hε0.ne' hδpos.ne']
      have := Real.log_nonpos hδpos.le hδ1
      linarith
    set x := Real.log n / Real.log (eps / δ) with hx
    have hx0 : 0 < x := div_pos hY hA
    rcases le_or_gt x 1 with hx1 | hx1
    · have h1 : Real.logb 2 (x + 1) ≤ 1 := by
        rw [Real.logb_le_iff_le_rpow one_lt_two (by linarith), Real.rpow_one]
        linarith
      have := le_max_left 0 (Real.logb 2 x)
      linarith
    · have h1 : Real.logb 2 (x + 1) ≤ Real.logb 2 (2 * x) :=
        Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
      rw [Real.logb_mul (by norm_num) hx0.ne', Real.logb_self_eq_one one_lt_two] at h1
      have := le_max_right 0 (Real.logb 2 x)
      linarith
  · push Not at hδn
    have hD : effDelta n δ = 1 / (n : ℝ) ^ 3 := max_eq_right hδn.le
    rw [hD]
    have hA : 3 * Real.log n ≤ Real.log (eps / (1 / (n : ℝ) ^ 3)) := by
      rw [show eps / (1 / (n : ℝ) ^ 3) = eps * (n : ℝ) ^ 3 by field_simp,
        Real.log_mul hε0.ne' (by positivity), Real.log_pow]
      push_cast
      linarith
    have hx : Real.log n / Real.log (eps / (1 / (n : ℝ) ^ 3)) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hx0 : 0 ≤ Real.log n / Real.log (eps / (1 / (n : ℝ) ^ 3)) :=
      div_nonneg hY.le (by linarith)
    have : Real.logb 2 (Real.log n / Real.log (eps / (1 / (n : ℝ) ^ 3)) + 1) ≤ 1 := by
      rw [Real.logb_le_iff_le_rpow one_lt_two (by linarith), Real.rpow_one]
      linarith
    linarith

/-! ## The constants -/

/-- `G = max 1 (2 (C_u + C_0))`, the constant of the upper curvature count. -/
def unifG (Cu C0 : ℝ) : ℝ := max 1 (2 * (Cu + C0))

/-- `c₅ = min c₁ (min c₂ c₃)`, the constant of the lower curvature count. -/
def unifC5 (c1 c2 c3 : ℝ) : ℝ := min c1 (min c2 c3)

/-- `b = max 1 (2 / c₅)`. -/
def unifB (c1 c2 c3 : ℝ) : ℝ := max 1 (2 / unifC5 c1 c2 c3)

/-- `K₂ = max K_L (16 / c₅²)`, the stopping level of the lower curvature count. -/
def unifK2 (c1 c2 c3 KL : ℝ) : ℝ := max KL (16 / unifC5 c1 c2 c3 ^ 2)

/-- The threshold `ε ≥ ε₀`. -/
def unifEps0 (cN CN Cu C0 c1 c2 c3 KL : ℝ) : ℝ :=
  max (max 3 CN) (max (max (1 / cN) (1 / CN))
    (max (unifG Cu C0 ^ 2) (unifB c1 c2 c3 ^ 2 * unifK2 c1 c2 c3 KL)))

/-- The polylogarithmic threshold `K₀ (log n)¹⁶ ≤ n`. -/
def unifPoly (CN c1 c2 c3 KL : ℝ) : ℝ :=
  max (max (KL ^ 12) (CN ^ 24)) (max (16 ^ 6 / c1 ^ 24) (max (16 ^ 6 / c2 ^ 24) (4096 / c3 ^ 12)))

/-! ## The deterministic bound -/

/-- **The two-phase height, deterministic form.**  Under the per-layer bounds
    `UniformLayerFacts`, for `n ≥ 3`, `ε ≥ ε₀` (`unifEps0`), `2 log ε ≤ log n`,
    `(log n)¹⁶ ε¹² ≤ n` and `K₀ (log n)¹⁶ ≤ n` (`unifPoly`): `|H - twoPhase n ε δ| ≤ 8`. -/
theorem abs_reHeight_sub_twoPhase_le {eps : ℝ} {p : ℕ → ℝ} {n : ℕ}
    {δ cN CN Cu C0 c1 c2 c3 KL : ℝ} (hF : UniformLayerFacts p n eps δ cN CN Cu C0 c1 c2 c3 KL)
    (hcN : 0 < cN) (hCN : 0 < CN) (hCu : 0 < Cu) (hC0 : 0 ≤ C0) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hc3 : 0 < c3) (hKL : 0 < KL) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hn3 : 3 ≤ n)
    (hε : unifEps0 cN CN Cu C0 c1 c2 c3 KL ≤ eps) (hX : 2 * Real.log eps ≤ Real.log n)
    (hbig : Real.log n ^ 16 * eps ^ 12 ≤ n)
    (hpoly : unifPoly CN c1 c2 c3 KL * Real.log n ^ 16 ≤ n) :
    |(reHeight eps p n : ℝ) - twoPhase n eps δ| ≤ 8 := by
  -- the thresholds
  unfold unifEps0 at hε
  unfold unifPoly at hpoly
  have hε3 : 3 ≤ eps := ((le_max_left 3 CN).trans (le_max_left _ _)).trans hε
  have hCNe : CN ≤ eps := ((le_max_right 3 CN).trans (le_max_left _ _)).trans hε
  have hcNe : 1 / cN ≤ eps :=
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hε
  have hCNe' : 1 / CN ≤ eps :=
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hε
  have hGe : unifG Cu C0 ^ 2 ≤ eps :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hε
  have hbKe : unifB c1 c2 c3 ^ 2 * unifK2 c1 c2 c3 KL ≤ eps :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hε
  have hn : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hY : 1 ≤ Real.log n := one_le_log_of_three_le hn3
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hY16 : 1 ≤ Real.log n ^ 16 := one_le_pow₀ hY
  have hPx : ∀ x, x ≤ max (max (KL ^ 12) (CN ^ 24))
      (max (16 ^ 6 / c1 ^ 24) (max (16 ^ 6 / c2 ^ 24) (4096 / c3 ^ 12))) →
      x * Real.log n ^ 16 ≤ n := fun x hx =>
    (mul_le_mul_of_nonneg_right hx (by positivity)).trans hpoly
  have hKLn : KL ^ 12 * Real.log n ^ 16 ≤ (n : ℝ) ^ 7 :=
    (hPx _ ((le_max_left _ _).trans (le_max_left _ _))).trans (le_self_pow₀ hN1 (by norm_num))
  have hCNn : CN ^ 24 ≤ n :=
    (le_mul_of_one_le_right (by positivity) hY16).trans
      (hPx _ ((le_max_right _ _).trans (le_max_left _ _)))
  have h1n : 16 ^ 6 * Real.log n ^ 16 ≤ c1 ^ 24 * n := by
    have h := hPx _ ((le_max_left _ _).trans (le_max_right _ _))
    have hc : c1 ^ 24 ≠ 0 := by positivity
    calc 16 ^ 6 * Real.log n ^ 16 = c1 ^ 24 * (16 ^ 6 / c1 ^ 24 * Real.log n ^ 16) := by
          field_simp
      _ ≤ c1 ^ 24 * n := mul_le_mul_of_nonneg_left h (by positivity)
  have h2n : 16 ^ 6 * Real.log n ^ 8 ≤ c2 ^ 24 * n := by
    have h := hPx _ ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    have hc : c2 ^ 24 ≠ 0 := by positivity
    have hY8 : Real.log n ^ 8 ≤ Real.log n ^ 16 := pow_le_pow_right₀ hY (by norm_num)
    calc 16 ^ 6 * Real.log n ^ 8 ≤ 16 ^ 6 * Real.log n ^ 16 := by linarith
      _ = c2 ^ 24 * (16 ^ 6 / c2 ^ 24 * Real.log n ^ 16) := by field_simp
      _ ≤ c2 ^ 24 * n := mul_le_mul_of_nonneg_left h (by positivity)
  have h3n : 4096 * Real.log n ^ 16 ≤ c3 ^ 12 * (n : ℝ) ^ 4 := by
    have h := hPx _ ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    have hc : c3 ^ 12 ≠ 0 := by positivity
    calc 4096 * Real.log n ^ 16 = c3 ^ 12 * (4096 / c3 ^ 12 * Real.log n ^ 16) := by field_simp
      _ ≤ c3 ^ 12 * n := mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ c3 ^ 12 * (n : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left (le_self_pow₀ hN1 (by norm_num)) (by positivity)
  -- consequences for `ε`
  have heps1 : 1 < eps := by linarith
  have hcNe2 : eps ≤ cN * eps ^ 2 := by
    have h := (div_le_iff₀ hcN).1 hcNe
    nlinarith
  have hCN1 : 1 ≤ CN * eps ^ 2 := by
    have h := (div_le_iff₀ hCN).1 hCNe'
    nlinarith
  -- the constants of the curvature counts
  have hG1 : 1 ≤ unifG Cu C0 := le_max_left _ _
  have hG : 2 * (Cu + C0) ≤ unifG Cu C0 := le_max_right _ _
  have hc₅ : 0 < unifC5 c1 c2 c3 := lt_min hc1 (lt_min hc2 hc3)
  have h51 : unifC5 c1 c2 c3 ≤ c1 := min_le_left _ _
  have h52 : unifC5 c1 c2 c3 ≤ c2 := (min_le_right _ _).trans (min_le_left _ _)
  have h53 : unifC5 c1 c2 c3 ≤ c3 := (min_le_right _ _).trans (min_le_right _ _)
  have hb : 1 ≤ unifB c1 c2 c3 := le_max_left _ _
  have hbc : 2 ≤ unifB c1 c2 c3 * unifC5 c1 c2 c3 :=
    (div_le_iff₀ hc₅).1 (le_max_right _ _)
  have hK₂ : KL ≤ unifK2 c1 c2 c3 KL := le_max_left _ _
  have hK₂' : 16 ≤ unifC5 c1 c2 c3 ^ 2 * unifK2 c1 c2 c3 KL := by
    have h := (div_le_iff₀ (by positivity)).1 (le_max_right KL (16 / unifC5 c1 c2 c3 ^ 2))
    unfold unifK2
    linarith
  -- the noise phase
  have hΔP := lt_reDelta_uEnd_pow hF heps1.le hn2 hY hδ1 hbig
  have hP1 := one_le_uEnd hn hΔP
  have hPlow := logb_lt_uEnd hF hCN heps1 hn2 hCNe hCN1 hΔP
  have hPup := uEnd_le_logb hF hcN heps1 hn hcNe2 hX hY hP1
  have hP2 := two_le_reSize_uEnd hF hn2
  have hHP : uEnd eps p n δ < reHeight eps p n := (lt_reHeight_iff heps1.le hn hP1).2 hP2
  have hHP' : (uEnd eps p n δ : ℝ) + 1 ≤ reHeight eps p n := by exact_mod_cast hHP
  have hQ := uCurvStart_mem (p := p) (δ := δ) heps1.le hn
  have hQle := uCurvStart_le hF heps1.le hn2 hΔP
  have hQle' : (uCurvStart eps p n δ : ℝ) ≤ uEnd eps p n δ + 3 := by exact_mod_cast hQle
  have hPQ' : (uEnd eps p n δ : ℝ) ≤ uCurvStart eps p n δ := by exact_mod_cast hQ.1
  have hQ1 : 1 ≤ uCurvStart eps p n δ := le_trans hP1 hQ.1
  have hΔPY : Real.log n ^ 2 ≤ (reDelta eps p n (uEnd eps p n δ) : ℝ) := by
    by_contra h
    push Not at h
    have hY8 : Real.log n ^ 8 ≤ n := by
      have h1 : Real.log n ^ 8 ≤ Real.log n ^ 16 := pow_le_pow_right₀ hY (by norm_num)
      have h2 : Real.log n ^ 16 ≤ Real.log n ^ 16 * eps ^ 12 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ heps1.le)
      linarith
    have h4 : (reDelta eps p n (uEnd eps p n δ) : ℝ) ^ 4 < (Real.log n ^ 2) ^ 4 :=
      pow_lt_pow_left₀ h (Nat.cast_nonneg _) (by norm_num)
    have : (Real.log n ^ 2) ^ 4 = Real.log n ^ 8 := by ring
    linarith
  -- the two terms
  have htw : twoPhase n eps δ = Real.logb 2 (Real.log n / Real.log eps) +
      (if δ = 0 then 0 else max 0 (Real.logb 2 (Real.log n / Real.log (eps / δ)))) := rfl
  have hΦ0 : 0 ≤ (if δ = 0 then 0 else max 0 (Real.logb 2 (Real.log n / Real.log (eps / δ)))) := by
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _
  rw [htw, abs_le]
  constructor
  · -- lower bound
    by_cases hΦ : (if δ = 0 then 0 else
        max 0 (Real.logb 2 (Real.log n / Real.log (eps / δ)))) ≤ 4
    · linarith
    have hδne : δ ≠ 0 := by
      intro h
      rw [if_pos h] at hΦ
      norm_num at hΦ
    rw [if_neg hδne] at hΦ ⊢
    have hδpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδne)
    have hL : 4 < Real.logb 2 (Real.log n / Real.log (eps / δ)) := by
      rcases lt_max_iff.1 (not_le.1 hΦ) with h | h
      · norm_num at h
      · exact h
    have hε0 : 0 < eps := by linarith
    have hlogε : 0 < Real.log eps := Real.log_pos heps1
    have hA : Real.log eps ≤ Real.log (eps / δ) := by
      rw [Real.log_div hε0.ne' hδpos.ne']
      have := Real.log_nonpos hδpos.le hδ1
      linarith
    have hApos : 0 < Real.log (eps / δ) := lt_of_lt_of_le hlogε hA
    have hY0 : 0 < Real.log n := by linarith
    have hAY : 16 * Real.log (eps / δ) < Real.log n := by
      have h := (Real.lt_logb_iff_rpow_lt one_lt_two (div_pos hY0 hApos)).1 hL
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, lt_div_iff₀ hApos] at h
      norm_num at h
      linarith
    have hlogδ : -(Real.log n / 16) < Real.log δ := by
      rw [Real.log_div hε0.ne' hδpos.ne'] at hAY
      linarith
    have hδn : 1 < δ ^ 16 * n := by
      have hpos : 0 < δ ^ 16 * n := by positivity
      rw [← Real.log_pos_iff hpos.le, Real.log_mul (by positivity) hN0.ne', Real.log_pow]
      push_cast
      linarith
    have hδn3 : 1 / (n : ℝ) ^ 3 ≤ δ := by
      have h1 : Real.log (1 / (n : ℝ) ^ 3) < Real.log δ := by
        rw [one_div, Real.log_inv, Real.log_pow]
        push_cast
        linarith
      exact ((Real.log_lt_log_iff (by positivity) hδpos).1 h1).le
    have hD : effDelta n δ = δ := max_eq_left hδn3
    -- the first curvature layer
    have hQ2 : 2 ≤ reSize eps p n (uCurvStart eps p n δ) ∧
        (n : ℝ) ≤ ((n : ℝ) / reDelta eps p n (uCurvStart eps p n δ)) ^ 4 := by
      rcases hQ.1.eq_or_lt with h | h
      · rw [← h]
        exact ⟨hP2, le_div_reDelta_uEnd_pow hF hCN heps1.le hn hY hδpos hD hδn hCNn hP1⟩
      · obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, uCurvStart eps p n δ = ℓ + 1 := ⟨uCurvStart eps p n δ - 1, by omega⟩
        have hB := band_of_lt_uCurvStart (p := p) (δ := δ) heps1.le hn
          (show uEnd eps p n δ ≤ ℓ by omega) (show ℓ < uCurvStart eps p n δ by omega)
        have hΔY := hΔPY.trans (reDelta_le_of_le heps1.le hn (show uEnd eps p n δ ≤ ℓ by omega))
        obtain ⟨hM2, hM4⟩ := band_layer_segs hF heps1.le hn hY hδpos hδ1 hD hδn hc1 hc2 hc3
          hKLn h1n h2n h3n hB.1 hB.2 hΔY
        rw [hℓ]
        refine ⟨le_trans hM2 (reSize_succ_bounds heps1.le hn ℓ).1, ?_⟩
        have h1 := reSegs_sub_one_lt (p := p) heps1.le hn ℓ
        have h0 : 0 ≤ (reSegs eps p n ℓ : ℝ) - 1 := by
          have : (2 : ℝ) ≤ reSegs eps p n ℓ := by exact_mod_cast hM2
          linarith
        exact hM4.trans (pow_le_pow_left₀ h0 h1.le 4)
    have hQC : UCurv eps p n δ (uCurvStart eps p n δ) := hQ.2.resolve_left (by omega)
    have hQY := hΔPY.trans (reDelta_le_of_le heps1.le hn hQ.1)
    have hlow := lt_reHeight_curvPhase hF heps1 hn2 hY hδpos hδ1 hD hKL hc₅ h51 h52 h53 hK₂ hK₂'
      hb hbc hbKe hQ1 hQ2.1 hQC hQY hQ2.2
    have hmax : max 0 (Real.logb 2 (Real.log n / Real.log (eps / δ))) =
        Real.logb 2 (Real.log n / Real.log (eps / δ)) := max_eq_right (by linarith)
    rw [hmax]
    linarith
  · -- upper bound
    rcases hQ.2 with hQ1' | hQC
    · have h := reHeight_le hQ1 hQ1'
      have h' : (reHeight eps p n : ℝ) ≤ uCurvStart eps p n δ := by exact_mod_cast h
      linarith
    · have hup := reHeight_le_curvPhase hF heps1 hn hδ1 hCu hC0 hG1 hG hGe hQ1 hQC
      have hphi := logb_div_log_effDelta_le (δ := δ) hn2 heps1 hδ1
      linarith

/-! ## Along the sequence -/

/-- **`thm:uniform`, deterministic part.**  There is `K` (namely `8`) such that along every
    sequence `n → ∞`, `ε → ∞`, `log ε / log n → 0`, eventually, for all keys `p` and all
    `δ ∈ [0, 1]` satisfying the per-layer bounds `UniformLayerFacts`,
    `|H - (log₂ (log n / log ε) + log₂⁺ (log n / log (ε / δ)))| ≤ K`. -/
theorem twoPhase_of_layerFacts {cN CN Cu C0 c1 c2 c3 KL : ℝ} (hcN : 0 < cN) (hCN : 0 < CN)
    (hCu : 0 < Cu) (hC0 : 0 ≤ C0) (hc1 : 0 < c1) (hc2 : 0 < c2) (hc3 : 0 < c3) (hKL : 0 < KL) :
    ∃ K : ℝ, ∀ {N : ℕ → ℕ} {ε : ℕ → ℝ},
      Tendsto (fun k => (N k : ℝ)) atTop atTop → Tendsto ε atTop atTop →
      Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0) →
      ∀ᶠ k in atTop, ∀ (p : ℕ → ℝ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 →
        UniformLayerFacts p (N k) (ε k) δ cN CN Cu C0 c1 c2 c3 KL →
        |(reHeight (ε k) p (N k) : ℝ) - twoPhase (N k) (ε k) δ| ≤ K := by
  refine ⟨8, fun {N ε} hN hε hεN => ?_⟩
  filter_upwards [hN.eventually_ge_atTop 3,
    hε.eventually_ge_atTop (unifEps0 cN CN Cu C0 c1 c2 c3 KL),
    eventually_le_rpow_of_logRatio hN hε hεN (by norm_num : (0 : ℝ) < 1 / 24),
    hN.eventually (eventually_mul_log_pow_le_rpow 1 16 (by norm_num : (0 : ℝ) < 1 / 2)),
    hN.eventually (eventually_mul_log_pow_le_rpow (unifPoly CN c1 c2 c3 KL) 16 one_pos)]
    with k h3 hεk h24 hY16 hpoly
  intro p δ hδ0 hδ1 hF
  have hn3 : 3 ≤ N k := by exact_mod_cast h3
  have hN0 : (0 : ℝ) < N k := by linarith
  have h3e : (3 : ℝ) ≤ unifEps0 cN CN Cu C0 c1 c2 c3 KL :=
    (le_max_left 3 CN).trans (le_max_left _ _)
  have hε1 : 1 ≤ ε k := by linarith
  have hlog24 : Real.log (ε k) ≤ Real.log (N k) / 24 := by
    have := Real.log_le_log (by linarith) h24
    rw [Real.log_rpow hN0] at this
    linarith
  have hlogε0 : 0 ≤ Real.log (ε k) := Real.log_nonneg hε1
  have hX : 2 * Real.log (ε k) ≤ Real.log (N k) := by linarith
  have hbig : Real.log (N k) ^ 16 * ε k ^ 12 ≤ N k := by
    have h1 : ε k ^ 12 ≤ (N k : ℝ) ^ (1 / 2 : ℝ) := by
      calc ε k ^ 12 ≤ ((N k : ℝ) ^ (1 / 24 : ℝ)) ^ 12 := pow_le_pow_left₀ (by linarith) h24 12
        _ = (N k : ℝ) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
            norm_num
    have h2 : Real.log (N k) ^ 16 ≤ (N k : ℝ) ^ (1 / 2 : ℝ) := by
      simpa only [one_mul] using hY16
    calc Real.log (N k) ^ 16 * ε k ^ 12 ≤ (N k : ℝ) ^ (1 / 2 : ℝ) * (N k : ℝ) ^ (1 / 2 : ℝ) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = N k := by
          rw [← Real.rpow_add hN0]
          norm_num
  have hpoly' : unifPoly CN c1 c2 c3 KL * Real.log (N k) ^ 16 ≤ N k := by
    simpa only [Real.rpow_one] using hpoly
  exact abs_reHeight_sub_twoPhase_le hF hcN hCN hCu hC0 hc1 hc2 hc3 hKL hδ0 hδ1 hn3 hεk hX hbig
    hpoly'

end

end PGM
