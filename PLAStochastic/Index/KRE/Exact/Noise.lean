import PLAStochastic.Index.KRE.Uniform.LayerPhases

/-! # Locating the exact noise-to-curvature transition -/

namespace PGM
noncomputable section

theorem kre_effDelta_one {n : ℕ} (hn : 1 ≤ n) : effDelta n (1 : ℝ) = 1 := by
  apply max_eq_left
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact (div_le_one (by positivity)).2 (one_le_pow₀ hn')

theorem kre_noise_of_log {eps : ℝ} {p : ℕ → ℝ} {n ℓ : ℕ}
    (he : 1 ≤ eps) (hn : 1 ≤ n) (hY : 1 ≤ Real.log n)
    (hN : 2 ≤ reSize eps p n ℓ)
    (hlog : 3 * Real.log eps + 3 * Real.log (reDelta eps p n ℓ) +
      4 * Real.log (Real.log n) ≤ Real.log n) : UNoise eps p n 1 ℓ := by
  have he0 : 0 < eps := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hY0 : 0 < Real.log n := by linarith
  have hlogY : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hY
  have hΔ := reDelta_pos (p := p) he hn ℓ
  refine ⟨hN, ?_, ?_⟩
  · rw [kre_effDelta_one hn, one_mul, le_div_iff₀ (pow_pos hY0 4)]
    apply (Real.log_le_log_iff (by positivity) hn0).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact hlog
  · rw [le_div_iff₀ (pow_pos hY0 2)]
    apply (Real.log_le_log_iff (by positivity) hn0).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith

theorem kre_curv_of_log {eps : ℝ} {p : ℕ → ℝ} {n ℓ : ℕ}
    (he : 1 ≤ eps) (hn : 1 ≤ n) (hY : 1 ≤ Real.log n)
    (hlog : Real.log n + 4 * Real.log (Real.log n) ≤
      3 * Real.log eps + 3 * Real.log (reDelta eps p n ℓ)) : UCurv eps p n 1 ℓ := by
  have he0 : 0 < eps := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hY0 : 0 < Real.log n := by linarith
  have hΔ := reDelta_pos (p := p) he hn ℓ
  unfold UCurv
  rw [kre_effDelta_one hn, one_mul]
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  exact hlog

/-- The accumulated logarithmic error in the noise recursion. -/
theorem kre_noise_log_bracket {eps : ℝ} {p : ℕ → ℝ} {n : ℕ}
    {cN CN Cu C0 c1 c2 c3 KL α : ℝ}
    (hF : UniformLayerFacts p n eps 1 cN CN Cu C0 c1 c2 c3 KL)
    (he : 1 ≤ eps) (hn : 1 ≤ n) (hcN : 0 < cN) (hCN : 0 < CN)
    (hlo : -α ≤ Real.log cN) (hhi : Real.log CN ≤ α)
    {ℓ : ℕ} (hℓ : ℓ ≤ uEnd eps p n 1) :
    ((2 : ℝ) ^ ℓ - 1) * (2 * Real.log eps - α) ≤ Real.log (reDelta eps p n ℓ) ∧
      Real.log (reDelta eps p n ℓ) ≤ ((2 : ℝ) ^ ℓ - 1) * (2 * Real.log eps + α) := by
  have he0 : 0 < eps := by linarith
  have hcast : ((2 ^ ℓ - 1 : ℕ) : ℝ) = (2 : ℝ) ^ ℓ - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  have hpow : 0 ≤ (2 : ℝ) ^ ℓ - 1 := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  have hl := Real.log_le_log (by positivity)
    (noise_le_reDelta hF hcN he hn ℓ hℓ)
  have hu := Real.log_le_log (reDelta_pos he hn ℓ)
    (reDelta_le_noise hF hCN he hn ℓ hℓ)
  rw [Real.log_pow, Real.log_mul hcN.ne' (by positivity), Real.log_pow, hcast] at hl
  rw [Real.log_pow, Real.log_mul hCN.ne' (by positivity), Real.log_pow, hcast] at hu
  norm_num only [Nat.cast_ofNat] at hl hu
  constructor
  · exact (mul_le_mul_of_nonneg_left (by linarith : 2 * Real.log eps - α ≤
      Real.log cN + 2 * Real.log eps) hpow).trans hl
  · exact hu.trans (mul_le_mul_of_nonneg_left (by linarith : Real.log CN +
      2 * Real.log eps ≤ 2 * Real.log eps + α) hpow)

/-- With margins on both sides of the noise bracket, layer `P` is the
first curvature layer and all preceding layers are noise layers. -/
theorem kre_exact_noise_start {eps : ℝ} {p : ℕ → ℝ} {n P : ℕ}
    {cN CN Cu C0 c1 c2 c3 KL α q : ℝ}
    (hF : UniformLayerFacts p n eps 1 cN CN Cu C0 c1 c2 c3 KL)
    (he : 1 ≤ eps) (hn : 2 ≤ n) (hY : 1 ≤ Real.log n)
    (hcN : 0 < cN) (hCN : 0 < CN) (hα : 0 ≤ α)
    (hρ : α ≤ 2 * Real.log eps) (hlo : -α ≤ Real.log cN) (hhi : Real.log CN ≤ α)
    (hq : Real.log n + 3 * Real.log eps = 3 * (2 * Real.log eps) * q)
    (hmlo : ((2 : ℝ) ^ P / 2 - 1) * (2 * Real.log eps + α) ≤
      (2 * Real.log eps) * (q - 1) - 4 / 3 * Real.log (Real.log n))
    (hmhi : (2 * Real.log eps) * (q - 1) + 4 / 3 * Real.log (Real.log n) ≤
      ((2 : ℝ) ^ P - 1) * (2 * Real.log eps - α)) :
    P ≤ uEnd eps p n 1 ∧ 2 ≤ reSize eps p n P ∧ UCurv eps p n 1 P ∧
      ((2 : ℝ) ^ P - 1) * (2 * Real.log eps - α) ≤ Real.log (reDelta eps p n P) ∧
      Real.log (reDelta eps p n P) ≤ ((2 : ℝ) ^ P - 1) * (2 * Real.log eps + α) := by
  have hn1 : 1 ≤ n := by omega
  have hP : P ≤ uEnd eps p n 1 := by
    by_contra h
    have hlt : uEnd eps p n 1 < P := by omega
    have hpow : (2 : ℝ) ^ (uEnd eps p n 1) ≤ (2 : ℝ) ^ P / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ← pow_succ]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hb := (kre_noise_log_bracket hF he hn1 hcN hCN hlo hhi le_rfl).2
    have hd : Real.log (reDelta eps p n (uEnd eps p n 1)) ≤
        ((2 : ℝ) ^ P / 2 - 1) * (2 * Real.log eps + α) := by
      exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
    have hnoise := kre_noise_of_log he hn1 hY (two_le_reSize_uEnd hF hn)
      (by nlinarith [hd, hmlo])
    exact not_UNoise_uEnd he hn1 hnoise
  have hb := kre_noise_log_bracket hF he hn1 hcN hCN hlo hhi hP
  have hNP : 2 ≤ reSize eps p n P := by
    rcases lt_or_eq_of_le hP with hlt | rfl
    · exact (UNoise_of_lt_uEnd hlt).1
    · exact two_le_reSize_uEnd hF hn
  exact ⟨hP, hNP, kre_curv_of_log he hn1 hY (by nlinarith [hb.1, hmhi]), hb⟩

end
end PGM
