import PLAStochastic.Index.GEP.QuadResponse.SecondDerivative
import PLAStochastic.Index.GEP.PointwiseSmall.LebesguePoints

/-!
# WP4 leaf `QuadResponse`: the `O(1)` derivative at `0` (PD §7)

`quad_deriv_zero_bound`: a holomorphic `H` on a fixed disc with `‖H‖ ≤ K ε^p` on the disc and
`‖H(t)‖ ≤ K ε^{-βU} + K t` on the real segment has `‖H'(0)‖ ≤ K'` uniformly in `ε ≥ e0`.  The
second derivative is `O((1 + log ε)⁴)` on `[0, R/32]` (`quad_second_deriv`, `quad_second_bound`),
and one-sided Taylor with `u = ε^{-βU/2}` gives
`‖H'(0)‖ ≤ (2 K ε^{-βU} + K u)/u + u O(log⁴ ε) = O(1)`.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter Topology Metric

theorem quad_log_le {eps c : ℝ} (heps : 1 ≤ eps) (hc : 0 ≤ c) (p : ℕ) :
    Real.log (1 + c * eps ^ p) ≤ Real.log (1 + c) + p * Real.log eps := by
  have heps0 : 0 < eps := by linarith
  have h1 : 1 ≤ eps ^ p := one_le_pow₀ heps
  have h2 : 1 + c * eps ^ p ≤ (1 + c) * eps ^ p := by nlinarith
  have hpos : 0 < 1 + c * eps ^ p := by positivity
  calc Real.log (1 + c * eps ^ p) ≤ Real.log ((1 + c) * eps ^ p) := Real.log_le_log hpos h2
    _ = Real.log (1 + c) + p * Real.log eps := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]

/-- The `(1 + log ε)⁴` form of the second-derivative bound. -/
theorem quad_second_bound {KI R δ₀ Kb eps M δ₁ : ℝ} (p : ℕ) (hKI : 0 < KI) (hR : 0 < R)
    (hδ₀ : 0 < δ₀) (hKb : 0 ≤ Kb) (heps : 1 ≤ eps) (hM : M = Kb * eps ^ p + δ₀)
    (hδ₁ : δ₁ = KI * δ₀ * (1 + Real.log (M / δ₀)) ^ 2 / (R / 2)) :
    KI * δ₁ * (1 + Real.log (max (M / (R / 4)) δ₁ / δ₁)) ^ 2 / (R / 4) ≤
      8 * KI ^ 2 * δ₀ * (1 + Real.log (1 + Kb / δ₀) + p) ^ 2 *
        (1 + Real.log (1 + 2 / KI * (Kb / δ₀ + 1)) + p) ^ 2 / R ^ 2 * (1 + Real.log eps) ^ 4 := by
  have heps0 : 0 < eps := by linarith
  have hl0 : 0 ≤ Real.log eps := Real.log_nonneg heps
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hep : 1 ≤ eps ^ p := one_le_pow₀ heps
  set L₀ := Real.log (1 + Kb / δ₀) with hL₀
  set c₂ := 2 / KI * (Kb / δ₀ + 1) with hc₂
  set L₂ := Real.log (1 + c₂) with hL₂
  have hL₀0 : 0 ≤ L₀ := Real.log_nonneg (by rw [le_add_iff_nonneg_right]; positivity)
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hL₂0 : 0 ≤ L₂ := Real.log_nonneg (by linarith)
  have hM0 : 0 < M := by rw [hM]; positivity
  have hMδ : M / δ₀ = 1 + Kb / δ₀ * eps ^ p := by
    rw [hM, add_div, div_self hδ₀.ne', mul_div_right_comm, add_comm]
  have hMδ1 : 1 ≤ M / δ₀ := by
    rw [hMδ]
    have : 0 ≤ Kb / δ₀ * eps ^ p := by positivity
    linarith
  have hlogM0 : 0 ≤ Real.log (M / δ₀) := Real.log_nonneg hMδ1
  have hL1 : 0 < 1 + Real.log (M / δ₀) := by linarith
  have hL1' : (1 + Real.log (M / δ₀)) ^ 2 ≠ 0 := by positivity
  have hδ₁0 : 0 < δ₁ := by rw [hδ₁]; positivity
  -- (1) the logarithm of `M/δ₀`
  have hlogM : Real.log (M / δ₀) ≤ L₀ + p * Real.log eps := by
    rw [hMδ]; exact quad_log_le heps (by positivity) p
  have hA : 1 + Real.log (M / δ₀) ≤ (1 + L₀ + p) * (1 + Real.log eps) := by nlinarith
  have hA2 : (1 + Real.log (M / δ₀)) ^ 2 ≤ ((1 + L₀ + p) * (1 + Real.log eps)) ^ 2 :=
    pow_le_pow_left₀ hL1.le hA 2
  -- (2) the bound of `δ₁`
  have hδ₁le : δ₁ ≤ KI * δ₀ * ((1 + L₀ + p) * (1 + Real.log eps)) ^ 2 * 2 / R := by
    calc δ₁ = KI * δ₀ * (1 + Real.log (M / δ₀)) ^ 2 * 2 / R := by rw [hδ₁, div_div_eq_mul_div]
      _ ≤ KI * δ₀ * ((1 + L₀ + p) * (1 + Real.log eps)) ^ 2 * 2 / R := by gcongr
  -- (3) the ratio
  have hone : 1 ≤ (1 + Real.log (M / δ₀)) ^ 2 := one_le_pow₀ (by linarith)
  have hratio : max (M / (R / 4)) δ₁ / δ₁ ≤ 1 + c₂ * eps ^ p := by
    have h1 : max (M / (R / 4)) δ₁ ≤ M / (R / 4) + δ₁ :=
      max_le (le_add_of_nonneg_right hδ₁0.le) (le_add_of_nonneg_left (by positivity))
    have h2 : M / (R / 4) / δ₁ ≤ c₂ * eps ^ p := by
      have e : M / (R / 4) / δ₁ = 2 * M / (KI * δ₀ * (1 + Real.log (M / δ₀)) ^ 2) := by
        rw [hδ₁]
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)]
      have h3 : 2 * M ≤ c₂ * eps ^ p * (KI * δ₀) := by
        rw [hM, hc₂]
        have e2 : 2 / KI * (Kb / δ₀ + 1) * eps ^ p * (KI * δ₀) =
            2 * (Kb * eps ^ p + δ₀ * eps ^ p) := by
          field_simp
        rw [e2]
        have := le_mul_of_one_le_right hδ₀.le hep
        linarith
      calc 2 * M ≤ c₂ * eps ^ p * (KI * δ₀) := h3
        _ = c₂ * eps ^ p * (KI * δ₀) * 1 := (mul_one _).symm
        _ ≤ c₂ * eps ^ p * (KI * δ₀) * (1 + Real.log (M / δ₀)) ^ 2 := by gcongr
        _ = c₂ * eps ^ p * (KI * δ₀ * (1 + Real.log (M / δ₀)) ^ 2) := by ring
    calc max (M / (R / 4)) δ₁ / δ₁ ≤ (M / (R / 4) + δ₁) / δ₁ := by gcongr
      _ = M / (R / 4) / δ₁ + 1 := by rw [add_div, div_self hδ₁0.ne']
      _ ≤ c₂ * eps ^ p + 1 := by linarith
      _ = 1 + c₂ * eps ^ p := add_comm _ _
  have hlog2 : Real.log (max (M / (R / 4)) δ₁ / δ₁) ≤ L₂ + p * Real.log eps := by
    have hpos : 0 < max (M / (R / 4)) δ₁ / δ₁ := by positivity
    exact (Real.log_le_log hpos hratio).trans (quad_log_le heps hc₂0 p)
  have hlog20 : 0 ≤ Real.log (max (M / (R / 4)) δ₁ / δ₁) :=
    Real.log_nonneg ((one_le_div hδ₁0).2 (le_max_right _ _))
  have hB : 1 + Real.log (max (M / (R / 4)) δ₁ / δ₁) ≤ (1 + L₂ + p) * (1 + Real.log eps) := by
    nlinarith
  have hB2 : (1 + Real.log (max (M / (R / 4)) δ₁ / δ₁)) ^ 2 ≤
      ((1 + L₂ + p) * (1 + Real.log eps)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hB 2
  -- (5) combine
  calc KI * δ₁ * (1 + Real.log (max (M / (R / 4)) δ₁ / δ₁)) ^ 2 / (R / 4)
      ≤ KI * (KI * δ₀ * ((1 + L₀ + p) * (1 + Real.log eps)) ^ 2 * 2 / R) *
          ((1 + L₂ + p) * (1 + Real.log eps)) ^ 2 / (R / 4) := by gcongr
    _ = 8 * KI ^ 2 * δ₀ * (1 + L₀ + p) ^ 2 * (1 + L₂ + p) ^ 2 / R ^ 2 * (1 + Real.log eps) ^ 4 := by
        field_simp
        ring

/-- **The `O(1)` bound of `H'(0)`** (PD §7). -/
theorem quad_deriv_zero_bound (hI : DiscInterp) {R Kb Kd Kq : ℝ} (p : ℕ) (hR : 0 < R)
    (hR1 : R ≤ 1) (hKb : 0 ≤ Kb) (hKd : 0 ≤ Kd) (hKq : 0 ≤ Kq) {βU : ℝ} (hβU : 0 < βU) :
    ∃ K e0 : ℝ, 0 ≤ K ∧ 1 ≤ e0 ∧ ∀ (H : ℂ → ℂ) (eps : ℝ), e0 ≤ eps →
      DifferentiableOn ℂ H (ball 0 R) → (∀ z ∈ ball (0 : ℂ) R, ‖H z‖ ≤ Kb * eps ^ p) →
      (∀ t : ℝ, 0 ≤ t → t ≤ R / 8 → ‖H t‖ ≤ Kd * eps ^ (-βU) + Kq * t) →
      ‖deriv H 0‖ ≤ K := by
  obtain ⟨KI, hKI, hsecond⟩ := quad_second_deriv hI
  set δ₀ : ℝ := Kd + Kq + 1 with hδ₀
  have hδ₀0 : 0 < δ₀ := by positivity
  set Kq2 : ℝ := 8 * KI ^ 2 * δ₀ * (1 + Real.log (1 + Kb / δ₀) + p) ^ 2 *
    (1 + Real.log (1 + 2 / KI * (Kb / δ₀ + 1)) + p) ^ 2 / R ^ 2 with hKq2
  have hKq20 : 0 ≤ Kq2 := by
    rw [hKq2]
    positivity
  set m : ℝ := max 1 (2 / (βU / 4)) with hm
  have hm0 : 0 < m := lt_max_of_lt_left one_pos
  set eu : ℝ := max 1 ((32 / R) ^ (2 / βU)) with heu
  refine ⟨2 * Kd + Kq + Kq2 * (16 * m ^ 4), eu, by positivity, le_max_left _ _, ?_⟩
  intro H eps heps hH hHb hHs
  have heps1 : 1 ≤ eps := (le_max_left _ _).trans heps
  have heps0 : 0 < eps := by linarith
  have hl0 : 0 ≤ Real.log eps := Real.log_nonneg heps1
  -- the constant segment bound and the disc bound
  have hpow1 : eps ^ (-βU) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos heps1 (by linarith)
  have hs0 : ∀ t : ℝ, 0 ≤ t → t ≤ R / 8 → ‖H t‖ ≤ δ₀ := by
    intro t ht0 ht1
    refine (hHs t ht0 ht1).trans ?_
    rw [hδ₀]
    have h1 : Kd * eps ^ (-βU) ≤ Kd := by
      calc Kd * eps ^ (-βU) ≤ Kd * 1 := by gcongr
        _ = Kd := mul_one _
    have h2 : Kq * t ≤ Kq := by
      calc Kq * t ≤ Kq * 1 := by gcongr; linarith
        _ = Kq := mul_one _
    linarith
  set Mb : ℝ := Kb * eps ^ p + δ₀ with hMb
  have hb0 : ∀ z ∈ ball (0 : ℂ) R, ‖H z‖ ≤ Mb := fun z hz => by
    rw [hMb]; linarith [hHb z hz]
  have hδM : δ₀ ≤ Mb := by
    rw [hMb]
    have : 0 ≤ Kb * eps ^ p := by positivity
    linarith
  -- the second derivative on `[0, R/32]`
  have hH'' : ∀ s : ℝ, 0 ≤ s → s ≤ R / 32 →
      ‖deriv (deriv H) s‖ ≤ Kq2 * (1 + Real.log eps) ^ 4 := by
    intro s hs0' hs1
    refine (hsecond H R Mb δ₀ hR hδ₀0 hδM hH hb0 hs0 s hs0' hs1).trans ?_
    exact quad_second_bound p hKI hR hδ₀0 hKb heps1 hMb rfl
  -- the Taylor point `u = ε^{-βU/2}`
  set u : ℝ := eps ^ (-(βU / 2)) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos heps0 _
  have hu1 : u ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos heps1 (by linarith)
  have huR : u ≤ R / 32 := by
    have h32 : (0 : ℝ) < 32 / R := by positivity
    have he : (32 / R) ^ (2 / βU) ≤ eps := (le_max_right _ _).trans heps
    have h1 : 32 / R ≤ eps ^ (βU / 2) := by
      have := Real.rpow_le_rpow (by positivity) he (by positivity : (0 : ℝ) ≤ βU / 2)
      rwa [← Real.rpow_mul h32.le, show 2 / βU * (βU / 2) = 1 by field_simp, Real.rpow_one] at this
    have h2 : 0 < eps ^ (βU / 2) := Real.rpow_pos_of_pos heps0 _
    rw [hu, Real.rpow_neg heps0.le, show R / 32 = (32 / R)⁻¹ by rw [inv_div]]
    exact inv_anti₀ h32 h1
  have huR' : u < R := by linarith
  have htay := quad_taylor hu0 huR' hH (fun s hs0' hs1 => hH'' s hs0' (hs1.trans huR))
  -- the increment
  have hHu : ‖H u - H 0‖ ≤ 2 * Kd * eps ^ (-βU) + Kq * u := by
    have h1 := hHs u hu0.le (by linarith)
    have h2 := hHs 0 le_rfl (by positivity)
    simp only [Complex.ofReal_zero, mul_zero, add_zero] at h2
    calc ‖H u - H 0‖ ≤ ‖H u‖ + ‖H 0‖ := norm_sub_le _ _
      _ ≤ (Kd * eps ^ (-βU) + Kq * u) + Kd * eps ^ (-βU) := add_le_add h1 h2
      _ = 2 * Kd * eps ^ (-βU) + Kq * u := by ring
  have hsplit : eps ^ (-βU) = u * u := by
    rw [hu, ← Real.rpow_add heps0]; congr 1; ring
  have hinc : ‖H u - H 0‖ / u ≤ 2 * Kd + Kq := by
    rw [div_le_iff₀ hu0]
    refine hHu.trans ?_
    rw [hsplit]
    have : 2 * Kd * (u * u) ≤ 2 * Kd * u := by
      have h0 : 0 ≤ 2 * Kd * u := by positivity
      nlinarith [mul_nonneg h0 (sub_nonneg.2 hu1)]
    linarith
  -- the log factor
  have hlog4 : (1 + Real.log eps) ^ 4 * u ≤ 16 * m ^ 4 := by
    have h := pw_log_sq_le_rpow (a := βU / 4) (by positivity) heps1
    rw [← hm] at h
    have h2 : ((1 + Real.log eps) ^ 2) ^ 2 ≤ (4 * m ^ 2 * eps ^ (βU / 4)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h 2
    have e : (4 * m ^ 2 * eps ^ (βU / 4)) ^ 2 * u = 16 * m ^ 4 := by
      rw [hu, mul_pow, ← Real.rpow_natCast (eps ^ (βU / 4)), ← Real.rpow_mul heps0.le,
        mul_assoc, ← Real.rpow_add heps0]
      rw [show βU / 4 * ((2 : ℕ) : ℝ) + -(βU / 2) = 0 by push_cast; ring, Real.rpow_zero, mul_one]
      ring
    calc (1 + Real.log eps) ^ 4 * u = ((1 + Real.log eps) ^ 2) ^ 2 * u := by ring
      _ ≤ (4 * m ^ 2 * eps ^ (βU / 4)) ^ 2 * u := by gcongr
      _ = 16 * m ^ 4 := e
  have htay' : ‖deriv H 0‖ ≤ ‖H u - H 0‖ / u + Kq2 * ((1 + Real.log eps) ^ 4 * u) := by
    rw [← mul_assoc]; exact htay
  calc ‖deriv H 0‖ ≤ ‖H u - H 0‖ / u + Kq2 * ((1 + Real.log eps) ^ 4 * u) := htay'
    _ ≤ (2 * Kd + Kq) + Kq2 * (16 * m ^ 4) := by gcongr

end

end PGM
