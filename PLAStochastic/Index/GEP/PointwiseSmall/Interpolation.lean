import PLAStochastic.Index.GEP.DirectTerm.DiscInterpolation
import PLAStochastic.Index.GEP.DirectTerm.OfRawDisc

/-!
# WP4 leaves `PointwiseSmall`, `QuadResponse`: interpolation of small real increments

`DiscInterp` applied to `h(z) = g(z) - g(0)`: if `g` is holomorphic on a fixed disc with
`‖g‖ ≤ K₁ ε^p` there and `‖g(t) - g(0)‖ ≤ K₂ ε^{-b}` on `[0, R/8]`, then
`‖g'(0)‖ ≤ K₃ ε^{-b} (1 + log ε)²` (`pw_interp_small`).  Here `δ = (|K₂| + 1) ε^{-b}` and
`M = 2|K₁| ε^p + δ`, so `log(M/δ) ≤ log(1 + 2|K₁|) + (p + b) log ε`.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter Topology Metric

theorem pw_log_le {eps c : ℝ} (heps : 1 ≤ eps) (hc : 0 ≤ c) (p : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    Real.log (1 + c * (eps ^ p * eps ^ b)) ≤
      Real.log (1 + c) + (p + b) * Real.log eps := by
  have heps0 : 0 < eps := by linarith
  have h1 : 1 ≤ eps ^ p * eps ^ b :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ heps) (Real.one_le_rpow heps hb)
  have h2 : 1 + c * (eps ^ p * eps ^ b) ≤ (1 + c) * (eps ^ p * eps ^ b) := by nlinarith
  have hpos : 0 < 1 + c * (eps ^ p * eps ^ b) := by positivity
  calc Real.log (1 + c * (eps ^ p * eps ^ b)) ≤ Real.log ((1 + c) * (eps ^ p * eps ^ b)) :=
        Real.log_le_log hpos h2
    _ = Real.log (1 + c) + (p * Real.log eps + b * Real.log eps) := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_rpow heps0]
    _ = Real.log (1 + c) + (p + b) * Real.log eps := by ring

/-- **Interpolation of a small real increment.** -/
theorem pw_interp_small (hI : DiscInterp) {R K₁ K₂ b : ℝ} (p : ℕ) (hR : 0 < R) (hb : 0 ≤ b) :
    ∃ K₃ : ℝ, 0 ≤ K₃ ∧ ∀ (g : ℂ → ℂ) (eps : ℝ), 1 ≤ eps →
      DifferentiableOn ℂ g (ball 0 R) → (∀ z ∈ ball (0 : ℂ) R, ‖g z‖ ≤ K₁ * eps ^ p) →
      (∀ t : ℝ, 0 ≤ t → t ≤ R / 8 → ‖g t - g 0‖ ≤ K₂ * eps ^ (-b)) →
        ‖deriv g 0‖ ≤ K₃ * eps ^ (-b) * (1 + Real.log eps) ^ 2 := by
  obtain ⟨KI, hKI, hI⟩ := hI
  set c : ℝ := 2 * |K₁| with hc
  set C : ℝ := 1 + Real.log (1 + c) + p + b with hC
  have hc0 : 0 ≤ c := by positivity
  have hlc : 0 ≤ Real.log (1 + c) := Real.log_nonneg (by linarith)
  have hC0 : 0 ≤ C := by positivity
  refine ⟨KI * (|K₂| + 1) * C ^ 2 / R, by positivity, fun g eps heps hg hball hseg => ?_⟩
  have heps0 : 0 < eps := by linarith
  have hle0 : 0 ≤ Real.log eps := Real.log_nonneg heps
  set h : ℂ → ℂ := fun z => g z - g 0 with hh
  have hdh : deriv h 0 = deriv g 0 := by
    rw [hh, deriv_sub_const]
  have hep : 0 < eps ^ (-b) := Real.rpow_pos_of_pos heps0 _
  set δ := (|K₂| + 1) * eps ^ (-b) with hδ
  have hδ0 : 0 < δ := by positivity
  set M := c * eps ^ p + δ with hM
  have hδM : δ ≤ M := by
    have : 0 ≤ c * eps ^ p := by positivity
    rw [hM]; linarith
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hg0 : ‖g 0‖ ≤ |K₁| * eps ^ p :=
    (hball 0 h0).trans (by gcongr; exact le_abs_self _)
  have hb' : ∀ z ∈ ball (0 : ℂ) R, ‖h z‖ ≤ M := by
    intro z hz
    have hgz : ‖g z‖ ≤ |K₁| * eps ^ p := (hball z hz).trans (by gcongr; exact le_abs_self _)
    calc ‖h z‖ ≤ ‖g z‖ + ‖g 0‖ := norm_sub_le _ _
      _ ≤ c * eps ^ p := by rw [hc]; linarith
      _ ≤ M := by rw [hM]; linarith
  have hs' : ∀ t : ℝ, 0 ≤ t → t ≤ R / 8 → ‖h t‖ ≤ δ := fun t ht0 ht1 =>
    (hseg t ht0 ht1).trans (by
      rw [hδ]
      gcongr
      linarith [le_abs_self K₂])
  have hdiff : DifferentiableOn ℂ h (ball 0 R) := hg.sub_const _
  have hmain := hI h R M δ hR hδ0 hδM hdiff hb' hs'
  rw [hdh] at hmain
  -- the logarithm
  have hMδ : M / δ = 1 + c * (eps ^ p * eps ^ b) / (|K₂| + 1) := by
    rw [hM, hδ, Real.rpow_neg heps0.le]
    have : 0 < eps ^ b := Real.rpow_pos_of_pos heps0 _
    field_simp
    ring
  have hMδ' : M / δ ≤ 1 + c * (eps ^ p * eps ^ b) := by
    rw [hMδ]
    have h1 : 0 ≤ c * (eps ^ p * eps ^ b) := by positivity
    have h2 : c * (eps ^ p * eps ^ b) / (|K₂| + 1) ≤ c * (eps ^ p * eps ^ b) :=
      div_le_self h1 (by linarith [abs_nonneg K₂])
    linarith
  have hMδ1 : 1 ≤ M / δ := by rw [le_div_iff₀ hδ0, one_mul]; exact hδM
  have hlog : Real.log (M / δ) ≤ Real.log (1 + c) + (p + b) * Real.log eps :=
    (Real.log_le_log (by linarith) hMδ').trans (pw_log_le heps hc0 p hb)
  have hl0 : 0 ≤ Real.log (M / δ) := Real.log_nonneg hMδ1
  have hsq : (1 + Real.log (M / δ)) ^ 2 ≤ C ^ 2 * (1 + Real.log eps) ^ 2 := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    rw [hC]
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith
  calc ‖deriv g 0‖ ≤ KI * δ * (1 + Real.log (M / δ)) ^ 2 / R := hmain
    _ ≤ KI * δ * (C ^ 2 * (1 + Real.log eps) ^ 2) / R := by gcongr
    _ = KI * (|K₂| + 1) * C ^ 2 / R * eps ^ (-b) * (1 + Real.log eps) ^ 2 := by
        rw [hδ]; ring

end

end PGM
