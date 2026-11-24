import PLAStochastic.Index.CEPS.Jets.JF
import Mathlib.Analysis.Complex.Schwarz

/-!
# X8: Lipschitz continuity of the contour jets near the reference density

On the jet line `s = c + iy` (`c = cepsJetLine`) the integrand `w ↦ G_{j,m,n}(s, w)` is
holomorphic on the ball of radius `2ρ` about the reference transform `M^Λ(s)` and moves there by
at most `C (1 + ‖s‖)^j` (`cepsContour_integrand_data`). By the Schwarz lemma
(`norm_cepsJetIntegrand_sub_le`), for `‖w - M^Λ(s)‖ < 2ρ`,
`‖G(s, w) - G(s, M^Λ(s))‖ ≤ C (1 + ‖s‖)^j ‖w - M^Λ(s)‖ / (2ρ)`.

For a density `f` vanishing on `(-∞, 0)` with `f - f_Λ` in the weighted Sobolev class of order
`N ≥ j + 2`, integration by parts gives
`(1 + ‖s‖)^N ‖M^f(s) - M^Λ(s)‖ ≤ 2^N e^c ‖f - f_Λ‖_{N,η}`. Hence the difference of the
integrands is at most a constant times `‖f - f_Λ‖_{N,η} (1 + y²)⁻¹`, and the contour jet moves by
`O(‖f - f_Λ‖_{N,η})` (`cepsContourJet_lipschitz`).
-/

noncomputable section

open MeasureTheory Complex Metric

namespace PGM

/-- **Schwarz lemma for the contour integrands.** If `G` is holomorphic on `B(z₀, R)` and moves
by at most `A` there, then `‖G w - G z₀‖ ≤ A/R ‖w - z₀‖` on the ball. -/
theorem norm_sub_le_of_ball_osc {G : ℂ → ℂ} {z₀ w : ℂ} {R A : ℝ}
    (hd : DifferentiableOn ℂ G (ball z₀ R)) (hosc : ∀ z ∈ ball z₀ R, ‖G z - G z₀‖ ≤ A)
    (hw : w ∈ ball z₀ R) : ‖G w - G z₀‖ ≤ A / R * ‖w - z₀‖ := by
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd
    (fun z hz => by rw [mem_closedBall, dist_eq_norm]; exact hosc z hz) hw
  rwa [dist_eq_norm, dist_eq_norm] at h

/-- **Integral comparison on a tube.** If `G(y, ·)` is jointly continuous on the tube
`‖w - M₀(y)‖ < 2ρ`, `y ↦ G(y, M₀ y)` is integrable, `M` stays in the tube, and the integrands
differ by at most `A (1 + y²)⁻¹`, then the integrals differ by at most `A π`. -/
theorem norm_integral_sub_le_of_tube {G : ℝ → ℂ → ℂ} {M₀ M : ℝ → ℂ} {ρ A : ℝ}
    (hGc : ContinuousOn (fun p : ℝ × ℂ => G p.1 p.2) {p | ‖p.2 - M₀ p.1‖ < 2 * ρ})
    (hM₀ : Continuous M₀) (hM : Continuous M) (hρ : 0 < ρ)
    (hball : ∀ y, ‖M y - M₀ y‖ < 2 * ρ) (hint : Integrable fun y => G y (M₀ y))
    (hpt : ∀ y, ‖G y (M y) - G y (M₀ y)‖ ≤ A * (1 + y ^ 2)⁻¹) :
    ‖(∫ y, G y (M y)) - ∫ y, G y (M₀ y)‖ ≤ A * Real.pi := by
  have hc : ∀ F : ℝ → ℂ, Continuous F → (∀ y, ‖F y - M₀ y‖ < 2 * ρ) →
      Continuous fun y => G y (F y) := fun F hF hFb =>
    ContinuousOn.comp_continuous (s := {p : ℝ × ℂ | ‖p.2 - M₀ p.1‖ < 2 * ρ})
      (g := fun p : ℝ × ℂ => G p.1 p.2) hGc (continuous_id.prodMk hF) hFb
  have h₀ : ∀ y, ‖M₀ y - M₀ y‖ < 2 * ρ := fun y => by
    rw [sub_self, norm_zero]
    positivity
  have hbound : Integrable fun y : ℝ => A * (1 + y ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  have hdiff : Integrable fun y => G y (M y) - G y (M₀ y) :=
    hbound.mono' ((hc M hM hball).sub (hc M₀ hM₀ h₀)).aestronglyMeasurable (ae_of_all _ hpt)
  have hMi : Integrable fun y => G y (M y) :=
    (hint.add hdiff).congr (ae_of_all _ fun y => by simp)
  rw [← integral_sub hMi hint]
  refine (norm_integral_le_of_norm_le hbound (ae_of_all _ hpt)).trans_eq ?_
  rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- `(1 + ‖s‖)^j ‖Δ‖ ≤ B (1 + y²)⁻¹` on the line `s = c + iy` when `(1 + ‖s‖)^N ‖Δ‖ ≤ B` and
`j + 2 ≤ N`. -/
theorem one_add_pow_mul_le_of_decay {c y : ℝ} {j N : ℕ} (hN : j + 2 ≤ N) {Δ B : ℝ}
    (hΔ : 0 ≤ Δ) (h : (1 + ‖(c : ℂ) + y * I‖) ^ N * Δ ≤ B) :
    (1 + ‖(c : ℂ) + y * I‖) ^ j * Δ ≤ B * (1 + y ^ 2)⁻¹ := by
  set t := 1 + ‖(c : ℂ) + y * I‖ with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith [norm_nonneg ((c : ℂ) + y * I)]
  have hpos : 0 < t ^ N := by positivity
  have hpow : t ^ (j + 2) ≤ t ^ N := pow_le_pow_right₀ ht1 hN
  have hB : 0 ≤ B := (mul_nonneg hpos.le hΔ).trans h
  have h1 : Δ ≤ B * (t ^ N)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
    exact h
  have h2 : (t ^ N)⁻¹ ≤ (t ^ (j + 2))⁻¹ := inv_anti₀ (by positivity) hpow
  have h3 : t ^ j * (t ^ (j + 2))⁻¹ ≤ (1 + y ^ 2)⁻¹ := one_add_pow_div_le (c := c) (y := y) j
  calc t ^ j * Δ ≤ t ^ j * (B * (t ^ (j + 2))⁻¹) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hB)) (by positivity)
    _ = B * (t ^ j * (t ^ (j + 2))⁻¹) := by ring
    _ ≤ B * (1 + y ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h3 hB

/-- **Contour jets are Lipschitz near `f_Λ`.** For the contour jet `(j, m, n)`, a Sobolev order
`N ≥ j + 2` and a weight `η ≥ 0` there are `r₀ > 0` and `C ≥ 0` such that every density `f`
vanishing on `(-∞, 0)` with `f - f_Λ` in the Sobolev class and `‖f - f_Λ‖_{N,η} ≤ r₀` has
contour jet within `C ‖f - f_Λ‖_{N,η}` of that of `f_Λ`. -/
theorem cepsContourJet_lipschitz (j m n : ℕ) {N : ℕ} (hN : j + 2 ≤ N) {η : ℝ} (hη : 0 ≤ η) :
    ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ∀ f : ℝ → ℝ, (∀ x, x < 0 → f x = 0) →
      CepsSobolevClass N η (fun x => f x - cepsLambdaDensity x) →
      cepsSobolev N η (fun x => f x - cepsLambdaDensity x) ≤ r₀ →
      ‖cepsContourJetC cepsJetLine (cepsJetTransform f) j m n -
          cepsContourJetC cepsJetLine (cepsJetTransform cepsLambdaDensity) j m n‖ ≤
        C * cepsSobolev N η (fun x => f x - cepsLambdaDensity x) := by
  obtain ⟨ρ, C, hρ, hC, hMΛc, hGd, hGc, hosc, hint⟩ := cepsContour_integrand_data j m n
  have hc := cepsJetLine_pos
  have hline : ∀ y : ℝ, ((cepsJetLine : ℂ) + y * I).re = cepsJetLine := fun y => by simp
  have hB0 : 0 < 2 ^ N * Real.exp cepsJetLine := by positivity
  refine ⟨ρ / (2 ^ N * Real.exp cepsJetLine),
    (m.factorial : ℝ) * (2 * Real.pi)⁻¹ * (C / (2 * ρ) * (2 ^ N * Real.exp cepsJetLine) *
      Real.pi), div_pos hρ hB0, by positivity, fun f hfneg hφ hS => ?_⟩
  have hS0 := cepsSobolev_nonneg N η (fun x => f x - cepsLambdaDensity x)
  have hΛneg : ∀ x, x < 0 → cepsLambdaDensity x = 0 := fun x hx =>
    cepsLambdaDensity_of_nonpos hx.le
  have hφneg : ∀ x, x < 0 → f x - cepsLambdaDensity x = 0 := fun x hx => by
    rw [hfneg x hx, hΛneg x hx, sub_zero]
  have hφi : Integrable fun x => f x - cepsLambdaDensity x := hφ.integrable_self hη
  have hfi : Integrable f :=
    (hφi.add integrable_cepsLambdaDensity).congr (ae_of_all _ fun x => by simp)
  -- the transform difference on the jet line
  have hdecay : ∀ y : ℝ, (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ N *
      ‖cepsJetTransform f (cepsJetLine + y * I) -
        cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ ≤
      2 ^ N * Real.exp cepsJetLine *
        cepsSobolev N η (fun x => f x - cepsLambdaDensity x) := fun y => by
    have hs : 0 ≤ ((cepsJetLine : ℂ) + y * I).re := by rw [hline]; exact hc.le
    have h := norm_cepsJetTransform_le_sobolev hφ hη hφneg hs
    rw [hline] at h
    rwa [← cepsJetTransform_sub hfi integrable_cepsLambdaDensity hfneg hΛneg hs]
  have hball : ∀ y : ℝ, ‖cepsJetTransform f (cepsJetLine + y * I) -
      cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ < 2 * ρ := fun y => by
    have h1 : 1 ≤ (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ N :=
      one_le_pow₀ (by linarith [norm_nonneg ((cepsJetLine : ℂ) + y * I)])
    have h2 := (le_mul_of_one_le_left (norm_nonneg _) h1).trans (hdecay y)
    have h3 : 2 ^ N * Real.exp cepsJetLine *
        cepsSobolev N η (fun x => f x - cepsLambdaDensity x) ≤ ρ := by
      calc 2 ^ N * Real.exp cepsJetLine * cepsSobolev N η (fun x => f x - cepsLambdaDensity x)
          ≤ 2 ^ N * Real.exp cepsJetLine * (ρ / (2 ^ N * Real.exp cepsJetLine)) :=
            mul_le_mul_of_nonneg_left hS hB0.le
        _ = ρ := by field_simp
    linarith
  -- pointwise bound on the integrand difference (Schwarz lemma)
  have hpt : ∀ y : ℝ,
      ‖cepsJetIntegrand j m n (cepsJetLine + y * I) (cepsJetTransform f (cepsJetLine + y * I)) -
        cepsJetIntegrand j m n (cepsJetLine + y * I)
          (cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I))‖ ≤
      C / (2 * ρ) * (2 ^ N * Real.exp cepsJetLine) *
        cepsSobolev N η (fun x => f x - cepsLambdaDensity x) * (1 + y ^ 2)⁻¹ := fun y => by
    have hmem : cepsJetTransform f (cepsJetLine + y * I) ∈
        ball (cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)) (2 * ρ) := by
      rw [mem_ball, dist_eq_norm]
      exact hball y
    have h := norm_sub_le_of_ball_osc (hGd y) (hosc y) hmem
    have hw := one_add_pow_mul_le_of_decay hN (norm_nonneg _) (hdecay y)
    calc _ ≤ C * (1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ j / (2 * ρ) *
          ‖cepsJetTransform f (cepsJetLine + y * I) -
            cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ := h
      _ = C / (2 * ρ) * ((1 + ‖(cepsJetLine : ℂ) + y * I‖) ^ j *
          ‖cepsJetTransform f (cepsJetLine + y * I) -
            cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖) := by ring
      _ ≤ C / (2 * ρ) * (2 ^ N * Real.exp cepsJetLine *
          cepsSobolev N η (fun x => f x - cepsLambdaDensity x) * (1 + y ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by ring
  have hMfc : Continuous fun y : ℝ => cepsJetTransform f (cepsJetLine + y * I) :=
    (continuousOn_cepsJetTransform hfi hfneg).comp_continuous (by fun_prop)
      (fun y => by simp only [Set.mem_ofPred_eq, hline]; exact hc.le)
  have hInt := norm_integral_sub_le_of_tube
    (G := fun y w => cepsJetIntegrand j m n (cepsJetLine + y * I) w)
    (M₀ := fun y => cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I))
    (M := fun y => cepsJetTransform f (cepsJetLine + y * I)) hGc hMΛc hMfc hρ hball hint hpt
  -- the contour jets
  have hjet : cepsContourJetC cepsJetLine (cepsJetTransform f) j m n -
      cepsContourJetC cepsJetLine (cepsJetTransform cepsLambdaDensity) j m n =
      (m.factorial : ℂ) * (2 * Real.pi : ℂ)⁻¹ *
        ((∫ y : ℝ, cepsJetIntegrand j m n (cepsJetLine + y * I)
            (cepsJetTransform f (cepsJetLine + y * I))) -
          ∫ y : ℝ, cepsJetIntegrand j m n (cepsJetLine + y * I)
            (cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I))) := by
    simp only [cepsContourJetC]
    ring
  have h2π : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hjet, norm_mul, norm_mul, norm_inv, norm_natCast, h2π]
  calc _ ≤ (m.factorial : ℝ) * (2 * Real.pi)⁻¹ *
        (C / (2 * ρ) * (2 ^ N * Real.exp cepsJetLine) *
          cepsSobolev N η (fun x => f x - cepsLambdaDensity x) * Real.pi) :=
        mul_le_mul_of_nonneg_left hInt (by positivity)
    _ = _ := by ring

end PGM
