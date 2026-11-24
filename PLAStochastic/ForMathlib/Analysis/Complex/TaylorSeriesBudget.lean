import PLAStochastic.ForMathlib.Analysis.Complex.PolynomialTaylorDisc
import PLAStochastic.ForMathlib.Analysis.Asymptotics.SeriesApprox

/-! # Formal Taylor series with reciprocal-polynomial-disc budgets -/

noncomputable section
open Complex Set Metric Finset PowerSeries
namespace PGM

def complexTaylorSeries (f : ℂ → ℂ) (c : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n f c

theorem truncEval_complexTaylorSeries (f : ℂ → ℂ) (N : ℕ) (b : ℝ) :
    truncEval (complexTaylorSeries f 0) N b = complexTaylorSum f (N + 1) 0 b := by
  unfold truncEval complexTaylorSeries complexTaylorSum
  simp only [coeff_mk, sub_zero]
  apply sum_congr rfl
  intro j _
  ring

def complexTaylorBudgetConstant (N : ℕ) (R K : ℝ) : ℝ :=
  ∑ j ∈ range (N + 2), (j.factorial : ℝ) * K / (R / 4) ^ j

theorem complexTaylorBudgetConstant_nonneg (N : ℕ) {R K : ℝ}
    (hR : 0 < R) (hK : 0 ≤ K) : 0 ≤ complexTaylorBudgetConstant N R K := by
  unfold complexTaylorBudgetConstant
  positivity

theorem seriesApprox_of_polynomial_disc {f : ℂ → ℂ} {R H K : ℝ}
    (hR : 0 < R) (hH : 1 ≤ H) (hK : 0 ≤ K) (q N : ℕ)
    (hd : DifferentiableOn ℂ f (ball 0 (R / H)))
    (hm : ∀ b ∈ ball (0 : ℂ) (R / H), ‖f b‖ ≤ K * H ^ q)
    {b : ℝ} (hb : 0 ≤ b) (hbs : (b : ℂ) ∈ ball (0 : ℂ) ((R / H) / 2)) :
    SeriesApprox (f b) (complexTaylorSeries f 0) N b
      (complexTaylorBudgetConstant N R K * H ^ (N + 1 + q)) := by
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hterm (j : ℕ) (hj : j < N + 2) :
      (j.factorial : ℝ) * K / (R / 4) ^ j ≤ complexTaylorBudgetConstant N R K := by
    unfold complexTaylorBudgetConstant
    exact single_le_sum (f := fun i : ℕ => (i.factorial : ℝ) * K / (R / 4) ^ i)
      (fun i _ => by positivity) (mem_range.mpr hj)
  have hbound (j : ℕ) :
      ‖iteratedDeriv j f 0‖ ≤ ((j.factorial : ℝ) * K / (R / 4) ^ j) * H ^ (j + q) := by
    have ht := norm_iteratedDeriv_le_of_ball_half (z := (0 : ℂ)) j (div_pos hR hH0) hd hm
      (mem_ball_self (half_pos (div_pos hR hH0)))
    apply ht.trans_eq
    rw [show (R / H / 4) ^ j = (R / 4) ^ j / H ^ j by
      rw [show R / H / 4 = R / 4 / H by ring, div_pow], div_div_eq_mul_div, pow_add]
    ring
  refine ⟨fun j hj => ?_, ?_⟩
  · simp only [complexTaylorSeries, coeff_mk, norm_mul]
    have hfac : ‖(j.factorial : ℂ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_natCast]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos j)
    calc _ ≤ ‖iteratedDeriv j f 0‖ := by
            have := mul_le_mul_of_nonneg_right hfac (norm_nonneg (iteratedDeriv j f 0))
            simpa only [one_mul] using this
      _ ≤ _ := (hbound j).trans (mul_le_mul
        (hterm j (by omega)) (pow_le_pow_right₀ hH (by omega)) (by positivity)
          (complexTaylorBudgetConstant_nonneg N hR hK))
  · rw [truncEval_complexTaylorSeries]
    have ht' := norm_sub_complexTaylorSum_le_of_ball (N + 1) (div_pos hR hH0) hd hm hbs
    simp only [sub_zero, norm_real, Real.norm_eq_abs, abs_of_nonneg hb] at ht'
    apply ht'.trans
    calc
      (((N + 1).factorial : ℝ) * (K * H ^ q) / (R / H / 4) ^ (N + 1)) * b ^ (N + 1) =
          (((N + 1).factorial : ℝ) * K / (R / 4) ^ (N + 1)) * H ^ (N + 1 + q) * b ^ (N + 1) := by
        rw [show (R / H / 4) ^ (N + 1) = (R / 4) ^ (N + 1) / H ^ (N + 1) by
          rw [show R / H / 4 = R / 4 / H by ring, div_pow], div_div_eq_mul_div, pow_add]
        ring
      _ ≤ _ := by gcongr; exact hterm (N + 1) (by omega)

theorem SeriesApprox.sub {z w : ℂ} {F G : PowerSeries ℂ} {N : ℕ} {b K L : ℝ}
    (hz : SeriesApprox z F N b K) (hw : SeriesApprox w G N b L) :
    SeriesApprox (z - w) (F - G) N b (K + L) := by
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [map_sub]
    exact (norm_sub_le _ _).trans (add_le_add (hz.1 j hj) (hw.1 j hj))
  · rw [truncEval_sub]
    rw [show z - w - (truncEval F N b - truncEval G N b) =
      (z - truncEval F N b) - (w - truncEval G N b) by ring]
    exact ((norm_sub_le _ _).trans (add_le_add hz.2 hw.2)).trans_eq (by ring)

end PGM
