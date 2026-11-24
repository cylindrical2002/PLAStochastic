import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.Bulk

/-! # A fixed polynomial budget for the genuine scalar bulk tails -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1600000

theorem kernel_spectral_pair_polynomial {D k w a N : ℝ}
    (hD : 0 ≤ D) (hk : 0 ≤ k) (hw : 1 ≤ w) :
    ((D / a) * (1 + 3 * Real.sqrt (2 * D * w))) ^ 2 *
      Real.exp (-(k * (N - 8) / (4 * w ^ 2))) ≤
        (D ^ 2 * (2 + 36 * D) * Real.exp (2 * k)) * w * a⁻¹ ^ 2 *
          Real.exp (-(k / (4 * w ^ 2)) * N) := by
  have hw0 : 0 < w := by linarith
  have hs : Real.sqrt (2 * D * w) ^ 2 = 2 * D * w := Real.sq_sqrt (by positivity)
  have hsbound : (1 + 3 * Real.sqrt (2 * D * w)) ^ 2 ≤ (2 + 36 * D) * w := by
    nlinarith [sq_nonneg (1 - 3 * Real.sqrt (2 * D * w))]
  have hexp : -(k * (N - 8) / (4 * w ^ 2)) ≤ 2 * k + (-(k / (4 * w ^ 2)) * N) := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * w ^ 2 by positivity)).mp
    field_simp
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ w ^ 2 by nlinarith) hk
    nlinarith
  have hcoef : ((D / a) * (1 + 3 * Real.sqrt (2 * D * w))) ^ 2 ≤
      D ^ 2 * a⁻¹ ^ 2 * ((2 + 36 * D) * w) := by
    have hh := mul_le_mul_of_nonneg_left hsbound (sq_nonneg (D / a))
    rw [mul_pow]
    exact hh.trans_eq (by simp only [div_eq_mul_inv]; ring)
  have hh := mul_le_mul hcoef (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _)
    (show 0 ≤ D ^ 2 * a⁻¹ ^ 2 * ((2 + 36 * D) * w) by positivity)
  apply hh.trans_eq
  rw [Real.exp_add]
  ring

theorem kernel_small_pair_polynomial {D θ ζ t c N a : ℝ}
    (ha : 0 < a) (halo : a ≤ 1 / 2) (hc : 0 < c) (hN : 1 ≤ N) :
    (D * Real.exp θ / a) ^ 2 * Real.exp (ζ * t - c * N / a) ≤
      ((D * Real.exp θ) ^ 2 * (8 / c ^ 2) * Real.exp (ζ * t)) * Real.exp (-c * N) := by
  have hh := mul_le_mul_of_nonneg_left (kernel_small_slope_inverse_square ha halo hc hN)
    (show 0 ≤ (D * Real.exp θ) ^ 2 * Real.exp (ζ * t) by positivity)
  have he : (D * Real.exp θ / a) ^ 2 * Real.exp (ζ * t - c * N / a) =
      ((D * Real.exp θ) ^ 2 * Real.exp (ζ * t)) * (a⁻¹ ^ 2 * Real.exp (-c * N / a)) := by
    rw [show ζ * t - c * N / a = ζ * t + (-c * N / a) by ring, Real.exp_add]
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  exact hh.trans_eq (by ring)

theorem kernel_time_sum_polynomial {k w : ℝ} (hk : 0 < k) (hw : 1 ≤ w) :
    (2 + w) * (1 + 1 / (k / (4 * w ^ 2))) ^ 4 ≤
      (3 * (1 + 4 / k) ^ 4) * w ^ 9 := by
  have hw0 : 0 < w := by linarith
  have hden : 1 + 1 / (k / (4 * w ^ 2)) ≤ (1 + 4 / k) * w ^ 2 := by
    have he : 1 / (k / (4 * w ^ 2)) = 4 * w ^ 2 / k := by field_simp
    rw [he]
    have he' : (1 + 4 / k) * w ^ 2 = w ^ 2 + 4 * w ^ 2 / k := by ring
    rw [he']
    nlinarith
  have hh := mul_le_mul (show 2 + w ≤ 3 * w by linarith)
    (pow_le_pow_left₀ (by positivity) hden 4) (by positivity : 0 ≤ (1 + 1 / (k / (4 * w ^ 2))) ^ 4)
    (show 0 ≤ 3 * w by positivity)
  exact hh.trans_eq (by ring)

/-- Uniform finite IF tail budgets at every positive slope. The width exponent
is the fixed integer 16, chosen before any positive input-tail exponent. The
large-slope budget has the integrable inverse-square slope factor. -/
theorem kernel_regLaw_bulk_tail_budget (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∀ ζ : ℝ, 0 < ζ → ∃ Ks Kl : ℝ, 0 < Ks ∧ 0 < Kl ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (∀ x ≤ 0, f x = 0) ∧ (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ w t : ℝ, 1 ≤ w → 0 ≤ t → ∀ y z : ℝ, ∀ L R M : ℕ,
        ∀ a : ℝ, 0 < a →
          kernelOuterWeight ν w a * kernelPairTailSum ν f w a t y z L R M ≤
            if a ≤ 1 / 2 then Ks * w ^ 16 * Real.exp (ζ * t)
            else Kl * w ^ 16 * a⁻¹ ^ 2 := by
  obtain ⟨k, hk, hslopes⟩ := kernel_regLaw_full_pair_all_slopes D θ vlo vhi hD hθ hvlo hv
  obtain ⟨Os, Ol, hOs, hOl, houter⟩ := kernel_regLaw_outer_weight_bound D θ vlo vhi hD hθ hvlo hv
  let K := D ^ 2 * (2 + 36 * D) * Real.exp (2 * k)
  have hK : 0 < K := by positivity
  intro ζ hζ
  obtain ⟨c, hc, hdata⟩ := hslopes ζ hζ
  let S := (D * Real.exp θ) ^ 2 * (8 / c ^ 2)
  have hS : 0 < S := by positivity
  refine ⟨Os * S * (3 * (1 + 1 / c) ^ 4), Ol * K * (3 * (1 + 4 / k) ^ 4),
    by positivity, by positivity, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hfD, hfz, hfe, hνf, hp⟩ := hdata ν hν
  refine ⟨f, hf, hf0, hfD, hfz, hfe, hνf, ?_⟩
  intro w t hw ht y z L R M a ha
  have hw0 : 0 < w := by linarith
  have hpair (l r m : ℕ) :
      kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z * krDens (Icc 0 w) ν f 1 a (m + 1) z y ≤
        if a ≤ 1 / 2 then (D * Real.exp θ / a) ^ 2 * Real.exp (ζ * t - c * ((l : ℝ) + r + (m + 1)) / a)
        else ((D / a) * (1 + 3 * Real.sqrt (2 * D * w))) ^ 2 *
          Real.exp (-(k * (((l : ℝ) + r + (m + 1)) - 8) / (4 * w ^ 2))) := by
    by_cases hlr : 1 ≤ l + r
    · simpa only [zero_add, Nat.cast_add, Nat.cast_one] using hp 0 w a hw ha t ht y z l r (m + 1) hlr (by omega)
    · have hl : l = 0 := by omega
      have hr : r = 0 := by omega
      simp only [hl, hr, kernelMarkedFullDens, zero_mul]
      split_ifs <;> positivity
  have ho := houter ν hν w a hw ha
  by_cases halo : a ≤ 1 / 2
  · rw [if_pos halo] at ho ⊢
    have hb (l r m : ℕ) :
        kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z * krDens (Icc 0 w) ν f 1 a (m + 1) z y ≤
          (S * Real.exp (ζ * t)) * Real.exp (-c * ((l : ℝ) + r + (m + 1))) := by
      have hh := hpair l r m
      rw [if_pos halo] at hh
      exact hh.trans (kernel_small_pair_polynomial ha halo hc (by
        nlinarith [Nat.cast_nonneg (α := ℝ) l, Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) m]))
    have hh := kernelPairTailSum_le_of_exp ν f hw0.le hc (by positivity) hb L R M
    have ht' : (2 + w) * (1 + 1 / c) ^ 4 ≤ 3 * (1 + 1 / c) ^ 4 * w := by
      have h := mul_le_mul_of_nonneg_right (show 2 + w ≤ 3 * w by linarith) (show 0 ≤ (1 + 1 / c) ^ 4 by positivity)
      exact h.trans_eq (by ring)
    have hh' := hh.trans (mul_le_mul_of_nonneg_left ht' (by positivity))
    have hh'' := mul_le_mul ho hh' (kernelPairTailSum_nonneg ν hf0 hw0.le a t y z L R M) (by positivity)
    have hw316 : w ^ 3 ≤ w ^ 16 := pow_le_pow_right₀ hw (by norm_num)
    have hlast := mul_le_mul_of_nonneg_left hw316
      (show 0 ≤ Os * S * (3 * (1 + 1 / c) ^ 4) * Real.exp (ζ * t) by positivity)
    apply hh''.trans
    convert hlast using 1 <;> ring
  · rw [if_neg halo] at ho ⊢
    have hu : 0 < k / (4 * w ^ 2) := by positivity
    have hb (l r m : ℕ) :
        kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z * krDens (Icc 0 w) ν f 1 a (m + 1) z y ≤
          (K * w * a⁻¹ ^ 2) * Real.exp (-(k / (4 * w ^ 2)) * ((l : ℝ) + r + (m + 1))) := by
      have hh := hpair l r m
      rw [if_neg halo] at hh
      exact hh.trans (kernel_spectral_pair_polynomial hD.le hk.le hw)
    have hh := kernelPairTailSum_le_of_exp ν f hw0.le hu (by positivity) hb L R M
    have hh' := hh.trans (mul_le_mul_of_nonneg_left (kernel_time_sum_polynomial hk hw) (by positivity))
    have hh'' := mul_le_mul ho hh' (kernelPairTailSum_nonneg ν hf0 hw0.le a t y z L R M) (by positivity)
    exact hh''.trans_eq (by ring)

end
end PGM
