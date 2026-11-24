import PLAStochastic.Index.GEP.Kernel.FarSlope.FixedUniform
import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.PinLength

/-! # Fixed far-slope crossing decay with the actual internal physical weight -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1400000

theorem kernel_fixed_time_weight_absorb {a c s N X : ℝ} (ha : 1 / 2 ≤ a)
    (hs0 : 0 ≤ s) (hs : s ≤ c / 8) (hN : 1 ≤ N) :
    Real.exp (s * (N + 1) / a) * Real.exp (X - c * N) ≤
      Real.exp (X - (c / 2) * N) := by
  have ha0 : 0 < a := by linarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h₁ : s * (N + 1) / a ≤ 4 * s * N := by
    apply (div_le_iff₀ ha0).mpr
    have h₂ := mul_le_mul_of_nonneg_left (show N + 1 ≤ 2 * N by linarith) hs0
    have h₃ := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4 * s * N by positivity)
    nlinarith
  have h₂ := mul_le_mul_of_nonneg_right hs (show 0 ≤ 4 * N by linarith)
  nlinarith

theorem kernel_regLaw_weighted_full_pair_far_width (D θ vlo vhi δ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) :
    ∃ ρ lam c K : ℝ, 0 < ρ ∧ 0 < lam ∧ 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ w s a t : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ → 0 < a → δ ≤ |a - 1| → 0 ≤ t →
      ∀ y z : ℝ, ((y = 0 ∧ z = w) ∨ (y = w ∧ z = 0)) →
      ∀ l r M : ℕ, 1 ≤ M →
        Real.exp (s * ((l : ℝ) + r + M + 1) / a) *
          (kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z * krDens (Icc 0 w) ν f 1 a M z y) ≤
          (if a ≤ 1 / 2 then K else K * a⁻¹ ^ 2) *
            Real.exp (lam * t - c * w) * Real.exp (-c * ((l : ℝ) + r + M)) := by
  obtain ⟨lam, c', hlam, hc', hraw⟩ :=
    kernel_regLaw_full_pair_fixed_far_of_density D θ vlo vhi δ hθ hvlo hv hδ hδhi
  let c := c' / 2
  have hc : 0 < c := half_pos hc'
  let S := (D * Real.exp θ) ^ 2 * (8 / c ^ 2)
  let L := (D * Real.exp θ) ^ 2 * Real.exp (2 * lam)
  let K := (S + L) * Real.exp (c / 2)
  have hS : 0 < S := by positivity
  have hL : 0 < L := by positivity
  have hK : 0 < K := by positivity
  refine ⟨c' / 8, lam, c / 2, K, by positivity, hlam, by positivity, hK, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf w s a t hw hs0 hs ha haway ht y z hyz l r M hM
  let N : ℝ := (l : ℝ) + r + M
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    dsimp [N]
    nlinarith [Nat.cast_nonneg (α := ℝ) l, Nat.cast_nonneg (α := ℝ) r]
  by_cases hwN : w ≤ N + 1
  · have hh0 := hraw ν hν f hf hf0 hfD hfz hfe hνf (Icc 0 w) measurableSet_Icc
      (by simp) a ha haway t ht y z l r M hM
    have hh1 := mul_le_mul_of_nonneg_left hh0 (Real.exp_nonneg (s * (N + 1) / a))
    have hh : Real.exp (s * (N + 1) / a) *
        (kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z * krDens (Icc 0 w) ν f 1 a M z y) ≤
        if a ≤ 1 / 2 then (D * Real.exp θ / a) ^ 2 * Real.exp (lam * t - c * N / a)
        else (D * Real.exp θ / a) ^ 2 * Real.exp (lam * t + 2 * lam - c * N) := by
      by_cases halo : a ≤ 1 / 2
      · rw [if_pos halo] at hh1 ⊢
        have hb := kernel_small_time_weight_absorb ha hc' hs0 (show s ≤ c' / 4 by linarith) hN (X := lam * t)
        calc
          _ ≤ (D * Real.exp θ / a) ^ 2 * (Real.exp (s * (N + 1) / a) * Real.exp (lam * t - c' * N / a)) :=
            hh1.trans_eq (by ring)
          _ ≤ _ := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      · rw [if_neg halo] at hh1 ⊢
        have hb := kernel_fixed_time_weight_absorb (le_of_lt (lt_of_not_ge halo)) hs0 hs hN (X := lam * t + 2 * lam)
        calc
          _ ≤ (D * Real.exp θ / a) ^ 2 * (Real.exp (s * (N + 1) / a) * Real.exp (lam * t + 2 * lam - c' * N)) :=
            hh1.trans_eq (by ring)
          _ ≤ _ := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    have hsplit := kernel_far_time_width_split_add_one hc.le hwN
    by_cases halo : a ≤ 1 / 2
    · rw [if_pos halo] at hh ⊢
      have hh' := hh.trans (kernel_small_pair_polynomial ha halo hc hN)
      have hwidth := mul_le_mul_of_nonneg_left hsplit (show 0 ≤ S * Real.exp (lam * t) by positivity)
      have hcoef : S * Real.exp (c / 2) ≤ K := by
        dsimp [K]
        gcongr
        linarith
      calc
        _ ≤ (S * Real.exp (lam * t)) *
            (Real.exp (c / 2) * Real.exp (-(c / 2) * w) * Real.exp (-(c / 2) * N)) := hh'.trans hwidth
        _ = (S * Real.exp (c / 2)) * Real.exp (lam * t - (c / 2) * w) * Real.exp (-(c / 2) * N) := by
          rw [show lam * t - (c / 2) * w = lam * t + (-(c / 2) * w) by ring, Real.exp_add]
          ring
        _ ≤ _ := by gcongr
    · rw [if_neg halo] at hh ⊢
      have he : (D * Real.exp θ / a) ^ 2 * Real.exp (lam * t + 2 * lam - c * N) =
          (L * a⁻¹ ^ 2 * Real.exp (lam * t)) * Real.exp (-c * N) := by
        rw [show lam * t + 2 * lam - c * N = 2 * lam + lam * t + (-c * N) by ring,
          Real.exp_add, Real.exp_add]
        dsimp [L]
        simp only [div_eq_mul_inv]
        ring
      change _ ≤ (D * Real.exp θ / a) ^ 2 * Real.exp (lam * t + 2 * lam - c * N) at hh
      rw [he] at hh
      have hwidth := mul_le_mul_of_nonneg_left hsplit (show 0 ≤ L * a⁻¹ ^ 2 * Real.exp (lam * t) by positivity)
      have hcoef : L * Real.exp (c / 2) ≤ K := by
        dsimp [K]
        gcongr
        linarith
      calc
        _ ≤ (L * a⁻¹ ^ 2 * Real.exp (lam * t)) *
            (Real.exp (c / 2) * Real.exp (-(c / 2) * w) * Real.exp (-(c / 2) * N)) := hh.trans hwidth
        _ = ((L * Real.exp (c / 2)) * a⁻¹ ^ 2) * Real.exp (lam * t - (c / 2) * w) * Real.exp (-(c / 2) * N) := by
          rw [show lam * t - (c / 2) * w = lam * t + (-(c / 2) * w) by ring, Real.exp_add]
          ring
        _ ≤ _ := by gcongr
  · rw [kernel_full_pair_short_zero hν hθ hvlo hfz ha ht hyz l r M hM (le_of_lt (not_le.mp hwN))]
    rw [mul_zero]
    split_ifs <;> positivity

end
end PGM
