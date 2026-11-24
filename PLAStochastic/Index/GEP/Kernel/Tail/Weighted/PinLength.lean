import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.PolynomialBudget

/-! # Absorbing the true closed-bridge physical length into tail decay -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1000000

/-- The sum of physical gaps of the two opposite pinned bridges is exactly
`(N+1)/a`: `N` random gaps and the one designated gap. This estimate absorbs
the resulting exponential weight at the small-slope Chernoff rate. -/
theorem kernel_small_time_weight_absorb {a c s N X : ℝ} (ha : 0 < a)
    (_hc : 0 < c) (hs0 : 0 ≤ s) (hs : s ≤ c / 4) (hN : 1 ≤ N) :
    Real.exp (s * (N + 1) / a) * Real.exp (X - c * N / a) ≤
      Real.exp (X - (c / 2) * N / a) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh : s * (N + 1) ≤ (c / 2) * N := by
    have h₁ := mul_le_mul_of_nonneg_left (show N + 1 ≤ 2 * N by linarith) hs0
    have h₂ := mul_le_mul_of_nonneg_right hs (show 0 ≤ 2 * N by linarith)
    nlinarith
  have hh' := div_le_div_of_nonneg_right hh ha.le
  have he : c * N / a = 2 * ((c / 2) * N / a) := by ring
  rw [he]
  linarith

/-- The output weight can be chosen on the diffusive scale, before the later
arbitrary input exponent. It consumes at most half the spectral rate. -/
theorem kernel_large_time_weight_absorb {a k w s N : ℝ} (ha : 1 / 2 ≤ a)
    (_hk : 0 < k) (_hw : 0 < w) (hs0 : 0 ≤ s) (hs : s ≤ k / (32 * w ^ 2))
    (hN : 1 ≤ N) :
    Real.exp (s * (N + 1) / a) * Real.exp (-(k / (4 * w ^ 2)) * N) ≤
      Real.exp (-((k / 2) / (4 * w ^ 2)) * N) := by
  have ha0 : 0 < a := by linarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h₁ : s * (N + 1) / a ≤ 4 * s * N := by
    apply (div_le_iff₀ ha0).mpr
    have h₂ := mul_le_mul_of_nonneg_left (show N + 1 ≤ 2 * N by linarith) hs0
    have h₃ := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4 * s * N by positivity)
    nlinarith
  have h₂ : 4 * s * N ≤ k / (8 * w ^ 2) * N := by
    have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ 4 * N by linarith)
    calc
      _ = s * (4 * N) := by ring
      _ ≤ _ := hh
      _ = _ := by ring
  have he : k / (4 * w ^ 2) * N = 2 * (k / (8 * w ^ 2) * N) := by ring
  have he' : (k / 2) / (4 * w ^ 2) * N = k / (8 * w ^ 2) * N := by ring
  rw [neg_mul, neg_mul, he, he']
  linarith

/-- Actual marked pin pairs with the full internal physical-sum reward. The
width-rate constant is fixed before `ζ`; only the eventual upper bound on
`s` may depend on `ζ`, as permitted by the final epsilon threshold. -/
theorem kernel_regLaw_weighted_pair_polynomial (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ k Kl : ℝ, 0 < k ∧ 0 < Kl ∧
      ∀ ζ : ℝ, 0 < ζ → ∃ c Ks : ℝ, 0 < c ∧ 0 < Ks ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (∀ x ≤ 0, f x = 0) ∧ (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ w s a t : ℝ, 1 ≤ w → 0 ≤ s → s ≤ c / 2 →
          s ≤ k / (16 * w ^ 2) → 0 < a → 0 ≤ t →
        ∀ y z : ℝ, ∀ l r M : ℕ, 1 ≤ l + r → 1 ≤ M →
          Real.exp (s * ((l : ℝ) + r + M + 1) / a) *
            (kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z *
              krDens (Icc 0 w) ν f 1 a M z y) ≤
            if a ≤ 1 / 2 then Ks * Real.exp (ζ * t) * Real.exp (-c * ((l : ℝ) + r + M))
            else Kl * w * a⁻¹ ^ 2 * Real.exp (-(k / (4 * w ^ 2)) * ((l : ℝ) + r + M)) := by
  obtain ⟨k, hk, hall⟩ := kernel_regLaw_full_pair_all_slopes D θ vlo vhi hD hθ hvlo hv
  let Kl := D ^ 2 * (2 + 36 * D) * Real.exp (2 * k)
  have hKl : 0 < Kl := by positivity
  refine ⟨k / 2, Kl, by positivity, hKl, ?_⟩
  intro ζ hζ
  obtain ⟨c, hc, hdata⟩ := hall ζ hζ
  let Ks := (D * Real.exp θ) ^ 2 * (8 / (c / 2) ^ 2)
  have hKs : 0 < Ks := by positivity
  refine ⟨c / 2, Ks, by positivity, hKs, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hfD, hfz, hfe, hνf, hp⟩ := hdata ν hν
  refine ⟨f, hf, hf0, hfD, hfz, hfe, hνf, ?_⟩
  intro w s a t hw hs0 hsc hsk ha ht y z l r M hlr hM
  have hw0 : 0 < w := by linarith
  have hN : 1 ≤ (l : ℝ) + r + M := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [Nat.cast_nonneg (α := ℝ) l, Nat.cast_nonneg (α := ℝ) r]
  have hh := hp 0 w a hw ha t ht y z l r M hlr hM
  simp only [zero_add] at hh
  by_cases halo : a ≤ 1 / 2
  · rw [if_pos halo] at hh ⊢
    have hs : s ≤ c / 4 := by linarith
    have hb := kernel_small_time_weight_absorb ha hc hs0 hs hN (X := ζ * t)
    have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (s * ((l : ℝ) + r + M + 1) / a))
    calc
      _ ≤ (D * Real.exp θ / a) ^ 2 *
          (Real.exp (s * ((l : ℝ) + r + M + 1) / a) * Real.exp (ζ * t - c * ((l : ℝ) + r + M) / a)) :=
        hh'.trans_eq (by ring)
      _ ≤ (D * Real.exp θ / a) ^ 2 * Real.exp (ζ * t - (c / 2) * ((l : ℝ) + r + M) / a) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ ≤ _ := kernel_small_pair_polynomial ha halo (half_pos hc) hN
  · rw [if_neg halo] at hh ⊢
    have hs : s ≤ k / (32 * w ^ 2) := hsk.trans_eq (by ring)
    have hb := kernel_large_time_weight_absorb (le_of_lt (lt_of_not_ge halo)) hk hw0 hs0 hs hN
    have hh' := hh.trans (kernel_spectral_pair_polynomial hD.le hk.le hw)
    calc
      _ ≤ (Kl * w * a⁻¹ ^ 2) *
          (Real.exp (s * ((l : ℝ) + r + M + 1) / a) * Real.exp (-(k / (4 * w ^ 2)) * ((l : ℝ) + r + M))) :=
        (mul_le_mul_of_nonneg_left hh' (Real.exp_nonneg _)).trans_eq (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

end
end PGM
