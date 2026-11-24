import PLAStochastic.Index.KEP.ReferenceScale.TailKilledBounds

/-!
# Killed budgets for the exterior fluxes and their terminal pins

The endpoint contributions use the same full-length rate as the integrated
internal flux. No rate is lost when a tail suffix is the zero-step Dirac mass.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kep_abs_neg_sub_add (a b c : ℝ) : |-a - b + c| ≤ |a| + |b| + |c| := by
  calc
    _ ≤ |-a - b| + |c| := abs_add_le _ _
    _ ≤ (|a| + |b|) + |c| := by
      have hh := abs_sub_le (-a) 0 b
      simp only [sub_zero, zero_sub, abs_neg] at hh
      linarith

theorem kepTailFluxTest_killed_bound {p : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) {σ w C r s B : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hw : 0 ≤ w) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hK : ∀ m : ℕ, ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge p w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc 0 w) {φ : ℝ → ℝ}
    (hφ : ∀ y ∈ Icc (0 : ℝ) w, |φ y| ≤ B) :
    |kepTailFluxTest p w σ s n x φ| ≤
      2 * (n : ℝ) * (w + (n : ℝ)) * (1 + C * w) * C * B *
        Real.exp (-r * (n : ℝ)) := by
  cases n with
  | zero => simp only [kepTailFluxTest, abs_zero, Nat.cast_zero, mul_zero, zero_mul, le_refl]
  | succ n =>
    let S := w + (n + 1 : ℕ)
    let E := Real.exp (-r * (n + 1 : ℕ))
    have hS : 0 ≤ S := by dsimp [S]; positivity
    have hE : 0 ≤ E := (Real.exp_pos _).le
    have hb0 : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw⟩
    have hbw : w ∈ Icc 0 w := ⟨hw, le_rfl⟩
    have hI : |∫ y in Ioc 0 w, kepBridgeTransportFlux p w σ s n x y * φ y| ≤
        (2 * (n : ℝ) * S * C ^ 2 * E * B) * w := by
      apply kep_integral_Ioc_uniform_abs hw (by positivity)
      intro y hy
      rw [abs_mul]
      exact mul_le_mul (kepBridgeTransportFlux_exp_bound hp hw hC hσ hK n hx hy)
        (hφ y hy) (abs_nonneg _) (by positivity)
    have ht (b : ℝ) (hb : b ∈ Icc 0 w) :
        |(b - x - (n + 1 : ℕ) * σ) * kepFixedBridge p w s n x b * φ b| ≤ S * C * E * B := by
      rw [abs_mul, abs_mul]
      have hh := mul_le_mul (mul_le_mul (kep_pin_coefficient_bound hσ hx hb n)
        (hK n x hx b hb) (abs_nonneg _) (by positivity)) (hφ b hb)
        (abs_nonneg _) (by positivity)
      simpa only [mul_assoc] using hh
    have h0 := ht 0 hb0
    simp only [zero_sub] at h0
    have hcoef : 2 * (n : ℝ) * S * C ^ 2 * w + 2 * S * C ≤
        2 * (n + 1 : ℕ) * S * (1 + C * w) * C := by
      have hh : 0 ≤ 2 * S * C * ((n : ℝ) + C * w) := by positivity
      push_cast
      nlinarith only [hh]
    have hm := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hB hE)
    simp only [kepTailFluxTest]
    calc
      _ ≤ |∫ y in Ioc 0 w, kepBridgeTransportFlux p w σ s n x y * φ y| +
          |(w - x - (n + 1 : ℕ) * σ) * kepFixedBridge p w s n x w * φ w| +
          |(-x - (n + 1 : ℕ) * σ) * kepFixedBridge p w s n x 0 * φ 0| :=
        kep_abs_neg_sub_add _ _ _
      _ ≤ (2 * (n : ℝ) * S * C ^ 2 * E * B) * w + (S * C * E * B) + (S * C * E * B) := by
        gcongr
        exact ht w hbw
      _ ≤ 2 * (n + 1 : ℕ) * S * (1 + C * w) * C * B * E := by nlinarith only [hm]

end

end PGM
