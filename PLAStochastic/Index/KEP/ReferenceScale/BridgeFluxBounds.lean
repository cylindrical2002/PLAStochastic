import PLAStochastic.Index.KEP.ReferenceScale.ActualBridgeBudgets
import PLAStochastic.Index.KEP.ReferenceScale.CertificateScalar

/-!
# Full-length killed bounds for every internal transport pin

The two bridge lengths on either side of a pin sum to the original physical
length. Consequently summing all pins costs a polynomial, with no loss of the
killed exponential rate. These estimates apply at both band endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kep_pin_coefficient_bound {w σ x b : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hx : x ∈ Icc 0 w) (hb : b ∈ Icc 0 w) (l : ℕ) :
    |b - x - (l + 1 : ℕ) * σ| ≤ w + (l + 1 : ℕ) := by
  have hs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hbx : |b - x| ≤ w := abs_le.mpr ⟨by linarith [hx.2, hb.1],
    by linarith [hx.1, hb.2]⟩
  calc
    _ ≤ |b - x| + |(l + 1 : ℕ) * σ| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (b - x) 0 ((l + 1 : ℕ) * σ)
    _ = |b - x| + (l + 1 : ℕ) := by
      rw [abs_mul, hs, mul_one, abs_of_nonneg (show (0 : ℝ) ≤ (l + 1 : ℕ) by positivity)]
    _ ≤ _ := by linarith

theorem kep_pin_length_exp {r : ℝ} {n l : ℕ} (hl : l < n) :
    Real.exp (-r * (l + 1 : ℕ)) * Real.exp (-r * (n - 1 - l + 1 : ℕ)) =
      Real.exp (-r * (n + 1 : ℕ)) := by
  rw [← Real.exp_add, ← mul_add, ← Nat.cast_add]
  have hlen : l + 1 + (n - 1 - l + 1) = n + 1 := by omega
  rw [hlen]

theorem kepBridgeTransportFlux_exp_bound {p : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) {w σ C r s : ℝ}
    (hw : 0 ≤ w) (hC : 0 ≤ C) (hσ : σ = 1 ∨ σ = -1)
    (hK : ∀ m : ℕ, ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge p w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (n : ℕ) {x y : ℝ} (hx : x ∈ Icc 0 w) (hy : y ∈ Icc 0 w) :
    |kepBridgeTransportFlux p w σ s n x y| ≤
      2 * (n : ℝ) * (w + (n + 1 : ℕ)) * C ^ 2 * Real.exp (-r * (n + 1 : ℕ)) := by
  have hb0 : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw⟩
  have hbw : w ∈ Icc 0 w := ⟨hw, le_rfl⟩
  have hterm (l : ℕ) (hl : l ∈ Finset.range n) (b : ℝ) (hb : b ∈ Icc 0 w) :
      |(b - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x b *
        kepFixedBridge p w s (n - 1 - l) b y| ≤
      (w + (n + 1 : ℕ)) * C ^ 2 * Real.exp (-r * (n + 1 : ℕ)) := by
    have hln := Finset.mem_range.mp hl
    have hcast : (l + 1 : ℕ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hln.le 1
    have hcoeff : |b - x - (l + 1 : ℕ) * σ| ≤ w + (n + 1 : ℕ) := by
      have hh := kep_pin_coefficient_bound hσ hx hb l
      push_cast at hh hcast ⊢
      linarith
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (w + (n + 1 : ℕ)) * (C * Real.exp (-r * (l + 1 : ℕ))) *
          (C * Real.exp (-r * (n - 1 - l + 1 : ℕ))) := by
        exact mul_le_mul (mul_le_mul hcoeff (hK l x hx b hb) (abs_nonneg _)
          (by positivity)) (hK _ b hb y hy) (abs_nonneg _) (by positivity)
      _ = (w + (n + 1 : ℕ)) * C ^ 2 *
          (Real.exp (-r * (l + 1 : ℕ)) * Real.exp (-r * (n - 1 - l + 1 : ℕ))) := by ring
      _ = _ := by rw [kep_pin_length_exp hln]
  rw [kepBridgeTransportFlux_eq_sum hp]
  calc
    _ ≤ ∑ l ∈ Finset.range n,
        |(w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w *
          kepFixedBridge p w s (n - 1 - l) w y -
        (-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0 *
          kepFixedBridge p w s (n - 1 - l) 0 y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l ∈ Finset.range n,
        2 * ((w + (n + 1 : ℕ)) * C ^ 2 * Real.exp (-r * (n + 1 : ℕ))) := by
      apply Finset.sum_le_sum
      intro l hl
      have h0 := hterm l hl 0 hb0
      simp only [zero_sub] at h0
      have ht := abs_sub_le
        ((w - x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x w *
          kepFixedBridge p w s (n - 1 - l) w y) 0
        ((-x - (l + 1 : ℕ) * σ) * kepFixedBridge p w s l x 0 *
          kepFixedBridge p w s (n - 1 - l) 0 y)
      simp only [sub_zero, zero_sub, abs_neg] at ht
      linarith [hterm l hl w hbw]
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end

end PGM
