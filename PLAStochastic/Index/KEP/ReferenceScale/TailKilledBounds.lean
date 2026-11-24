import PLAStochastic.Index.KEP.ReferenceScale.ActualBridgeFluxBudgets
import PLAStochastic.Index.KEP.ReferenceScale.GraphTransport

/-!
# Killed exterior tail budgets, including every zero-step Dirac case

The pointwise bridge bound gives the exterior mass without using a probability
bound that would discard its killed rate. A zero-step tail is kept explicitly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kep_integral_Ioc_uniform_abs {F : ℝ → ℝ} {w A : ℝ}
    (hw : 0 ≤ w) (_hA0 : 0 ≤ A) (hA : ∀ y ∈ Icc (0 : ℝ) w, |F y| ≤ A) :
    |∫ y in Ioc 0 w, F y| ≤ A * w := by
  have hh := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc 0 w))
    (C := A) (f := F)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        simpa only [Real.norm_eq_abs] using hA y ⟨hy.1.le, hy.2⟩)
  rw [Real.norm_eq_abs, measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hw,
    sub_zero] at hh
  exact hh

theorem kepTailTest_killed_bound {p : ℝ → ℝ → ℝ} {w C r s B : ℝ}
    (hw : 0 ≤ w) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hK : ∀ m : ℕ, ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge p w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc 0 w) {φ : ℝ → ℝ}
    (hφ : ∀ y ∈ Icc (0 : ℝ) w, |φ y| ≤ B) :
    |kepTailTest p w s n x φ| ≤ (1 + C * w) * B * Real.exp (-r * (n : ℝ)) := by
  cases n with
  | zero =>
    simp only [kepTailTest, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    exact (hφ x hx).trans (by nlinarith [mul_nonneg (mul_nonneg hC hw) hB])
  | succ n =>
    have hh := kep_integral_Ioc_uniform_abs hw
      (by positivity : 0 ≤ C * Real.exp (-r * (n + 1 : ℕ)) * B)
      (F := fun y => kepFixedBridge p w s n x y * φ y)
      (fun y hy => by
        rw [abs_mul]
        exact mul_le_mul (hK n x hx y hy) (hφ y hy) (abs_nonneg _) (by positivity))
    change |∫ y in Ioc 0 w, kepFixedBridge p w s n x y * φ y| ≤ _
    apply hh.trans
    push_cast
    have he := (Real.exp_pos (-r * ((n : ℝ) + 1))).le
    nlinarith [mul_nonneg hB he]

theorem kepTailPairTest_killed_bound {pA pB : ℝ → ℝ → ℝ} {w C r s B : ℝ}
    (hw : 0 ≤ w) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hA : ∀ m : ℕ, ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge pA w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (hBstep : ∀ m : ℕ, ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge pB w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (i k : ℕ) {xA xB : ℝ} (hxA : xA ∈ Icc 0 w) (hxB : xB ∈ Icc 0 w)
    {Φ : ℝ → ℝ → ℝ} (hΦ : ∀ u ∈ Icc (0 : ℝ) w, ∀ v ∈ Icc (0 : ℝ) w, |Φ u v| ≤ B) :
    |kepTailPairTest pA pB w s i k xA xB Φ| ≤
      (1 + C * w) ^ 2 * B * Real.exp (-r * (i + k : ℕ)) := by
  have hh := kepTailTest_killed_bound hw hC
    (by positivity : 0 ≤ (1 + C * w) * B * Real.exp (-r * (k : ℝ))) hA i hxA
    (φ := fun u => kepTailTest pB w s k xB (Φ u))
    (fun u hu => kepTailTest_killed_bound hw hC hB hBstep k hxB (hΦ u hu))
  change |kepTailPairTest pA pB w s i k xA xB Φ| ≤ _ at hh
  apply hh.trans_eq
  calc
    _ = (1 + C * w) ^ 2 * B * (Real.exp (-r * (i : ℝ)) *
        Real.exp (-r * (k : ℝ))) := by ring
    _ = _ := by rw [← Real.exp_add, ← mul_add, ← Nat.cast_add]

end

end PGM
