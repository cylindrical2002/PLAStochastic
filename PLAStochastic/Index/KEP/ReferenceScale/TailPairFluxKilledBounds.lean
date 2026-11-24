import PLAStochastic.Index.KEP.ReferenceScale.TailFluxKilledBounds

/-!
# The full exterior two-tail flux keeps the total killed length

The two terms retain the rate in the sum of both exterior lengths. Either
tail, or either pinned suffix, may have zero steps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kepTailPairFlux_killed_bound {pA pB : ℝ → ℝ → ℝ}
    (hpA : Continuous (Function.uncurry pA)) (hpB : Continuous (Function.uncurry pB))
    {σA σB w C r s B : ℝ} (hσA : σA = 1 ∨ σA = -1) (hσB : σB = 1 ∨ σB = -1)
    (hw : 0 ≤ w) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hA : ∀ m : ℕ, ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge pA w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (hBstep : ∀ m : ℕ, ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge pB w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (i k : ℕ) {xA xB : ℝ} (hxA : xA ∈ Icc 0 w) (hxB : xB ∈ Icc 0 w)
    {Φ : ℝ → ℝ → ℝ} (hΦ : ∀ u ∈ Icc (0 : ℝ) w, ∀ v ∈ Icc (0 : ℝ) w, |Φ u v| ≤ B) :
    |kepTailPairFlux pA pB w σA σB s i k xA xB Φ| ≤
      2 * (i + k : ℕ) * (w + (i + k : ℕ)) * (1 + C * w) ^ 2 * C * B *
        Real.exp (-r * (i + k : ℕ)) := by
  let T := 1 + C * w
  let E := Real.exp (-r * (i + k : ℕ))
  have hleft := kepTailFluxTest_killed_bound hpA hσA hw hC
    (by positivity : 0 ≤ T * B * Real.exp (-r * (k : ℝ))) hA i hxA
    (φ := fun u => kepTailTest pB w s k xB (Φ u))
    (fun u hu => kepTailTest_killed_bound hw hC hB hBstep k hxB (hΦ u hu))
  have hleft' : |kepTailFluxTest pA w σA s i xA
      (fun u => kepTailTest pB w s k xB (Φ u))| ≤ 2 * (i : ℝ) * (w + i) * T ^ 2 * C * B * E := by
    apply hleft.trans_eq
    calc
      _ = 2 * (i : ℝ) * (w + i) * T ^ 2 * C * B *
          (Real.exp (-r * (i : ℝ)) * Real.exp (-r * (k : ℝ))) := by dsimp [T]; ring
      _ = _ := by rw [← Real.exp_add, ← mul_add, ← Nat.cast_add]
  have hright := kepTailTest_killed_bound hw hC
    (by positivity : 0 ≤ 2 * (k : ℝ) * (w + k) * T * C * B * Real.exp (-r * (k : ℝ)))
    hA i hxA (φ := fun u => kepTailFluxTest pB w σB s k xB (Φ u))
    (fun u hu => kepTailFluxTest_killed_bound hpB hσB hw hC hB hBstep k hxB (hΦ u hu))
  have hright' : |kepTailTest pA w s i xA
      (fun u => kepTailFluxTest pB w σB s k xB (Φ u))| ≤ 2 * (k : ℝ) * (w + k) * T ^ 2 * C * B * E := by
    apply hright.trans_eq
    calc
      _ = 2 * (k : ℝ) * (w + k) * T ^ 2 * C * B *
          (Real.exp (-r * (i : ℝ)) * Real.exp (-r * (k : ℝ))) := by dsimp [T]; ring
      _ = _ := by rw [← Real.exp_add, ← mul_add, ← Nat.cast_add]
  have hcoef : 2 * (i : ℝ) * (w + i) + 2 * (k : ℝ) * (w + k) ≤
      2 * (i + k : ℕ) * (w + (i + k : ℕ)) := by
    push_cast
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) i) (Nat.cast_nonneg (α := ℝ) k)]
  have hm := mul_le_mul_of_nonneg_right hcoef
    (by dsimp [E]; positivity : 0 ≤ T ^ 2 * C * B * E)
  unfold kepTailPairFlux
  apply (abs_add_le _ _).trans
  calc
    _ ≤ 2 * (i : ℝ) * (w + i) * T ^ 2 * C * B * E +
        2 * (k : ℝ) * (w + k) * T ^ 2 * C * B * E := by gcongr
    _ ≤ _ := by nlinarith only [hm]

end

end PGM
