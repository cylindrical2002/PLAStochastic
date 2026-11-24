import Mathlib.NumberTheory.Harmonic.Bounds

/-! Reciprocal sums over a finite interval. -/
noncomputable section
open Set MeasureTheory

theorem reciprocal_sum_Ico_le_log_ratio {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    (∑ j ∈ Finset.Ico k m, ((j + 1 : ℕ) : ℝ)⁻¹) ≤
      Real.log ((m : ℝ) / (k : ℝ)) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hs := @AntitoneOn.sum_le_integral_Ico k m (fun x : ℝ => x⁻¹) hkm
    (inv_antitoneOn_Icc_right hkr)
  rw [integral_inv (by
    rw [Set.uIcc_of_le (by exact_mod_cast hkm)]
    rintro ⟨hz, _⟩
    linarith) ] at hs
  simpa only [Nat.cast_add] using hs

end
