import PLAStochastic.Index.KEP.ReferenceScale.TailPairFluxKilledBounds
import PLAStochastic.Index.KEP.ReferenceScale.GraphTransfer

/-!
# Compact graph integrals with the full exterior killed rate

Only values of the test on the actual compact graph are required. This permits
the physical exponential output weight without assuming a globally bounded
test. The scalar is paid in logarithmic-slope absolute integral norm.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kep_logSlope_integral_product_bound {R T : ℝ → ℝ} (hR : Continuous R)
    (hT : Continuous T) {A : ℝ}
    (hA : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), |T s| ≤ A) :
    |∫ s in Ioc (Real.log (1 / 2)) (Real.log 2), R s * T s| ≤ A * kepLogSlopeNorm R := by
  calc
    _ ≤ kepLogSlopeNorm (fun s => R s * T s) := by
      simpa only [kepLogSlopeNorm, Real.norm_eq_abs] using
        norm_integral_le_integral_norm (f := fun s => R s * T s)
          (μ := volume.restrict (Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2)))
    _ = kepLogSlopeNorm (fun s => T s * R s) := by congr 1; funext s; ring
    _ ≤ _ := kepLogSlopeNorm_mul_bound hT hR hA

theorem kepLogGraphIntegral_killed_bound {pA pB : ℝ → ℝ → ℝ}
    (hpA : Continuous (Function.uncurry pA)) (hpB : Continuous (Function.uncurry pB))
    {w C r B D : ℝ} (hw : 0 ≤ w) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hA : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), ∀ m : ℕ,
      ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge pA w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (hBstep : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), ∀ m : ℕ,
      ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge pB w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (i k : ℕ) {xA xB : ℝ} (hxA : xA ∈ Icc 0 w) (hxB : xB ∈ Icc 0 w)
    {R φ : ℝ → ℝ} (hR : Continuous R) (hφ : Continuous φ)
    (hTest : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      ∀ u ∈ Icc (0 : ℝ) w, ∀ v ∈ Icc (0 : ℝ) w,
      |φ (kepGraphOutput D i k xA xB s u v)| ≤ B) :
    |kepLogGraphIntegral pA pB w (Real.log (1 / 2)) (Real.log 2) D i k xA xB R φ| ≤
      (1 + C * w) ^ 2 * B * Real.exp (-r * (i + k : ℕ)) * kepLogSlopeNorm R := by
  have hT := continuous_kepTailPairTest hpA hpB
    (Φ := fun s u v => φ (kepGraphOutput D i k xA xB s u v))
    (hφ.comp (continuous_kepGraphOutput D i k xA xB)) w i k xA xB
  exact kep_logSlope_integral_product_bound hR hT (fun s hs =>
    kepTailPairTest_killed_bound hw hC hB (hA s hs) (hBstep s hs) i k hxA hxB
      (hTest s hs))

theorem kepLogGraphFluxIntegral_killed_bound {pA pB : ℝ → ℝ → ℝ}
    (hpA : Continuous (Function.uncurry pA)) (hpB : Continuous (Function.uncurry pB))
    {w C r B D : ℝ} (hw : 0 ≤ w) (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 1 ≤ D)
    (hA : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), ∀ m : ℕ,
      ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge pA w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (hBstep : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), ∀ m : ℕ,
      ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
      |kepFixedBridge pB w s m x y| ≤ C * Real.exp (-r * (m + 1 : ℕ)))
    (i k : ℕ) {xA xB : ℝ} (hxA : xA ∈ Icc 0 w) (hxB : xB ∈ Icc 0 w)
    {R φ : ℝ → ℝ} (hR : Continuous R) (hφ : Continuous φ)
    (hTest : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      ∀ u ∈ Icc (0 : ℝ) w, ∀ v ∈ Icc (0 : ℝ) w,
      |φ (kepGraphOutput D i k xA xB s u v)| ≤ B) :
    |kepLogGraphFluxIntegral pA pB w (Real.log (1 / 2)) (Real.log 2) D i k xA xB R φ| ≤
      4 * (i + k : ℕ) * (w + (i + k : ℕ)) * (1 + C * w) ^ 2 * C * B *
        Real.exp (-r * (i + k : ℕ)) * kepLogSlopeNorm R := by
  let U := fun s => Real.exp s * R s / D
  have hU : Continuous U := (Real.continuous_exp.mul hR).div_const D
  have hT := continuous_kepTailPairFlux hpA hpB
    (Φ := fun s u v => φ (kepGraphOutput D i k xA xB s u v))
    (hφ.comp (continuous_kepGraphOutput D i k xA xB)) w (-1) 1 i k xA xB
  have hh := kep_logSlope_integral_product_bound hU hT (fun s hs =>
    kepTailPairFlux_killed_bound hpA hpB (Or.inr rfl) (Or.inl rfl) hw hC hB
      (hA s hs) (hBstep s hs) i k hxA hxB (hTest s hs))
  have hc : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), |Real.exp s / D| ≤ 2 := by
    intro s hs
    rw [abs_of_nonneg (by positivity : 0 ≤ Real.exp s / D)]
    have he : Real.exp s ≤ 2 := by
      have ht := Real.exp_le_exp.mpr hs.2
      simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using ht
    have hi := inv_le_one_of_one_le₀ hD
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp s * 1 := mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
      _ ≤ 2 := by simpa only [mul_one] using he
  have hUn : kepLogSlopeNorm U ≤ 2 * kepLogSlopeNorm R := by
    have he : U = fun s => (Real.exp s / D) * R s := by funext s; dsimp [U]; ring
    rw [he]
    exact kepLogSlopeNorm_mul_bound (Real.continuous_exp.div_const D) hR hc
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left hUn (by positivity : 0 ≤
    2 * (i + k : ℕ) * (w + (i + k : ℕ)) * (1 + C * w) ^ 2 * C * B *
      Real.exp (-r * (i + k : ℕ)))
  convert hm using 1
  ring

end

end PGM
