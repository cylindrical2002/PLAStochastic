import PLAStochastic.Index.GEP.Kernel.BV.Scale

/-!
# Scalar estimates for the far-slope kernel region

These estimates separate displacement and killed-time exponential decay and
choose logarithmic cutoffs after a fixed polynomial exponent. They are scalar
consequences used after the actual tilted-kernel bounds, not replacements for
those bounds.
-/

namespace PGM
noncomputable section

theorem kBV_crossing_energy {d w N : ℝ} (hN : 0 < N) :
    2 * w * |d| ≤ d ^ 2 * N + w ^ 2 / N := by
  apply (mul_le_mul_iff_right₀ hN).mp
  rw [mul_comm N (2 * w * |d|), mul_comm N (d ^ 2 * N + w ^ 2 / N)]
  have hs := sq_nonneg (|d| * N - w)
  have he : (|d| * N - w) ^ 2 = d ^ 2 * N ^ 2 - 2 * w * |d| * N + w ^ 2 := by
    rw [← sq_abs d]
    ring
  rw [he] at hs
  calc 2 * w * |d| * N ≤ d ^ 2 * N ^ 2 + w ^ 2 := by linarith
       _ = (d ^ 2 * N + w ^ 2 / N) * N := by
         rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hN)]
         ring

/-- Crossing suppression keeps the complete killed-time exponential factor. -/
theorem kBV_farSlope_exp_split {c d w N : ℝ} (hc : 0 ≤ c) (hw : 0 ≤ w) (hN : 0 < N) :
    Real.exp (-c * (d ^ 2 * N + w ^ 2 / N + N / w ^ 2)) ≤
      Real.exp (-c * w * |d|) * Real.exp (-c * N / w ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hE := kBV_crossing_energy (d := d) (w := w) hN
  have hsmall : w * |d| ≤ d ^ 2 * N + w ^ 2 / N := by
    nlinarith [mul_nonneg hw (abs_nonneg d)]
  have hmul := mul_le_mul_of_nonneg_left (add_le_add_right hsmall (N / w ^ 2)) hc
  calc -c * (d ^ 2 * N + w ^ 2 / N + N / w ^ 2) =
        -(c * (d ^ 2 * N + w ^ 2 / N + N / w ^ 2)) := by ring
       _ ≤ -(c * (w * |d| + N / w ^ 2)) := neg_le_neg (by simpa only [add_comm] using hmul)
       _ = -c * w * |d| + -c * N / w ^ 2 := by ring

/-- Outside the logarithmic slope window the decay separates into the window
factor and an unchanged time factor. -/
theorem kBV_farSlope_window {c d w N A : ℝ} (hc : 0 ≤ c) (hw : 0 ≤ w) (hN : 0 < N)
    (hA : A ≤ w * |d|) :
    Real.exp (-c * (d ^ 2 * N + w ^ 2 / N + N / w ^ 2)) ≤
      Real.exp (-c * A) * Real.exp (-c * N / w ^ 2) := by
  refine (kBV_farSlope_exp_split hc hw hN).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hA hc
  nlinarith

theorem kBV_log_cutoff_eq {w : ℝ} (hw : 0 < w) (P c K : ℝ) :
    w ^ P * Real.exp (-c * (K * Real.log w)) = w ^ (P - c * K) := by
  rw [Real.rpow_def_of_pos hw, Real.rpow_def_of_pos hw, ← Real.exp_add]
  congr 1
  ring

/-- An explicit logarithmic cutoff absorbs any fixed polynomial power. -/
theorem kBV_log_cutoff_absorbs (P B : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ K > 0, ∀ w : ℝ, 1 ≤ w →
      w ^ P * Real.exp (-c * (K * Real.log w)) ≤ w ^ (-B) := by
  let K := (|P| + |B| + 1) / c
  have hK : 0 < K := div_pos (by positivity) hc
  refine ⟨K, hK, ?_⟩
  intro w hw
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw
  rw [kBV_log_cutoff_eq hw0, Real.rpow_def_of_pos hw0, Real.rpow_def_of_pos hw0]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg hw)
  have hcancel : c * K = |P| + |B| + 1 := by
    dsimp [K]
    field_simp
  have hP := le_abs_self P
  have hB := le_abs_self B
  linarith

/-- The polynomial exponent is fixed before the growth-window and tail-weight
parameters. The logarithmic cutoff constant is then chosen afterwards. -/
theorem kBV_log_cutoff_with_growth (P₀ : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ b ℓ B : ℝ, ∃ K > 0, ∀ w : ℝ, 1 ≤ w →
      w ^ (P₀ + ℓ * b) * Real.exp (-c * (K * Real.log w)) ≤ w ^ (-B) := by
  intro b ℓ B
  exact kBV_log_cutoff_absorbs (P₀ + ℓ * b) B hc

theorem kBV_growth_window_exp {w b ℓ x : ℝ} (hw : 0 < w) (hℓ : 0 ≤ ℓ)
    (hx : x ≤ b * Real.log w) : Real.exp (ℓ * x) ≤ w ^ (ℓ * b) := by
  rw [Real.rpow_def_of_pos hw]
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_left hx hℓ).trans_eq (by ring)

/-- Weighted tails are reduced to a power of the width with the original fixed
polynomial exponent. No compact-interval convergence is used. -/
theorem kBV_weighted_tail_power {w ξ ζ b x : ℝ} (hw : 0 < w) (hgap : ζ ≤ ξ)
    (hx : b * Real.log w ≤ x) (P₀ : ℝ) :
    Real.exp (-ξ * x) * (w ^ P₀ * Real.exp (ζ * x)) ≤ w ^ (P₀ - (ξ - ζ) * b) := by
  have he : Real.exp (-(ξ - ζ) * x) ≤ Real.exp (-(ξ - ζ) * (b * Real.log w)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hgap)
    linarith
  calc Real.exp (-ξ * x) * (w ^ P₀ * Real.exp (ζ * x)) =
        w ^ P₀ * Real.exp (-(ξ - ζ) * x) := by
          rw [show -(ξ - ζ) * x = -ξ * x + ζ * x by ring, Real.exp_add]
          ring
       _ ≤ w ^ P₀ * Real.exp (-(ξ - ζ) * (b * Real.log w)) :=
          mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hw.le _)
       _ = w ^ (P₀ - (ξ - ζ) * b) := kBV_log_cutoff_eq hw P₀ (ξ - ζ) b

/-- After fixing the polynomial exponent and the two weights, a logarithmic
input cutoff makes the weighted tail smaller than any specified inverse power. -/
theorem kBV_weighted_tail_cutoff (P₀ : ℝ) {ξ ζ : ℝ} (hgap : ζ < ξ) (B : ℝ) :
    ∃ b > 0, ∀ w : ℝ, 1 ≤ w → ∀ x : ℝ, b * Real.log w ≤ x →
      Real.exp (-ξ * x) * (w ^ P₀ * Real.exp (ζ * x)) ≤ w ^ (-B) := by
  obtain ⟨b, hb, hcut⟩ := kBV_log_cutoff_absorbs P₀ B (sub_pos.mpr hgap)
  refine ⟨b, hb, ?_⟩
  intro w hw x hx
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have h := kBV_weighted_tail_power hw0 hgap.le hx P₀
  rw [← kBV_log_cutoff_eq hw0 P₀ (ξ - ζ) b] at h
  exact h.trans (hcut w hw)

end
end PGM
