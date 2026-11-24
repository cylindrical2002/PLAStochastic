import PLAStochastic.Index.CEPS.Scaled.CombinedRootDirections

/-! # Complex-width sectors for both cubic root combinations -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

private theorem rotate_combined_root {a u : ℂ} {R H v : ℝ}
    (hR : 0 ≤ R) (hH : 0 < H) (hv : 0 < Real.sqrt v)
    (hre : R / (8 * Real.sqrt v) ≤ a.re) (hn : ‖a‖ ≤ 3 * H * R)
    (hu : ‖u‖ ≤ 1 / (48 * Real.sqrt v * H)) :
    R / (16 * Real.sqrt v) ≤ (a * (1 + u)).re := by
  have hp : ‖a * u‖ ≤ R / (16 * Real.sqrt v) := by
    rw [norm_mul]
    calc
      _ ≤ (3 * H * R) * (1 / (48 * Real.sqrt v * H)) :=
        mul_le_mul hn hu (norm_nonneg _) (by positivity)
      _ = _ := by field_simp; ring
  have hneg := (neg_le_abs (a * u).re).trans ((abs_re_le_norm _).trans hp)
  rw [mul_add, mul_one, add_re]
  ring_nf at hre hneg ⊢
  linarith

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledCombinedRoots_width_lower (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.positiveCorrectionScaleRadius N M lam z)) :
    (‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (16 * Real.sqrt v) ≤
      ((2 * cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b) * (1 + b * lam)).re) ∧
    (‖cepsScaledRootCoordinate D θ ρW lam z b‖ / (16 * Real.sqrt v) ≤
      ((cepsScaledSignedRoot D θ ρW lam z 1 b - 2 * cepsScaledSignedRoot D θ ρW lam z (-1) b) * (1 + b * lam)).re) := by
  have hbD := ball_subset_ball (min_le_left _ _) hb
  obtain ⟨hbC, hμ, _⟩ := complexDirectionScaleCurve_bounds dom N M lam hbD
  let R := ‖cepsScaledRootCoordinate D θ ρW lam z b‖
  let H := dom.complexIndividualRootBound
  let p := cepsScaledSignedRoot D θ ρW lam z 1 b
  let m := cepsScaledSignedRoot D θ ρW lam z (-1) b
  have hH : 0 < H := complexIndividualRootBound_pos dom hW hθ hD
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hdirs := cepsScaledCombinedRoots_real_lower dom hW hθ hD lam hz hbC hμ
  have hn1 : ‖2 * p - m‖ ≤ 3 * H * R := cepsScaledPositiveCorrectionRoot_norm_le dom hW hθ hD lam hz hbC hμ
  have hn2 : ‖p - 2 * m‖ ≤ 3 * H * R := by
    have hp := cepsScaledRoot_individual_norm_le dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbC hμ
    have hm := cepsScaledRoot_individual_norm_le dom hW hθ hD lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbC hμ
    have ht := norm_sub_le p (2 * m)
    rw [norm_mul] at ht
    norm_num at ht
    nlinarith
  have ht : ‖b‖ * (1 + |lam|) < 1 / (48 * Real.sqrt v * H) :=
    (lt_div_iff₀ (by positivity : 0 < 1 + |lam|)).mp
      ((mem_ball_zero_iff.mp hb).trans_le (min_le_right _ _))
  have hu : ‖b * (lam : ℂ)‖ ≤ 1 / (48 * Real.sqrt v * H) := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg b]
  exact ⟨rotate_combined_root (norm_nonneg _) hH hv hdirs.1 hn1 hu,
    rotate_combined_root (norm_nonneg _) hH hv hdirs.2 hn2 hu⟩

end PGM
