import PLAStochastic.Index.CEPS.Scaled.RootZero
import PLAStochastic.Index.CEPS.Normal.ExtendedRootSector

/-! # Complex-scale sector of the actual square-root coordinate -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledMorseRadicand_relative_quarter (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.radicandScaleRadius lam / 2)) :
    ‖cepsScaledMorseRadicand D θ ρW lam z b - cepsScaledMorseRadicand D θ ρW lam z 0‖ ≤
      ‖cepsScaledMorseRadicand D θ ρW lam z 0‖ / 4 := by
  let F : ℂ → ℂ := fun b => cepsScaledMorseRadicand D θ ρW lam z b -
    cepsScaledMorseRadicand D θ ρW lam z 0
  let R := dom.radicandScaleRadius lam
  have hR : 0 < R := (radicandScaleRadius_budget dom hW hθ hD lam).1
  have hsub : ball (0 : ℂ) R ⊆ ball 0 (dom.minimumScaleRadius lam) :=
    ball_subset_ball ((radicandScaleRadius_budget dom hW hθ hD lam).2.trans
      (half_le_self (dom.minimumScaleRadius_pos (lam : ℂ)).le))
  have hd : DifferentiableOn ℂ F (ball 0 R) :=
    ((cepsScaledMorseRadicand_budget dom hW hθ hD (lam : ℂ) z).1.mono hsub).sub_const _
  have hF0 : F 0 = 0 := sub_self _
  have hmap : MapsTo F (ball 0 R)
      (closedBall (F 0) (‖cepsScaledMorseRadicand D θ ρW lam z 0‖ / 2)) := by
    intro b hb
    rw [mem_closedBall, hF0, dist_zero_right]
    exact cepsScaledMorseRadicand_relative dom hW hθ hD lam hz hb
  have hbR : b ∈ ball (0 : ℂ) R := ball_subset_ball (half_le_self hR.le) hb
  have hS := norm_dslope_le_div_of_mapsTo_ball hd hmap hbR
  have he := sub_smul_dslope F 0 b
  rw [sub_zero, smul_eq_mul, hF0, sub_zero] at he
  have hnorm : ‖F b‖ = ‖b‖ * ‖dslope F 0 b‖ := by rw [← he, norm_mul]
  change ‖F b‖ ≤ _
  rw [hnorm]
  calc
    _ ≤ ‖b‖ * ((‖cepsScaledMorseRadicand D θ ρW lam z 0‖ / 2) / R) :=
      mul_le_mul_of_nonneg_left hS (norm_nonneg b)
    _ ≤ (R / 2) * ((‖cepsScaledMorseRadicand D θ ρW lam z 0‖ / 2) / R) :=
      mul_le_mul_of_nonneg_right (mem_ball_zero_iff.mp hb).le (by positivity)
    _ = _ := by field_simp; ring

include hW hθ hD in
theorem cepsScaledRootCoordinate_complex_sector (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.radicandScaleRadius lam / 2)) :
    ‖cepsScaledRootCoordinate D θ ρW lam z b‖ / 2 ≤
      (cepsScaledRootCoordinate D θ ρW lam z b).re := by
  let u := cepsScaledMorseRadicand D θ ρW lam z 0
  let w := cepsScaledMorseRadicand D θ ρW lam z b
  have hu : 0 ≤ u.re := (cepsScaledMorseRadicand_zero_coercive hW hθ hD lam hz).1
  have hdiff : ‖w - u‖ ≤ ‖u‖ / 4 := cepsScaledMorseRadicand_relative_quarter dom hW hθ hD lam hz hb
  have hre := (abs_re_le_norm (w - u)).trans hdiff
  have hneg := neg_le_abs (w - u).re
  simp only [sub_re] at hre hneg
  have hn := norm_sub_norm_le u w
  rw [norm_sub_rev] at hn
  have hsector : -‖w‖ / 2 ≤ w.re := by nlinarith [norm_nonneg w]
  exact sqrt_re_ge_half_norm_of_re_ge hsector

include hW hθ hD in
theorem cepsScaledRootCoordinate_complex_coercive (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.radicandScaleRadius lam / 2)) :
    lam ^ 2 + ‖z‖ ≤ (4 * v + 4) * ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ^ 2 := by
  let u := cepsScaledMorseRadicand D θ ρW lam z 0
  let w := cepsScaledMorseRadicand D θ ρW lam z b
  have hdiff : ‖w - u‖ ≤ ‖u‖ / 4 := cepsScaledMorseRadicand_relative_quarter dom hW hθ hD lam hz hb
  have hn := norm_sub_norm_le u w
  rw [norm_sub_rev] at hn
  have hlow : ‖u‖ ≤ 2 * ‖w‖ := by linarith [norm_nonneg w]
  have hco := (cepsScaledMorseRadicand_zero_coercive hW hθ hD lam hz).2
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have h := hco.trans (mul_le_mul_of_nonneg_left hlow (by linarith : 0 ≤ 2 * v + 2))
  rw [show ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ^ 2 = ‖w‖ from norm_complex_sqrt_sq w]
  exact h.trans_eq (by ring)

end PGM
