import PLAStochastic.Index.CEPS.Scaled.SurrogateOrigin

/-! # Nonzero holomorphic divided denominators, including root merging -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

theorem cepsScaledSurrogateG_root_ratio (N : ℕ) (lam : ℝ) (z b : ℂ) :
    cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b) /
      cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z (-1) b) =
        exp (-cepsScaledEffectiveGap D θ ρW lam z b) * cepsScaledSurrogatePi dom ρW N lam z b := by
  unfold cepsScaledSurrogateG cepsScaledSurrogatePi cepsScaledEffectiveGap
  rw [mul_div_mul_comm, ← exp_sub]
  congr 2
  ring

include hW hθ hD in
theorem cepsScaledSurrogateG_root_ne_zero {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {sign : ℂ} (hsign : ‖sign‖ ≤ 1) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z sign b) ≠ 0 := by
  obtain ⟨hμ, hq, hζ⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz hsign hb
  have hlo := (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ.le hq.le hζ.le).1
  have hpos : 0 < cepsVarLo D / 4 *
      Real.exp (-2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) :=
    mul_pos (div_pos (cepsVarLo_pos hD) (by norm_num)) (Real.exp_pos _)
  exact mul_ne_zero (exp_ne_zero _) (norm_pos_iff.mp (hpos.trans_le hlo))

include hW hθ hD in
theorem cepsScaledSurrogateDelta_mul_rootG {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    cepsScaledSurrogateDelta dom ρW N lam z b *
      cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z (-1) b) =
      -(cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b) *
        cepsScaledSurrogateDenominator dom ρW N lam z b := by
  have hgm := cepsScaledSurrogateG_root_ne_zero dom hW hθ hD hf hη hM N hN lam hz
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hb
  rw [cepsScaledSurrogateDelta, ← cepsScaledSurrogateG_root_ratio dom N lam z b]
  have h := sub_smul_dslope (cepsScaledSurrogateG dom ρW N lam z b)
    (cepsScaledSignedRoot D θ ρW lam z (-1) b) (cepsScaledSignedRoot D θ ρW lam z 1 b)
  rw [smul_eq_mul] at h
  unfold cepsScaledSurrogateDenominator
  field_simp
  linear_combination h

include hW hθ hD in
theorem cepsScaledRootGap_ne_zero (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (hne : 0 < lam ^ 2 + ‖z‖) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z)) :
    cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b ≠ 0 := by
  have hcoord := (scaledCoordinateLower_pos dom hW hθ hD lam hne).trans_le
    (cepsScaledRootCoordinate_lower dom hW hθ hD N M lam hz hb)
  have he := cepsScaledRootGap_complex_sector dom hW hθ hD lam hz (ball_subset_ball (min_le_left _ _) hb)
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hre : 0 < (cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b).re :=
    (div_pos hcoord (by positivity)).trans_le he
  exact fun hz0 => by rw [hz0] at hre; simp at hre

include hW hθ hD in
theorem cepsScaledSurrogateDenominator_ne_zero {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z)) :
    cepsScaledSurrogateDenominator dom ρW N lam z b ≠ 0 := by
  have hbS : b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z) := ball_subset_ball (min_le_left _ _) hb
  have hbC : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) :=
    ball_subset_ball ((min_le_left _ _).trans (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)) hbS
  by_cases hne : 0 < lam ^ 2 + ‖z‖
  · have hc := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1
    have hR := (scaledCoordinateLower_pos dom hW hθ hD lam hne).trans_le
      (cepsScaledRootCoordinate_lower dom hW hθ hD N M lam hz hbS)
    have hΔ : cepsScaledSurrogateDelta dom ρW N lam z b ≠ 0 := norm_pos_iff.mp
      ((mul_pos (div_pos hc (by norm_num)) (lt_min (by norm_num) hR)).trans_le
        (cepsScaledSurrogateDelta_lower_bound dom hW hθ hD hf hη hM N hN lam hz hbS))
    have hgm := cepsScaledSurrogateG_root_ne_zero dom hW hθ hD hf hη hM N hN lam hz
      (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbC
    intro hS
    have hid := cepsScaledSurrogateDelta_mul_rootG dom hW hθ hD hf hη hM N hN lam hz hbC
    rw [hS, mul_zero] at hid
    exact mul_ne_zero hΔ hgm hid
  · have hl : lam = 0 := by nlinarith [norm_nonneg z, sq_nonneg lam]
    have hz0 : z = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg lam, norm_nonneg z])
    subst lam
    subst z
    apply norm_pos_iff.mp
    exact (mul_pos (div_pos (cepsVarLo_pos hD) (by norm_num)) (Real.exp_pos _)).trans_le
      (cepsScaledSurrogateDenominator_origin_bound dom hW hθ hD hf hη hM N hN hb)

include hW hθ hD in
theorem cepsScaledSurrogateGRoot_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {sign : ℂ} (hsign : ‖sign‖ ≤ 1) :
    DifferentiableOn ℂ (fun b => cepsScaledSurrogateG dom ρW N lam z b
      (cepsScaledSignedRoot D θ ρW lam z sign b)) (ball 0 (dom.canonScaleRadius lam z)) := by
  have hr : DifferentiableOn ℂ (cepsScaledSignedRoot D θ ρW lam z sign)
      (ball 0 (dom.canonScaleRadius lam z)) :=
    (cepsScaledSignedRoot_budget dom hW hθ hD lam hz hsign).1.mono
    (ball_subset_ball (min_le_left _ _))
  have hw : DifferentiableOn ℂ (fun b : ℂ => 1 + b * lam) (ball 0 (dom.canonScaleRadius lam z)) := by fun_prop
  exact ((hr.neg.mul hw).cexp).mul
    (cepsScaledSurrogateWeightRoot_differentiableOn dom hW hθ hD hf hη hM N hN lam hz hsign)

include hW hθ hD in
theorem cepsScaledSurrogateDenominator_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateDenominator dom ρW N lam z)
      (ball 0 (dom.surrogateRegularScaleRadius N M lam z)) := by
  let U := ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z)
  have hsub : U ⊆ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z) := ball_subset_ball (min_le_left _ _)
  have hsubC : U ⊆ ball (0 : ℂ) (dom.canonScaleRadius lam z) :=
    hsub.trans (ball_subset_ball ((min_le_left _ _).trans
      (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)))
  by_cases hne : 0 < lam ^ 2 + ‖z‖
  · have hdp := (cepsScaledSurrogateGRoot_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
      (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).mono hsubC
    have hdm := (cepsScaledSurrogateGRoot_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
      (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)).mono hsubC
    have hrp := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).1.mono
      (hsubC.trans (ball_subset_ball (min_le_left _ _)))
    have hrm := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)).1.mono
      (hsubC.trans (ball_subset_ball (min_le_left _ _)))
    have hraw := (hdp.sub hdm).div (hrp.sub hrm)
      (fun b hb => cepsScaledRootGap_ne_zero dom hW hθ hD N M lam hz hne (hsub hb))
    apply hraw.congr
    intro b hb
    unfold cepsScaledSurrogateDenominator
    rw [dslope_of_ne _ (sub_ne_zero.mp (cepsScaledRootGap_ne_zero dom hW hθ hD N M lam hz hne (hsub hb))),
      slope_def_field]
    rfl
  · have hl : lam = 0 := by nlinarith [norm_nonneg z, sq_nonneg lam]
    have hz0 : z = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg lam, norm_nonneg z])
    subst lam
    subst z
    have hd : DifferentiableOn ℂ (fun b : ℂ => -cepsCanonSurrogateWeight dom ρW N 0 0 0 +
      b * deriv (cepsCanonSurrogateWeight dom ρW N 0 0) 0) U := by fun_prop
    exact hd.congr fun b _ => cepsScaledSurrogateDenominator_origin dom hW hθ hD hf hη N hN b

include hW hθ hD in
theorem cepsScaledSurrogateDenominator_inverse_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (fun b => (cepsScaledSurrogateDenominator dom ρW N lam z b)⁻¹)
      (ball 0 (dom.surrogateRegularScaleRadius N M lam z)) :=
    (cepsScaledSurrogateDenominator_differentiableOn dom hW hθ hD hf hη hM N hN lam hz).inv
      (fun _ hb => cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz hb)

end PGM
