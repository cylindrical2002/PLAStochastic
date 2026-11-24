import PLAStochastic.Index.CEPS.Scaled.BoundedSpatialG

/-! # Class-uniform denominator separation on a bounded two-root disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledBoundedSpatialG_deriv_zero_lower {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {μ q w b : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 8) (hq : ‖q‖ < dom.q₀ / 2)
    (hw : ‖w - 1‖ ≤ 1 / 2) (hb : ‖b‖ ≤ 1 / (4 * (1 + dom.canonSurrogatePiBound N M))) :
    dom.boundedSpatialWeightLower N M / 4 ≤ ‖deriv (cepsScaledBoundedSpatialG dom ρW N μ q w b) 0‖ := by
  let W := cepsCanonSurrogateWeight dom ρW N μ q
  have hP : 0 ≤ dom.canonSurrogatePiBound N M := by
    have := CepsCanonDomain.v_pos hW hθ hD
    have := cepsVarLo_pos hD
    have := dom.c₀_pos
    unfold CepsCanonDomain.canonSurrogatePiBound
    positivity
  have hmul := (le_div_iff₀ (by positivity : 0 < 4 * (1 + dom.canonSurrogatePiBound N M))).mp hb
  have hbp : ‖b‖ * dom.canonSurrogatePiBound N M ≤ 1 / 4 := by nlinarith [norm_nonneg b]
  have hrel := cepsCanonSurrogateWeight_deriv_relative_bound dom hW hθ hD hf hη hM N hN hμ hq
    (show ‖(0 : ℂ)‖ ≤ dom.c₀ / 4 by simpa only [norm_zero] using (div_pos dom.c₀_pos (by norm_num : (0 : ℝ) < 4)).le)
  have hpert : ‖b * deriv W 0‖ ≤ ‖W 0‖ / 4 := by
    rw [norm_mul]
    calc
      _ ≤ ‖b‖ * (dom.canonSurrogatePiBound N M * ‖W 0‖) := mul_le_mul_of_nonneg_left hrel (norm_nonneg _)
      _ = (‖b‖ * dom.canonSurrogatePiBound N M) * ‖W 0‖ := by ring
      _ ≤ (1 / 4) * ‖W 0‖ := mul_le_mul_of_nonneg_right hbp (norm_nonneg _)
      _ = _ := by ring
  have hwlo : 1 / 2 ≤ ‖w‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) w
    rw [norm_one, norm_sub_rev] at ht
    linarith
  have hmain : ‖W 0‖ / 2 ≤ ‖w * W 0‖ := by
    rw [norm_mul]
    nlinarith [mul_le_mul_of_nonneg_right hwlo (norm_nonneg (W 0))]
  have hlo := (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ hq.le
    (show ‖(0 : ℂ)‖ ≤ dom.c₀ / 2 by simpa only [norm_zero] using (half_pos dom.c₀_pos).le)).1
  change dom.boundedSpatialWeightLower N M ≤ ‖W 0‖ at hlo
  have ht := norm_sub_norm_le (w * W 0) (b * deriv W 0)
  have he : ‖w * W 0 - b * deriv W 0‖ = ‖deriv (cepsScaledBoundedSpatialG dom ρW N μ q w b) 0‖ := by
    rw [cepsScaledBoundedSpatialG_deriv_zero dom hW hθ hD hf hη N hN hμ hq]
    rw [← norm_neg (w * W 0 - b * deriv W 0)]
    congr 1
    dsimp only [W]
    ring
  rw [he] at ht
  linarith

include hW hθ hD in
theorem cepsScaledBoundedSpatialSlope_lower {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {μ q w b a p : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 8) (hq : ‖q‖ < dom.q₀ / 2)
    (hw : ‖w - 1‖ ≤ 1 / 2) (hb : ‖b‖ ≤ dom.c₀ / 4)
    (hbP : ‖b‖ ≤ 1 / (4 * (1 + dom.canonSurrogatePiBound N M)))
    (ha : ‖a‖ ≤ dom.boundedSpatialRootRadius N M) (hp : ‖p‖ ≤ dom.boundedSpatialRootRadius N M) :
    dom.boundedSpatialWeightLower N M / 8 ≤ ‖dslope (cepsScaledBoundedSpatialG dom ρW N μ q w b) a p‖ := by
  have hw2 : ‖w‖ ≤ 2 := by
    have ht := norm_add_le (w - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at ht
    linarith
  obtain ⟨hd, hbound⟩ := cepsScaledBoundedSpatialG_budget dom hW hθ hD hf hη hM N hN hμ hq hw2 hb
  have hLo := cepsScaledBoundedSpatialG_deriv_zero_lower dom hW hθ hD hf hη hM N hN hμ hq hw hbP
  have haB : a ∈ ball (0 : ℂ) ((1 : ℝ) / 2) := mem_ball_zero_iff.mpr
    ((ha.trans (min_le_left _ _)).trans_lt (by norm_num : (1 : ℝ) / 4 < 1 / 2))
  have hpB : p ∈ ball (0 : ℂ) ((1 : ℝ) / 2) := mem_ball_zero_iff.mpr
    ((hp.trans (min_le_left _ _)).trans_lt (by norm_num : (1 : ℝ) / 4 < 1 / 2))
  have hK := boundedSpatialGUpper_pos dom hW hθ hD N M
  have hratio := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 512) hK)).mp
    (show dom.boundedSpatialRootRadius N M ≤ dom.boundedSpatialWeightLower N M /
      (512 * dom.boundedSpatialGUpper N M) from min_le_right _ _)
  have hsum : ‖a‖ + ‖p‖ ≤ 2 * dom.boundedSpatialRootRadius N M := by linarith
  have hsmall : (32 * dom.boundedSpatialGUpper N M / (1 : ℝ) ^ 2) * (‖a‖ + ‖p‖) ≤
      (dom.boundedSpatialWeightLower N M / 4) / 2 := by
    norm_num only [one_pow, div_one]
    nlinarith [mul_le_mul_of_nonneg_left hsum hK.le]
  have h := cepsNormal_dslope_norm_lower_of_near_origin (by norm_num : (0 : ℝ) < 1) hd hbound haB hpB hLo hsmall
  simpa only [div_div, show (4 : ℝ) * 2 = 8 by norm_num] using h

end PGM
