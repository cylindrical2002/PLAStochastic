import PLAStochastic.Index.CEPS.Scaled.SurrogateDeltaInverse

/-! # The genuine divided denominator at the joint origin -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogateG {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  exp (-ξ * (1 + b * lam)) * cepsCanonSurrogateWeight dom ρW N (b * lam)
    (cepsComplexScaledDiscount lam z b) (b * ξ)

def cepsScaledSurrogateDenominator {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  dslope (cepsScaledSurrogateG dom ρW N lam z b)
    (cepsScaledSignedRoot D θ ρW lam z (-1) b) (cepsScaledSignedRoot D θ ρW lam z 1 b)

def CepsCanonDomain.surrogateRegularScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M lam : ℝ) (z : ℂ) : ℝ :=
  min (dom.surrogateScaleRadius N M lam z) (1 / (4 * (1 + dom.canonSurrogatePiBound N M)))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSignedRoot_joint_origin (sign b : ℂ) :
    cepsScaledSignedRoot D θ ρW 0 0 sign b = 0 := by
  have hzero := cepsMorseRoot_zero hW hθ hD (μ := 0) (by simpa using cepsChartMu_pos hD hθ)
  rw [cepsMorseCenter_at_zero hW hθ hD] at hzero
  have hf : (fun a : ℂ => cepsMorseRoot D θ ρW (a * (0 : ℝ))
      (a * sign * cepsScaledRootCoordinate D θ ρW 0 0 a)) = fun _ : ℂ => (0 : ℂ) := by
    funext a
    simp [cepsScaledRootCoordinate, cepsScaledMorseRadicand, hzero]
  rw [cepsScaledSignedRoot, hf]
  by_cases hb : b = 0
  · subst b
    rw [dslope_same]
    simp
  · rw [dslope_of_ne _ hb, slope_def_field]
    simp

include hW hθ hD in
theorem surrogateRegularScaleRadius_pos (N : ℕ) (M lam : ℝ) (z : ℂ) :
    0 < dom.surrogateRegularScaleRadius N M lam z := by
  have hP := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.2.1
  exact lt_min (surrogateScaleRadius_pos dom hW hθ hD N M lam z) (by positivity)

include hW hθ hD in
theorem cepsScaledSurrogateG_origin_deriv {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (b : ℂ) :
    deriv (cepsScaledSurrogateG dom ρW N 0 0 b) 0 =
      -cepsCanonSurrogateWeight dom ρW N 0 0 0 +
        b * deriv (cepsCanonSurrogateWeight dom ρW N 0 0) 0 := by
  have hμ : ‖(0 : ℂ)‖ ≤ dom.μ₀ / 8 := by simpa using div_nonneg dom.μ₀_pos.le (by norm_num : (0 : ℝ) ≤ 8)
  have hq : ‖(0 : ℂ)‖ < dom.q₀ / 2 := by simpa using half_pos dom.q₀_pos
  have hdF := ((cepsCanonSurrogateWeight_differentiableOn dom hW hθ hD hf hη N hN hμ hq)
    0 (mem_ball_self (half_pos dom.c₀_pos))).differentiableAt
      (ball_mem_nhds 0 (half_pos dom.c₀_pos)) |>.hasDerivAt
  have hcurve : HasDerivAt (fun ξ : ℂ => b * ξ) b 0 := by simpa using (hasDerivAt_id' (0 : ℂ)).const_mul b
  have hF := hdF.comp_of_eq (0 : ℂ) hcurve (by simp)
  have he := ((hasDerivAt_id' (0 : ℂ)).neg.cexp).mul hF
  have hG : HasDerivAt (cepsScaledSurrogateG dom ρW N 0 0 b)
      (-cepsCanonSurrogateWeight dom ρW N 0 0 0 +
        b * deriv (cepsCanonSurrogateWeight dom ρW N 0 0) 0) 0 := by
    change HasDerivAt (fun ξ : ℂ => exp (-ξ * (1 + b * (0 : ℂ))) *
      cepsCanonSurrogateWeight dom ρW N (b * 0) (cepsComplexScaledDiscount 0 0 b) (b * ξ)) _ 0
    simpa [cepsComplexScaledDiscount, Function.comp_def, Pi.mul_def, mul_comm] using! he
  exact hG.deriv

include hW hθ hD in
theorem cepsScaledSurrogateDenominator_origin {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (b : ℂ) :
    cepsScaledSurrogateDenominator dom ρW N 0 0 b =
      -cepsCanonSurrogateWeight dom ρW N 0 0 0 +
        b * deriv (cepsCanonSurrogateWeight dom ρW N 0 0) 0 := by
  rw [cepsScaledSurrogateDenominator, cepsScaledSignedRoot_joint_origin hW hθ hD,
    cepsScaledSignedRoot_joint_origin hW hθ hD, dslope_same]
  exact cepsScaledSurrogateG_origin_deriv dom hW hθ hD hf hη N hN b

include hW hθ hD in
theorem cepsScaledSurrogateDenominator_origin_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M 0 0)) :
    cepsVarLo D / 8 * Real.exp (-2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) ≤
      ‖cepsScaledSurrogateDenominator dom ρW N 0 0 b‖ := by
  let F := cepsCanonSurrogateWeight dom ρW N 0 0
  have hμ : ‖(0 : ℂ)‖ ≤ dom.μ₀ / 8 := by simpa using div_nonneg dom.μ₀_pos.le (by norm_num : (0 : ℝ) ≤ 8)
  have hq : ‖(0 : ℂ)‖ < dom.q₀ / 2 := by simpa using half_pos dom.q₀_pos
  have hζ : ‖(0 : ℂ)‖ ≤ dom.c₀ / 4 := by simpa using div_nonneg dom.c₀_pos.le (by norm_num : (0 : ℝ) ≤ 4)
  have hD' := cepsCanonSurrogateWeight_deriv_relative_bound dom hW hθ hD hf hη hM N hN hμ hq hζ
  have hP := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.2.1
  have hsmall : ‖b‖ ≤ 1 / (4 * (1 + dom.canonSurrogatePiBound N M)) :=
    (mem_ball_zero_iff.mp hb).le.trans (min_le_right _ _)
  have hmul := (le_div_iff₀ (by positivity : 0 < 4 * (1 + dom.canonSurrogatePiBound N M))).mp hsmall
  have hbp : ‖b‖ * dom.canonSurrogatePiBound N M ≤ 1 / 4 := by nlinarith [norm_nonneg b]
  have hpert : ‖b * deriv F 0‖ ≤ ‖F 0‖ / 4 := by
    rw [norm_mul]
    calc
      _ ≤ ‖b‖ * (dom.canonSurrogatePiBound N M * ‖F 0‖) :=
        mul_le_mul_of_nonneg_left hD' (norm_nonneg b)
      _ = (‖b‖ * dom.canonSurrogatePiBound N M) * ‖F 0‖ := by ring
      _ ≤ (1 / 4) * ‖F 0‖ := mul_le_mul_of_nonneg_right hbp (norm_nonneg _)
      _ = _ := by ring
  have htri := norm_sub_norm_le (F 0) (b * deriv F 0)
  have he : ‖F 0 - b * deriv F 0‖ = ‖cepsScaledSurrogateDenominator dom ρW N 0 0 b‖ := by
    rw [cepsScaledSurrogateDenominator_origin dom hW hθ hD hf hη N hN]
    rw [← norm_neg (F 0 - b * deriv F 0)]
    congr 1
    dsimp only [F]
    ring
  rw [he] at htri
  have hlo := (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ hq.le
    (show ‖(0 : ℂ)‖ ≤ dom.c₀ / 2 by simpa using (half_pos dom.c₀_pos).le)).1
  change _ ≤ ‖F 0‖ at hlo
  nlinarith [norm_nonneg (F 0)]

end PGM
