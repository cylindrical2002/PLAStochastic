import PLAStochastic.Index.CEPS.Scaled.SurrogateDividedDenominator

/-! # The genuine regular scaled bridge for canonical Taylor surrogates -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogateBridge {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  -cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b) *
    cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z (-1) b) /
      cepsScaledSurrogateDenominator dom ρW N lam z b

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateBridge_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateBridge dom ρW N lam z)
      (ball 0 (dom.surrogateRegularScaleRadius N M lam z)) := by
  have hsub : ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z) ⊆
      ball 0 (dom.canonScaleRadius lam z) :=
    ball_subset_ball ((min_le_left _ _).trans ((min_le_left _ _).trans
      (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)))
  have hp := (cepsScaledSurrogateGRoot_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).mono hsub
  have hn := (cepsScaledSurrogateGRoot_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)).mono hsub
  exact (hp.neg.mul hn).div
    (cepsScaledSurrogateDenominator_differentiableOn dom hW hθ hD hf hη hM N hN lam hz)
      (fun _ hb => cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz hb)

include hW hθ hD in
theorem cepsScaledSurrogateBridge_mul_delta {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z)) :
    cepsScaledSurrogateBridge dom ρW N lam z b * cepsScaledSurrogateDelta dom ρW N lam z b =
      (cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b) *
        cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b) := by
  have hsub : dom.surrogateRegularScaleRadius N M lam z ≤ dom.canonScaleRadius lam z :=
    (min_le_left _ _).trans ((min_le_left _ _).trans
      (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le))
  have hid := cepsScaledSurrogateDelta_mul_rootG dom hW hθ hD hf hη hM N hN lam hz (ball_subset_ball hsub hb)
  have hS := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz hb
  unfold cepsScaledSurrogateBridge
  field_simp
  linear_combination -cepsScaledSurrogateG dom ρW N lam z b
    (cepsScaledSignedRoot D θ ρW lam z 1 b) * hid

include hW hθ hD in
theorem cepsScaledSurrogateBridge_origin {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (b : ℂ) :
    cepsScaledSurrogateBridge dom ρW N 0 0 b =
      -(cepsCanonSurrogateWeight dom ρW N 0 0 0) ^ 2 /
        (-cepsCanonSurrogateWeight dom ρW N 0 0 0 +
          b * deriv (cepsCanonSurrogateWeight dom ρW N 0 0) 0) := by
  rw [cepsScaledSurrogateBridge, cepsScaledSignedRoot_joint_origin hW hθ hD,
    cepsScaledSignedRoot_joint_origin hW hθ hD,
    cepsScaledSurrogateDenominator_origin dom hW hθ hD hf hη N hN]
  simp only [cepsScaledSurrogateG, cepsComplexScaledDiscount, ofReal_zero, mul_zero, zero_mul,
    neg_zero, exp_zero, one_mul]
  ring

include hW hθ hD in
theorem cepsScaledSurrogateBridge_origin_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M 0 0)) :
    ‖cepsScaledSurrogateBridge dom ρW N 0 0 b‖ ≤
      8 * v ^ 2 / cepsVarLo D * Real.exp (6 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) := by
  let B := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  let F := cepsCanonSurrogateWeight dom ρW N 0 0 0
  have hμ : ‖(0 : ℂ)‖ ≤ dom.μ₀ / 8 := by simpa using div_nonneg dom.μ₀_pos.le (by norm_num : (0 : ℝ) ≤ 8)
  have hq : ‖(0 : ℂ)‖ ≤ dom.q₀ / 2 := by simpa using (half_pos dom.q₀_pos).le
  have hζ : ‖(0 : ℂ)‖ ≤ dom.c₀ / 2 := by simpa using (half_pos dom.c₀_pos).le
  have hF : ‖F‖ ≤ v * Real.exp (2 * B) :=
    (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ hq hζ).2
  have hnum : ‖F‖ ^ 2 ≤ (v * Real.exp (2 * B)) ^ 2 := pow_le_pow_left₀ (norm_nonneg F) hF 2
  have hden := cepsScaledSurrogateDenominator_origin_bound dom hW hθ hD hf hη hM N hN hb
  have hlo : 0 < cepsVarLo D / 8 * Real.exp (-2 * B) :=
    mul_pos (div_pos (cepsVarLo_pos hD) (by norm_num)) (Real.exp_pos _)
  have he : cepsScaledSurrogateBridge dom ρW N 0 0 b =
      -F ^ 2 / cepsScaledSurrogateDenominator dom ρW N 0 0 b := by
    rw [cepsScaledSurrogateBridge_origin dom hW hθ hD hf hη N hN,
      cepsScaledSurrogateDenominator_origin dom hW hθ hD hf hη N hN]
  rw [he, norm_div, norm_neg, norm_pow]
  apply (div_le_div₀ (sq_nonneg _) hnum hlo hden).trans_eq
  have hexp : Real.exp (6 * B) * Real.exp (-2 * B) = (Real.exp (2 * B)) ^ 2 := by
    rw [← Real.exp_add, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hvl := (cepsVarLo_pos hD).ne'
  rw [div_eq_iff (mul_ne_zero (div_ne_zero hvl (by norm_num)) (Real.exp_ne_zero _))]
  change (v * Real.exp (2 * B)) ^ 2 =
    8 * v ^ 2 / cepsVarLo D * Real.exp (6 * B) * (cepsVarLo D / 8 * Real.exp (-2 * B))
  calc
    _ = v ^ 2 * (Real.exp (6 * B) * Real.exp (-2 * B)) := by rw [hexp, mul_pow]
    _ = _ := by field_simp

end PGM
