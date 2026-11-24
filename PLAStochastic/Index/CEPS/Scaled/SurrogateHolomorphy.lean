import PLAStochastic.Index.CEPS.Scaled.SurrogateDelta

/-! # Holomorphic surrogate ratios and denominator units -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.surrogatePiNormBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) : ℝ :=
  4 * v / cepsVarLo D * Real.exp (4 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateWeightRoot_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {sign : ℂ} (hsign : ‖sign‖ ≤ 1) :
    DifferentiableOn ℂ (fun b => cepsCanonSurrogateWeight dom ρW N (b * lam)
      (cepsComplexScaledDiscount lam z b) (b * cepsScaledSignedRoot D θ ρW lam z sign b))
      (ball 0 (dom.canonScaleRadius lam z)) := by
  have hQ : DifferentiableOn ℂ (fun b => cepsQ D θ ρW (b * lam)
      (cepsComplexScaledDiscount lam z b) (b * cepsScaledSignedRoot D θ ρW lam z sign b))
      (ball 0 (dom.canonScaleRadius lam z)) :=
    (cepsScaledQuotientAtRoot_budget dom hW hθ hD lam hz hsign).1.congr fun b hb =>
      (cepsScaledQuotient_eq_actual dom hW hθ hD lam hz hb _).symm
  have hL := (cepsScaledCanonRoot_budget dom hW hθ hD hf hη hM N hN lam hz hsign).1
  exact hQ.mul ((hL.const_mul (-2)).cexp)

include hW hθ hD in
theorem cepsScaledSurrogatePi_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogatePi dom ρW N lam z) (ball 0 (dom.canonScaleRadius lam z)) ∧
      ∀ b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z),
        ‖cepsScaledSurrogatePi dom ρW N lam z b‖ ≤ dom.surrogatePiNormBound N M := by
  let F := fun sign b => cepsCanonSurrogateWeight dom ρW N (b * lam)
    (cepsComplexScaledDiscount lam z b) (b * cepsScaledSignedRoot D θ ρW lam z sign b)
  let B := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  have hbnd : ∀ sign : ℂ, ‖sign‖ ≤ 1 → ∀ b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z),
      cepsVarLo D / 4 * Real.exp (-2 * B) ≤ ‖F sign b‖ ∧
        ‖F sign b‖ ≤ v * Real.exp (2 * B) := by
    intro sign hsign b hb
    obtain ⟨hμ, hq, hζ⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz hsign hb
    exact cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ.le hq.le hζ.le
  have hlo : 0 < cepsVarLo D / 4 * Real.exp (-2 * B) :=
    mul_pos (div_pos (cepsVarLo_pos hD) (by norm_num)) (Real.exp_pos _)
  have hnz : ∀ b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z), F (-1) b ≠ 0 :=
    fun b hb => norm_pos_iff.mp (hlo.trans_le (hbnd (-1) (by norm_num) b hb).1)
  refine ⟨(cepsScaledSurrogateWeightRoot_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).div
    (cepsScaledSurrogateWeightRoot_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
      (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)) hnz, fun b hb => ?_⟩
  change ‖F 1 b / F (-1) b‖ ≤ _
  rw [norm_div]
  have hden := (hbnd (-1) (by norm_num) b hb).1
  have hnum := (hbnd 1 (by norm_num) b hb).2
  have hdiv := div_le_div₀
    (mul_nonneg (CepsCanonDomain.v_pos hW hθ hD).le (Real.exp_pos _).le) hnum hlo hden
  apply hdiv.trans_eq
  have hexp : Real.exp (4 * B) * Real.exp (-2 * B) = Real.exp (2 * B) := by
    rw [← Real.exp_add]; congr 1; ring
  have hvl := (cepsVarLo_pos hD).ne'
  have hex0 := (Real.exp_pos (-2 * B)).ne'
  unfold CepsCanonDomain.surrogatePiNormBound
  change v * Real.exp (2 * B) / (cepsVarLo D / 4 * Real.exp (-2 * B)) =
    4 * v / cepsVarLo D * Real.exp (4 * B)
  rw [div_eq_iff (mul_ne_zero (div_ne_zero hvl (by norm_num)) hex0)]
  calc
    _ = (4 * v / cepsVarLo D * (cepsVarLo D / 4)) *
        (Real.exp (4 * B) * Real.exp (-2 * B)) := by rw [hexp]; field_simp
    _ = _ := by ring

include hW hθ hD in
theorem cepsScaledSurrogateDelta_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateDelta dom ρW N lam z)
      (ball 0 (dom.surrogateScaleRadius N M lam z)) ∧
    ∀ b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z),
      ‖cepsScaledSurrogateDelta dom ρW N lam z b‖ ≤ 1 + dom.surrogatePiNormBound N M := by
  have hR := canonScaleRadius_pos dom hW hθ hD lam z
  have hsub : ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z) ⊆
      ball 0 (dom.canonScaleRadius lam z) :=
    ball_subset_ball ((min_le_left _ _).trans (half_le_self hR.le))
  have hp := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).1.mono
    (hsub.trans (ball_subset_ball (min_le_left _ _)))
  have hn := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)).1.mono
    (hsub.trans (ball_subset_ball (min_le_left _ _)))
  have he : DifferentiableOn ℂ (cepsScaledEffectiveGap D θ ρW lam z)
      (ball 0 (dom.surrogateScaleRadius N M lam z)) :=
    (hp.sub hn).mul ((differentiableOn_const _).add (differentiableOn_id.mul_const _))
  obtain ⟨hPi, hbound⟩ := cepsScaledSurrogatePi_budget dom hW hθ hD hf hη hM N hN lam hz
  refine ⟨(differentiableOn_const _).sub (he.neg.cexp.mul (hPi.mono hsub)), fun b hb => ?_⟩
  have hsector := cepsScaledEffectiveGap_sector dom hW hθ hD N M lam hz hb
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1
  have he0 : 0 ≤ (cepsScaledEffectiveGap D θ ρW lam z b).re :=
    (mul_nonneg hc.le (norm_nonneg _)).trans hsector
  have hExp : ‖exp (-cepsScaledEffectiveGap D θ ρW lam z b)‖ ≤ 1 := by
    rw [norm_exp, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by simpa using he0)
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖exp (-cepsScaledEffectiveGap D θ ρW lam z b) *
      cepsScaledSurrogatePi dom ρW N lam z b‖ := norm_sub_le _ _
    _ ≤ 1 + dom.surrogatePiNormBound N M := by
      rw [norm_one, norm_mul]
      have ht := (mul_le_mul_of_nonneg_right hExp (norm_nonneg _)).trans
        (by simpa using hbound b (hsub hb))
      linarith

end PGM
