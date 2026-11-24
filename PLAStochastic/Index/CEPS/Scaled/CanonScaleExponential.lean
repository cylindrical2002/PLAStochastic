import PLAStochastic.Index.CEPS.Scaled.CanonScaleCurve
import PLAStochastic.ForMathlib.Analysis.Complex.ExpDifference

/-! # Exponential factors of the actual-root canonical surrogates -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledCanonRoot_exp_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {sign : ℂ} (hsign : ‖sign‖ ≤ 1) (c : ℂ) :
    DifferentiableOn ℂ (fun b => exp (c * cepsScaledCanonRoot dom ρW N lam z sign b))
      (ball 0 (dom.canonScaleRadius lam z)) ∧
    ∀ b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z),
      ‖exp (c * cepsScaledCanonRoot dom ρW N lam z sign b)‖ ≤
        Real.exp (‖c‖ * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) := by
  obtain ⟨hd, hb⟩ := cepsScaledCanonRoot_budget dom hW hθ hD hf hη hM N hN lam hz hsign
  refine ⟨by simpa only using! (hd.const_mul c).cexp, fun b hbb => ?_⟩
  apply (norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb b hbb) (norm_nonneg c)

include hW hθ hD in
theorem cepsScaledCanonRoot_exp_approx {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {sign : ℂ} (hsign : ‖sign‖ ≤ 1) (c : ℂ) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    ‖exp (c * dom.canonL ρW ((b * lam : ℝ) : ℂ) (cepsScaledDiscount b lam z)
        ((b : ℂ) * cepsScaledSignedRoot D θ ρW lam z sign b)) -
      exp (c * cepsScaledCanonRoot dom ρW N lam z sign b)‖ ≤
      (Real.exp (‖c‖ * (dom.normalLogBound + dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
        ‖c‖ * dom.canonDriftCoeffBound (N + 1) M) * |b * lam| ^ (N + 1) := by
  let A := dom.canonL ρW ((b * lam : ℝ) : ℂ) (cepsScaledDiscount b lam z)
    ((b : ℂ) * cepsScaledSignedRoot D θ ρW lam z sign b)
  let B := cepsScaledCanonRoot dom ρW N lam z sign b
  let K := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  obtain ⟨hμ, hq, hζ⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz hsign hb
  have heq : cepsComplexScaledDiscount lam z b = cepsScaledDiscount b lam z := by
    simp only [cepsComplexScaledDiscount, cepsScaledDiscount, ofReal_mul]
  have hA : ‖A‖ ≤ dom.normalLogBound := by
    apply dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
      (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos])
    · simpa only [ofReal_mul] using hμ.le.trans (by linarith [dom.μ₀_pos])
    · exact ofReal_im _
    · rw [← heq]; exact hq.le.trans (half_le_self dom.q₀_pos.le)
    · exact hζ.le
  have hB : ‖B‖ ≤ K :=
    (cepsScaledCanonRoot_budget dom hW hθ hD hf hη hM N (by omega) lam hz hsign).2 b hb
  have hA0 : 0 ≤ dom.normalLogBound := (norm_nonneg A).trans hA
  have hB0 : 0 ≤ K := (norm_nonneg B).trans hB
  have h := norm_cexp_sub_cexp_le
    (M := ‖c‖ * (dom.normalLogBound + K))
    (a := c * A) (b := c * B)
    (by rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg c); linarith)
    (by rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg c); linarith)
  have he : ‖A - B‖ ≤ dom.canonDriftCoeffBound (N + 1) M * |b * lam| ^ (N + 1) :=
    cepsScaledCanonRoot_approx dom hW hθ hD hf hη hM N hN lam hz hsign hb
  rw [← mul_sub, norm_mul] at h
  exact h.trans (by
    change _ ≤ (Real.exp (‖c‖ * (dom.normalLogBound + K)) * ‖c‖ *
      dom.canonDriftCoeffBound (N + 1) M) * |b * lam| ^ (N + 1)
    calc
      _ ≤ Real.exp (‖c‖ * (dom.normalLogBound + K)) *
          (‖c‖ * (dom.canonDriftCoeffBound (N + 1) M * |b * lam| ^ (N + 1))) := by gcongr
      _ = _ := by ring)

include hW hθ hD in
theorem cepsScaledCanonRoot_exp_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {sign : ℂ} (hsign : ‖sign‖ ≤ 1)
    (c : ℂ) (n : ℕ) {b : ℂ} (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2)) :
    ‖exp (c * cepsScaledCanonRoot dom ρW N lam z sign b) -
      complexTaylorSum (fun b => exp (c * cepsScaledCanonRoot dom ρW N lam z sign b)) n 0 b‖ ≤
      ((n.factorial : ℝ) * Real.exp (‖c‖ * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) /
        (dom.canonScaleRadius lam z / 4) ^ n) * ‖b‖ ^ n := by
  obtain ⟨hd, hm⟩ := cepsScaledCanonRoot_exp_budget dom hW hθ hD hf hη hM N hN lam hz hsign c
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (canonScaleRadius_pos dom hW hθ hD lam z) hd hm hb

include hW hθ hD in
/-- Taylor approximation of the true factor exponential using the analytic surrogate. -/
theorem cepsScaledCanonRoot_actual_exp_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {sign : ℂ} (hsign : ‖sign‖ ≤ 1) (c : ℂ) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2)) :
    ‖exp (c * dom.canonL ρW ((b * lam : ℝ) : ℂ) (cepsScaledDiscount b lam z)
        ((b : ℂ) * cepsScaledSignedRoot D θ ρW lam z sign b)) -
      complexTaylorSum (fun b => exp (c * cepsScaledCanonRoot dom ρW N lam z sign b)) (N + 1) 0 b‖ ≤
      (Real.exp (‖c‖ * (dom.normalLogBound + dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
        ‖c‖ * dom.canonDriftCoeffBound (N + 1) M) * |b * lam| ^ (N + 1) +
      (((N + 1).factorial : ℝ) * Real.exp (‖c‖ * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) /
        (dom.canonScaleRadius lam z / 4) ^ (N + 1)) * |b| ^ (N + 1) := by
  have ha := cepsScaledCanonRoot_exp_approx dom hW hθ hD hf hη hM N hN lam hz hsign c
    (ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le) hb)
  have ht := cepsScaledCanonRoot_exp_taylor_le dom hW hθ hD hf hη hM N (by omega)
    lam hz hsign c (N + 1) hb
  rw [norm_real, Real.norm_eq_abs] at ht
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add ha ht)

end PGM
