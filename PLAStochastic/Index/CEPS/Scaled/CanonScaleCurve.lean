import PLAStochastic.Index.CEPS.Scaled.CanonDriftTaylor
import PLAStochastic.Index.CEPS.Scaled.RootZero

/-! # Uniform complex-scale canonical surrogates along the actual roots -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ}

def cepsComplexScaledDiscount (lam : ℝ) (z b : ℂ) : ℂ := b ^ 2 * z * (1 + b * lam)

def CepsCanonDomain.canonScaleBase (dom : CepsCanonDomain D θ v) : ℝ :=
  min 1 (min (dom.μ₀ / 8) (min (dom.q₀ / 8) (dom.c₀ / 4)))

def CepsCanonDomain.canonScaleRadius (dom : CepsCanonDomain D θ v) (lam : ℝ) (z : ℂ) : ℝ :=
  min (dom.actualRootScaleRadius lam z)
    (dom.canonScaleBase / (1 + |lam| + Real.sqrt ‖z‖ + dom.actualScaledRootBound lam z))

def cepsScaledCanonRoot (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (N : ℕ) (lam : ℝ) (z sign b : ℂ) : ℂ :=
  cepsCanonDriftTaylor dom ρW N (b * lam) (cepsComplexScaledDiscount lam z b)
    (b * cepsScaledSignedRoot D θ ρW lam z sign b)

variable {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem canonScaleRadius_pos (lam : ℝ) (z : ℂ) : 0 < dom.canonScaleRadius lam z := by
  have hC : 0 ≤ dom.actualScaledRootBound lam z := by
    unfold CepsCanonDomain.actualScaledRootBound
    have := cepsVarLo_pos hD
    have := cepsChartK_pos hD
    have := Real.sqrt_nonneg (2 * (‖z‖ + lam ^ 2 / (2 * cepsVarLo D)))
    change 0 ≤ 2 / cepsVarLo D * |lam| + cepsChartK D * Real.sqrt _
    positivity
  unfold CepsCanonDomain.canonScaleRadius CepsCanonDomain.canonScaleBase
  exact lt_min (actualRootScaleRadius_pos dom hW hθ hD lam z)
    (div_pos (by have := dom.μ₀_pos; have := dom.q₀_pos; have := dom.c₀_pos; positivity)
      (by positivity))

include hW hθ hD in
theorem canonScaleCurve_bounds (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    ‖b * (lam : ℂ)‖ < dom.μ₀ / 8 ∧
    ‖cepsComplexScaledDiscount lam z b‖ < dom.q₀ / 2 ∧
    ‖b * cepsScaledSignedRoot D θ ρW lam z sign b‖ < dom.c₀ / 2 := by
  let C := dom.actualScaledRootBound lam z
  let A := dom.canonScaleBase
  have hC : 0 ≤ C := (norm_nonneg _).trans
    ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz hsign).2 0
      (mem_ball_self (actualRootScaleRadius_pos dom hW hθ hD lam z)))
  have hA1 : A ≤ 1 := min_le_left _ _
  have hAm : A ≤ dom.μ₀ / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hAq : A ≤ dom.q₀ / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hAc : A ≤ dom.c₀ / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsub : b ∈ ball (0 : ℂ) (dom.actualRootScaleRadius lam z) :=
    ball_subset_ball (min_le_left _ _) hb
  have ht : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖ + C) < A := by
    apply (lt_div_iff₀ (by positivity : 0 < 1 + |lam| + Real.sqrt ‖z‖ + C)).mp
    exact (mem_ball_zero_iff.mp hb).trans_le (min_le_right _ _)
  have hb1 : ‖b‖ ≤ 1 := by nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖, norm_nonneg b]
  have hbl : ‖b‖ * |lam| < A := by
    nlinarith [norm_nonneg b, mul_nonneg (norm_nonneg b) hC,
      mul_nonneg (norm_nonneg b) (Real.sqrt_nonneg ‖z‖)]
  have hbs : ‖b‖ * Real.sqrt ‖z‖ < A := by
    nlinarith [norm_nonneg b, mul_nonneg (norm_nonneg b) hC,
      mul_nonneg (norm_nonneg b) (abs_nonneg lam)]
  have hbC : ‖b‖ * C < A := by
    nlinarith [mul_nonneg (norm_nonneg b) (Real.sqrt_nonneg ‖z‖),
      mul_nonneg (norm_nonneg b) (abs_nonneg lam)]
  have hA0 : 0 ≤ A := (mul_nonneg (norm_nonneg b) (Real.sqrt_nonneg ‖z‖)).trans hbs.le
  have hbz : ‖b‖ ^ 2 * ‖z‖ ≤ A := by
    have hnon : 0 ≤ ‖b‖ * Real.sqrt ‖z‖ := by positivity
    have hAle : 0 ≤ A := hnon.trans hbs.le
    have hs := Real.sq_sqrt (norm_nonneg z)
    nlinarith [sq_nonneg (A - ‖b‖ * Real.sqrt ‖z‖), mul_nonneg hAle (by linarith : 0 ≤ 1 - A)]
  refine ⟨by simpa only [norm_mul, norm_real, Real.norm_eq_abs] using hbl.trans_le hAm, ?_, ?_⟩
  · have he : ‖1 + b * (lam : ℂ)‖ ≤ 2 := by
      calc
        _ ≤ ‖(1 : ℂ)‖ + ‖b * (lam : ℂ)‖ := norm_add_le _ _
        _ ≤ 2 := by rw [norm_one, norm_mul, norm_real, Real.norm_eq_abs]; linarith
    rw [cepsComplexScaledDiscount, norm_mul, norm_mul, norm_pow]
    calc
      ‖b‖ ^ 2 * ‖z‖ * ‖1 + b * (lam : ℂ)‖ ≤ A * 2 :=
        mul_le_mul hbz he (norm_nonneg _) hA0
      _ ≤ dom.q₀ / 4 := by linarith
      _ < dom.q₀ / 2 := by linarith [dom.q₀_pos]
  · rw [norm_mul]
    apply (mul_le_mul_of_nonneg_left
      ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz hsign).2 b hsub) (norm_nonneg b)).trans_lt
    exact (hbC.trans_le hAc).trans (by linarith [dom.c₀_pos])

include hW hθ hD in
theorem cepsScaledCanonRoot_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {sign : ℂ} (hsign : ‖sign‖ ≤ 1) :
    DifferentiableOn ℂ (cepsScaledCanonRoot dom ρW N lam z sign)
      (ball 0 (dom.canonScaleRadius lam z)) ∧
    ∀ b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z),
      ‖cepsScaledCanonRoot dom ρW N lam z sign b‖ ≤ dom.canonDriftTaylorBound N M (dom.μ₀ / 8) := by
  have hroot : DifferentiableOn ℂ (cepsScaledSignedRoot D θ ρW lam z sign)
      (ball 0 (dom.canonScaleRadius lam z)) := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz hsign).1.mono
    (ball_subset_ball (min_le_left _ _))
  have hcurve : DifferentiableOn ℂ
      (fun b : ℂ => (b * (lam : ℂ),
        (cepsComplexScaledDiscount lam z b, b * cepsScaledSignedRoot D θ ρW lam z sign b)))
      (ball 0 (dom.canonScaleRadius lam z)) := by
    apply (differentiableOn_id.mul_const (lam : ℂ)).prodMk
    apply DifferentiableOn.prodMk
    · unfold cepsComplexScaledDiscount
      fun_prop
    · exact differentiableOn_id.mul hroot
  have hmap : MapsTo
      (fun b : ℂ => (b * (lam : ℂ),
        (cepsComplexScaledDiscount lam z b, b * cepsScaledSignedRoot D θ ρW lam z sign b)))
      (ball 0 (dom.canonScaleRadius lam z))
      {x : ℂ × (ℂ × ℂ) | x.2.2.re < dom.c₀ ∧ ‖x.2.1‖ < dom.q₀ / 2} := by
    intro b hb
    obtain ⟨_, hq, hζ⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz hsign hb
    exact ⟨(re_le_norm _).trans_lt (hζ.trans (by linarith [dom.c₀_pos])), hq⟩
  have hd := (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp hcurve hmap
  refine ⟨?_, fun b hb => ?_⟩
  · simpa only [cepsScaledCanonRoot, Function.comp_apply] using! hd
  · obtain ⟨hμ, hq, hζ⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz hsign hb
    exact cepsCanonDriftTaylor_norm_le dom hW hθ hD hf hη hM N hN hμ.le hq.le hζ.le

include hW hθ hD in
theorem cepsScaledCanonRoot_approx {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {sign : ℂ} (hsign : ‖sign‖ ≤ 1) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    ‖dom.canonL ρW ((b * lam : ℝ) : ℂ) (cepsScaledDiscount b lam z)
        ((b : ℂ) * cepsScaledSignedRoot D θ ρW lam z sign b) -
      cepsScaledCanonRoot dom ρW N lam z sign b‖ ≤
        dom.canonDriftCoeffBound (N + 1) M * |b * lam| ^ (N + 1) := by
  obtain ⟨hμ, hq, hζ⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz hsign hb
  have hμ' : |b * lam| < dom.μ₀ / 4 := by
    rw [norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at hμ
    rw [abs_mul]
    linarith [dom.μ₀_pos]
  have heq : cepsComplexScaledDiscount lam z b = cepsScaledDiscount b lam z := by
    simp only [cepsComplexScaledDiscount, cepsScaledDiscount, ofReal_mul]
  simpa only [cepsScaledCanonRoot, heq, ← ofReal_mul] using
    cepsCanonDriftTaylor_approx dom hW hθ hD hf hη hM N hN hμ' hq.le hζ.le

include hW hθ hD in
theorem cepsScaledCanonRoot_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {sign : ℂ} (hsign : ‖sign‖ ≤ 1) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2)) :
    ‖cepsScaledCanonRoot dom ρW N lam z sign b -
      complexTaylorSum (cepsScaledCanonRoot dom ρW N lam z sign) n 0 b‖ ≤
        ((n.factorial : ℝ) * dom.canonDriftTaylorBound N M (dom.μ₀ / 8) /
          (dom.canonScaleRadius lam z / 4) ^ n) * ‖b‖ ^ n := by
  obtain ⟨hd, hm⟩ := cepsScaledCanonRoot_budget dom hW hθ hD hf hη hM N hN lam hz hsign
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (canonScaleRadius_pos dom hW hθ hD lam z) hd hm hb

end PGM
