import PLAStochastic.Index.CEPS.Scaled.SurrogateMarkHolomorphy

/-! # Doubled marked factors for pole-cancelled endpoint amplitudes -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueDoubleMarkPrefactor {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  exp (2 * dom.canonL ρW (b * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z)) /
    cepsQ D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z)

def cepsScaledSurrogateDoubleMarkPrefactor {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  exp (2 * cepsCanonDriftTaylor dom ρW N (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) /
    cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)

def CepsCanonDomain.doubleMarkErrorConstant {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) : ℝ :=
  2 * Real.exp (2 * (dom.normalLogBound + dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
    dom.canonDriftCoeffBound (N + 1) M * (4 / cepsVarLo D)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueDoubleMarkPrefactor_budget (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueDoubleMarkPrefactor dom ρW lam z b‖ ≤
      Real.exp (2 * dom.normalLogBound) * (4 / cepsVarLo D) := by
  have hL := cepsScaledTrueMarkLog_budget dom hW hθ hD N M lam hz hb
  have hQ := cepsScaledSurrogateMarkQuotient_inverse_budget dom hW hθ hD N M lam hz hb
  unfold cepsScaledTrueDoubleMarkPrefactor
  rw [div_eq_mul_inv, norm_mul, norm_exp]
  apply mul_le_mul ?_ hQ (norm_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  change (((2 : ℝ) : ℂ) * _).re ≤ _
  rw [re_ofReal_mul]
  exact mul_le_mul_of_nonneg_left ((re_le_norm _).trans hL) (by norm_num)

include hD in
theorem doubleMarkErrorConstant_nonneg {M : ℝ} (hM : 0 ≤ M) (N : ℕ) :
    0 ≤ dom.doubleMarkErrorConstant N M := by
  have := dom.jetC_nonneg hD N
  have := dom.c₀_pos
  have := cepsVarLo_pos hD
  unfold CepsCanonDomain.doubleMarkErrorConstant CepsCanonDomain.canonDriftCoeffBound
  positivity

include hW hθ hD in
theorem cepsScaledTrueDoubleMarkPrefactor_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueDoubleMarkPrefactor dom ρW lam z b -
      cepsScaledSurrogateDoubleMarkPrefactor dom ρW N lam z b‖ ≤
        dom.doubleMarkErrorConstant N M * |b * lam| ^ (N + 1) := by
  let A := dom.canonL ρW (b * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z)
  let B := cepsCanonDriftTaylor dom ρW N ((b : ℂ) * lam)
    (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z)
  let K := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  have hbase := entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam hb
    (entranceScaleCurve_mark_mem dom hD N M lam hb)
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbase.1
  have hζ : ‖(b : ℂ) ^ 2 * z‖ ≤ dom.c₀ / 2 := by simpa only [pow_two, mul_assoc] using hbase.2.le
  have hA : ‖A‖ ≤ dom.normalLogBound := cepsScaledTrueMarkLog_budget dom hW hθ hD N M lam hz hb
  have hB : ‖B‖ ≤ K := cepsCanonDriftTaylor_norm_le dom hW hθ hD hf hη hM N (by omega) hμ.le hq.le hζ
  have hA0 : 0 ≤ dom.normalLogBound := (norm_nonneg A).trans hA
  have hB0 : 0 ≤ K := (norm_nonneg B).trans hB
  have hExp := norm_cexp_sub_cexp_le (M := 2 * (dom.normalLogBound + K)) (a := 2 * A) (b := 2 * B)
    (by rw [norm_mul, norm_ofNat]; nlinarith)
    (by rw [norm_mul, norm_ofNat]; nlinarith)
  have hμr : |b * lam| < dom.μ₀ / 4 := by
    have ht : ‖((b * lam : ℝ) : ℂ)‖ < dom.μ₀ / 8 := by simpa only [ofReal_mul] using hμ
    rw [norm_real, Real.norm_eq_abs] at ht
    linarith [dom.μ₀_pos]
  have hErr := cepsCanonDriftTaylor_approx dom hW hθ hD hf hη hM N hN hμr hq.le hζ
  rw [ofReal_mul] at hErr
  have hQ := cepsScaledSurrogateMarkQuotient_inverse_budget dom hW hθ hD N M lam hz hb
  unfold cepsScaledTrueDoubleMarkPrefactor cepsScaledSurrogateDoubleMarkPrefactor
  rw [← sub_div, div_eq_mul_inv, norm_mul]
  change ‖exp (2 * A) - exp (2 * B)‖ * _ ≤ _
  rw [← mul_sub, norm_mul, norm_ofNat] at hExp
  calc
    _ ≤ (Real.exp (2 * (dom.normalLogBound + K)) *
        (2 * (dom.canonDriftCoeffBound (N + 1) M * |b * lam| ^ (N + 1)))) * (4 / cepsVarLo D) :=
      mul_le_mul (hExp.trans (by gcongr)) hQ (norm_nonneg _) (by
        have := dom.jetC_nonneg hD N
        have := dom.c₀_pos
        have := (cepsSobolev_nonneg m η fW).trans hM
        unfold CepsCanonDomain.canonDriftCoeffBound
        positivity)
    _ = _ := by unfold CepsCanonDomain.doubleMarkErrorConstant; ring

end PGM
