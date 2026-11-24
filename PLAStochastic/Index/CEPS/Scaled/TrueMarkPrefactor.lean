import PLAStochastic.Index.CEPS.Scaled.TrueBridgeError
import PLAStochastic.Index.CEPS.Scaled.SurrogateHalfEntranceBudget

/-! # Actual marked entrance prefactors and real-drift errors -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueMarkPrefactor {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  exp (dom.canonL ρW (b * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z)) /
    cepsQ D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z)

def cepsScaledSurrogateMarkPrefactor {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  exp (cepsCanonDriftTaylor dom ρW N (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) /
    cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)

def CepsCanonDomain.trueMarkPrefactorErrorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  Real.exp (dom.normalLogBound + dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) *
    dom.canonDriftCoeffBound (N + 1) M * (4 / cepsVarLo D)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueMarkLog_budget (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖dom.canonL ρW (b * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z)‖ ≤
      dom.normalLogBound := by
  have hbase := entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam hb
    (entranceScaleCurve_mark_mem dom hD N M lam hb)
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbase.1
  have hμD : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ := by
    rw [ofReal_mul]
    exact hμ.le.trans (by linarith [dom.μ₀_pos])
  have hζ : ‖(b : ℂ) ^ 2 * z‖ ≤ dom.c₀ / 2 := by
    simpa only [pow_two, mul_assoc] using hbase.2.le
  simpa only [ofReal_mul, CepsCanonDomain.canonL, CepsCanonDomain.normalLogBound] using!
    dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμD (ofReal_im (b * lam))
      (hq.le.trans (half_le_self dom.q₀_pos.le)) hζ

include hW hθ hD in
theorem cepsScaledTrueMarkPrefactor_budget (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueMarkPrefactor dom ρW lam z b‖ ≤ Real.exp dom.normalLogBound * (4 / cepsVarLo D) := by
  have hL := cepsScaledTrueMarkLog_budget dom hW hθ hD N M lam hz hb
  have hQ := cepsScaledSurrogateMarkQuotient_inverse_budget dom hW hθ hD N M lam hz hb
  unfold cepsScaledTrueMarkPrefactor
  rw [div_eq_mul_inv, norm_mul]
  exact mul_le_mul (by rw [norm_exp]; exact Real.exp_le_exp.mpr ((re_le_norm _).trans hL)) hQ
    (norm_nonneg _) (Real.exp_pos _).le

include hW hθ hD in
theorem cepsScaledSurrogateMarkPrefactor_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledSurrogateMarkPrefactor dom ρW N lam z b‖ ≤
      Real.exp (dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) * (4 / cepsVarLo D) := by
  unfold cepsScaledSurrogateMarkPrefactor
  rw [div_eq_mul_inv, norm_mul]
  exact mul_le_mul
    (cepsScaledSurrogateMarkExp_budget dom hW hθ hD hf hη hM N hN lam hz hb)
    (cepsScaledSurrogateMarkQuotient_inverse_budget dom hW hθ hD N M lam hz hb)
    (norm_nonneg _) (Real.exp_pos _).le

include hD in
theorem trueMarkPrefactorErrorConstant_nonneg {M : ℝ} (hM : 0 ≤ M) (N : ℕ) :
    0 ≤ dom.trueMarkPrefactorErrorConstant N M := by
  have := dom.jetC_nonneg hD N
  have := dom.c₀_pos
  have := cepsVarLo_pos hD
  unfold CepsCanonDomain.trueMarkPrefactorErrorConstant CepsCanonDomain.canonDriftCoeffBound
  positivity

include hW hθ hD in
theorem cepsScaledTrueMarkPrefactor_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueMarkPrefactor dom ρW lam z b - cepsScaledSurrogateMarkPrefactor dom ρW N lam z b‖ ≤
      dom.trueMarkPrefactorErrorConstant N M * |b * lam| ^ (N + 1) := by
  let A := dom.canonL ρW (b * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z)
  let B := cepsCanonDriftTaylor dom ρW N ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z)
  let K := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  have hbase := entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam hb
    (entranceScaleCurve_mark_mem dom hD N M lam hb)
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbase.1
  have hζ : ‖(b : ℂ) ^ 2 * z‖ ≤ dom.c₀ / 2 := by simpa only [pow_two, mul_assoc] using hbase.2.le
  have hA : ‖A‖ ≤ dom.normalLogBound := cepsScaledTrueMarkLog_budget dom hW hθ hD N M lam hz hb
  have hB : ‖B‖ ≤ K := cepsCanonDriftTaylor_norm_le dom hW hθ hD hf hη hM N (by omega) hμ.le hq.le hζ
  have hA0 : 0 ≤ dom.normalLogBound := (norm_nonneg A).trans hA
  have hB0 : 0 ≤ K := (norm_nonneg B).trans hB
  have hExp := norm_cexp_sub_cexp_le (M := dom.normalLogBound + K) (a := A) (b := B)
    (by linarith) (by linarith)
  have hμr : |b * lam| < dom.μ₀ / 4 := by
    have ht : ‖((b * lam : ℝ) : ℂ)‖ < dom.μ₀ / 8 := by simpa only [ofReal_mul] using hμ
    rw [norm_real, Real.norm_eq_abs] at ht
    linarith [dom.μ₀_pos]
  have hErr := cepsCanonDriftTaylor_approx dom hW hθ hD hf hη hM N hN hμr hq.le hζ
  rw [ofReal_mul] at hErr
  have hQ := cepsScaledSurrogateMarkQuotient_inverse_budget dom hW hθ hD N M lam hz hb
  unfold cepsScaledTrueMarkPrefactor cepsScaledSurrogateMarkPrefactor
  rw [← sub_div, div_eq_mul_inv, norm_mul]
  change ‖exp A - exp B‖ * _ ≤ _
  calc
    _ ≤ (Real.exp (dom.normalLogBound + K) *
        (dom.canonDriftCoeffBound (N + 1) M * |b * lam| ^ (N + 1))) * (4 / cepsVarLo D) :=
      mul_le_mul (hExp.trans (mul_le_mul_of_nonneg_left hErr (Real.exp_pos _).le)) hQ
        (norm_nonneg _) (by
          have := dom.jetC_nonneg hD N
          have := dom.c₀_pos
          have := (cepsSobolev_nonneg m η fW).trans hM
          unfold CepsCanonDomain.canonDriftCoeffBound
          positivity)
    _ = _ := by unfold CepsCanonDomain.trueMarkPrefactorErrorConstant; ring

end PGM
