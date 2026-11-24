import PLAStochastic.Index.CEPS.Normal.ActualMorseData

/-! # Class norm estimates for the actual scaled roots -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain

/-- Class coefficient of the drift in the unscaled root norm estimate. -/
def scaledRootDriftBound {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  2 / cepsVarLo D * (1 + cepsChartK D * Real.sqrt v)

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMorseCenter_norm_le_drift {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) :
    ‖cepsMorseCenter D θ ρW μ‖ ≤ 2 / cepsVarLo D * ‖μ‖ := by
  have h := norm_cepsMorseCenter_le hW hθ hD (dom.μ_lt_chart hμ)
  calc
    _ ≤ 2 * ‖μ‖ / cepsVarLo D := h.trans
      (div_le_div_of_nonneg_left (by positivity) (cepsVarLo_pos hD) (cepsVarLo_le hW hθ hD))
    _ = _ := by ring

include hW hθ hD in
theorem cepsRootR_norm_le_drift_sqrt {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) :
    ‖cepsRootR D θ ρW μ q‖ ≤ Real.sqrt ‖q‖ +
      Real.sqrt v * (2 / cepsVarLo D * ‖μ‖) := by
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hcenter := cepsMorseCenter_norm_le_drift dom hW hθ hD hμ
  have hm := norm_cepsMorseMin_le hW hθ hD (dom.μ_lt_chart hμ)
  have hmsq : ‖cepsMorseMin D θ ρW μ‖ ≤ v * (2 / cepsVarLo D * ‖μ‖) ^ 2 :=
    hm.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcenter 2) hv.le)
  have hr := norm_cepsRootR_sq D θ ρW μ q
  have hq := norm_sub_le q (cepsMorseMin D θ ρW μ)
  have hs := Real.sq_sqrt (norm_nonneg q)
  have hsv := Real.sq_sqrt hv.le
  have hμ0 : 0 ≤ 2 / cepsVarLo D * ‖μ‖ := by have := cepsVarLo_pos hD; positivity
  have hroot0 := Real.sqrt_nonneg ‖q‖
  have hvroot0 := Real.sqrt_nonneg v
  have hprod : (Real.sqrt v * (2 / cepsVarLo D * ‖μ‖)) ^ 2 =
      v * (2 / cepsVarLo D * ‖μ‖) ^ 2 := by rw [mul_pow, hsv]
  have hsq : ‖cepsRootR D θ ρW μ q‖ ^ 2 ≤
      (Real.sqrt ‖q‖ + Real.sqrt v * (2 / cepsVarLo D * ‖μ‖)) ^ 2 := by
    nlinarith [mul_nonneg hroot0 (mul_nonneg hvroot0 hμ0)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num : 2 ≠ 0)).mp hsq

include hW hθ hD in
theorem cepsRoots_norm_le_class {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hq : ‖q‖ ≤ dom.q₀) :
    ‖cepsRootPlus D θ ρW μ q‖ ≤ dom.scaledRootDriftBound * ‖μ‖ +
        cepsChartK D * Real.sqrt ‖q‖ ∧
      ‖cepsRootMinus D θ ρW μ q‖ ≤ dom.scaledRootDriftBound * ‖μ‖ +
        cepsChartK D * Real.sqrt ‖q‖ := by
  have hc := cepsMorseCenter_norm_le_drift dom hW hθ hD hμ
  have hr := cepsRootR_norm_le_drift_sqrt dom hW hθ hD (q := q) hμ
  have hK := cepsChartK_pos hD
  have hp := norm_rootPlus_sub_center_le hW hθ hD (dom.μ_lt_chart hμ)
    (dom.norm_cepsRootR_lt hW hθ hD hμ hq)
  have hm := norm_rootMinus_sub_center_le hW hθ hD (dom.μ_lt_chart hμ)
    (dom.norm_cepsRootR_lt hW hθ hD hμ hq)
  have hbound : ∀ β : ℂ, ‖β - cepsMorseCenter D θ ρW μ‖ ≤
      cepsChartK D * ‖cepsRootR D θ ρW μ q‖ →
      ‖β‖ ≤ dom.scaledRootDriftBound * ‖μ‖ + cepsChartK D * Real.sqrt ‖q‖ := by
    intro β hβ
    calc
      ‖β‖ = ‖cepsMorseCenter D θ ρW μ + (β - cepsMorseCenter D θ ρW μ)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
      _ ≤ 2 / cepsVarLo D * ‖μ‖ + cepsChartK D *
          (Real.sqrt ‖q‖ + Real.sqrt v * (2 / cepsVarLo D * ‖μ‖)) :=
        add_le_add hc (hβ.trans (mul_le_mul_of_nonneg_left hr hK.le))
      _ = _ := by unfold CepsCanonDomain.scaledRootDriftBound; ring
  exact ⟨hbound _ hp, hbound _ hm⟩

/-- The exact marked discount after the `b=1/w` change of variables. -/
def cepsScaledDiscount (b lam : ℝ) (z : ℂ) : ℂ := (b : ℂ) ^ 2 * z * (1 + (b * lam : ℝ))

/-- Norm scaling with the actual factor `1+blam` retained. -/
theorem cepsScaledDiscount_norm (b lam : ℝ) (z : ℂ) :
    ‖cepsScaledDiscount b lam z‖ = b ^ 2 * ‖z‖ * |1 + b * lam| := by
  simp only [cepsScaledDiscount, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  congr 1
  rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]

include hW hθ hD in
theorem cepsScaledRoots_norm_le {b lam : ℝ} (hb : 0 < b) {z : ℂ}
    (hμ : |b * lam| ≤ dom.μ₀) (hq : ‖cepsScaledDiscount b lam z‖ ≤ dom.q₀) :
    ‖cepsRootPlus D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z) / (b : ℂ)‖ ≤
        dom.scaledRootDriftBound * |lam| +
          cepsChartK D * (Real.sqrt ‖z‖ * Real.sqrt |1 + b * lam|) ∧
      ‖cepsRootMinus D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z) / (b : ℂ)‖ ≤
        dom.scaledRootDriftBound * |lam| +
          cepsChartK D * (Real.sqrt ‖z‖ * Real.sqrt |1 + b * lam|) := by
  have hμ' : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  obtain ⟨hp, hm⟩ := cepsRoots_norm_le_class dom hW hθ hD hμ' hq
  have hbabs : |b| = b := abs_of_pos hb
  have hs : Real.sqrt ‖cepsScaledDiscount b lam z‖ =
      b * (Real.sqrt ‖z‖ * Real.sqrt |1 + b * lam|) := by
    rw [cepsScaledDiscount_norm, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq_eq_abs, hbabs]
    ring
  have hμn : ‖((b * lam : ℝ) : ℂ)‖ = b * |lam| := by
    rw [norm_real, Real.norm_eq_abs, abs_mul, hbabs]
  rw [hμn, hs] at hp hm
  constructor
  · rw [norm_div, norm_real, Real.norm_eq_abs, hbabs, div_le_iff₀ hb]
    nlinarith [hp]
  · rw [norm_div, norm_real, Real.norm_eq_abs, hbabs, div_le_iff₀ hb]
    nlinarith [hm]


include hW hθ hD in
/-- The factor `1+b*lam` stays uniformly bounded on the small drift window. -/
theorem cepsScaledRoots_norm_le_polynomial {b lam : ℝ} (hb : 0 < b) {z : ℂ}
    (hμ : |b * lam| ≤ dom.μ₀) (hsmall : |b * lam| ≤ 1)
    (hq : ‖cepsScaledDiscount b lam z‖ ≤ dom.q₀) :
    ‖cepsRootPlus D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z) / (b : ℂ)‖ ≤
        (dom.scaledRootDriftBound + 2 * cepsChartK D) * (|lam| + Real.sqrt ‖z‖) ∧
      ‖cepsRootMinus D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z) / (b : ℂ)‖ ≤
        (dom.scaledRootDriftBound + 2 * cepsChartK D) * (|lam| + Real.sqrt ‖z‖) := by
  obtain ⟨hp, hm⟩ := cepsScaledRoots_norm_le dom hW hθ hD hb hμ hq
  have hs : Real.sqrt |1 + b * lam| ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    have ht := abs_add_le (1 : ℝ) (b * lam)
    have ht' : |1 + b * lam| ≤ 1 + |b * lam| := by simpa only [abs_one] using ht
    exact ⟨by norm_num, by linarith⟩
  have hK := cepsChartK_pos hD
  have hC : 0 ≤ dom.scaledRootDriftBound := by
    unfold CepsCanonDomain.scaledRootDriftBound
    have := cepsVarLo_pos hD
    positivity
  have hmajor : dom.scaledRootDriftBound * |lam| +
      cepsChartK D * (Real.sqrt ‖z‖ * Real.sqrt |1 + b * lam|) ≤
      (dom.scaledRootDriftBound + 2 * cepsChartK D) * (|lam| + Real.sqrt ‖z‖) := by
    have hterm := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg ‖z‖)) hK.le
    nlinarith [mul_nonneg hC (Real.sqrt_nonneg ‖z‖), mul_nonneg hK.le (abs_nonneg lam)]
  exact ⟨hp.trans hmajor, hm.trans hmajor⟩

end PGM
