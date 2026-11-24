import PLAStochastic.Index.CEPS.Scaled.RootDirections

/-! # Class-uniform scaled root-difference sector

The marked discount factor is retained exactly. The result covers the
imaginary axis and the closed right half-plane within the root chart;
no positive sector bound is asserted on the entire negative-real strip.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM
namespace CepsCanonDomain

def scaledRootCoercivityConst {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  min (Real.sqrt (cepsVarLo D) / (3 * v)) (1 / 2)

def scaledRootSectorConst {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  dom.scaledRootCoercivityConst / (4 * Real.sqrt v)

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRoot_sectorConst_pos : 0 < dom.scaledRootSectorConst := by
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hvl := cepsVarLo_pos hD
  have ha : 0 < dom.scaledRootCoercivityConst := lt_min (by positivity) (by norm_num)
  exact div_pos ha (by positivity)

/-- The actual marked discount preserves the right half-plane at small drift. -/
theorem cepsScaledDiscount_re_nonneg {b lam : ℝ} {z : ℂ}
    (hsmall : |b * lam| ≤ 1 / 2) (hz : 0 ≤ z.re) :
    0 ≤ (cepsScaledDiscount b lam z).re := by
  have hmark : 0 ≤ 1 + b * lam := by linarith [neg_le_abs (b * lam)]
  simp [cepsScaledDiscount, mul_re, mul_im, pow_two]
  exact mul_nonneg (mul_nonneg (mul_self_nonneg b) hz) hmark

include hW hθ hD in
/-- The Morse scale controls both scaled drift and square-root frequency. -/
theorem cepsScaledRootR_norm_ge {b lam : ℝ} (hb : 0 < b) {z : ℂ}
    (hμ : |b * lam| ≤ dom.μ₀) (hsmall : |b * lam| ≤ 1 / 2) (hz : 0 ≤ z.re) :
    dom.scaledRootCoercivityConst / 2 * (|lam| + Real.sqrt ‖z‖) ≤
      ‖cepsRootR D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)‖ / b := by
  have hqre := cepsScaledDiscount_re_nonneg hsmall hz
  have hdrift := cepsRootR_norm_ge_drift dom hW hθ hD hμ hqre
  have hzq := cepsRootR_norm_ge_discount dom hW hθ hD hμ hqre
  have hbabs := abs_of_pos hb
  have hs : Real.sqrt ‖cepsScaledDiscount b lam z‖ =
      b * (Real.sqrt ‖z‖ * Real.sqrt |1 + b * lam|) := by
    rw [cepsScaledDiscount_norm, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq_eq_abs, hbabs]
    ring
  have hhalf : 1 / 2 ≤ Real.sqrt |1 + b * lam| := by
    have hmark : 1 / 2 ≤ |1 + b * lam| := by
      linarith [neg_le_abs (b * lam), le_abs_self (1 + b * lam)]
    have hs2 := Real.sq_sqrt (abs_nonneg (1 + b * lam))
    nlinarith [Real.sqrt_nonneg |1 + b * lam|]
  rw [abs_mul, hbabs] at hdrift
  rw [hs] at hzq
  have hdrift' : dom.scaledRootCoercivityConst * |lam| ≤
      ‖cepsRootR D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)‖ / b := by
    apply (le_div_iff₀ hb).mpr
    calc
      _ = dom.scaledRootCoercivityConst * (b * |lam|) := by ring
      _ ≤ (Real.sqrt (cepsVarLo D) / (3 * v)) * (b * |lam|) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ _ := hdrift
  have hz' : dom.scaledRootCoercivityConst * Real.sqrt ‖z‖ ≤
      ‖cepsRootR D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)‖ / b := by
    apply (le_div_iff₀ hb).mpr
    calc
      _ = b * (Real.sqrt ‖z‖ * dom.scaledRootCoercivityConst) := by ring
      _ ≤ b * (Real.sqrt ‖z‖ * Real.sqrt |1 + b * lam|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          ((min_le_right _ _).trans hhalf) (Real.sqrt_nonneg _)) hb.le
      _ ≤ _ := hzq
  nlinarith

include hW hθ hD in
/-- C-9's root-difference sector with constants chosen before the step law. -/
theorem cepsScaledRoots_difference_re_ge {b lam : ℝ} (hb : 0 < b) {z : ℂ}
    (hμ : |b * lam| ≤ dom.μ₀) (hsmall : |b * lam| ≤ 1 / 2) (hz : 0 ≤ z.re)
    (hq : ‖cepsScaledDiscount b lam z‖ ≤ dom.q₀) :
    dom.scaledRootSectorConst * (|lam| + Real.sqrt ‖z‖) ≤
      ((cepsRootPlus D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z) -
        cepsRootMinus D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)) / (b : ℂ)).re := by
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hR := cepsScaledRootR_norm_ge dom hW hθ hD hb hμ hsmall hz
  have hsector := cepsRoots_difference_re_ge hW hθ hD dom hμ hq
    (cepsScaledDiscount_re_nonneg hsmall hz)
  rw [Complex.div_ofReal_re]
  calc
    _ = (dom.scaledRootCoercivityConst / 2 * (|lam| + Real.sqrt ‖z‖)) /
        (2 * Real.sqrt v) := by unfold CepsCanonDomain.scaledRootSectorConst; ring
    _ ≤ (‖cepsRootR D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)‖ / b) /
        (2 * Real.sqrt v) := div_le_div_of_nonneg_right hR (by positivity)
    _ = (‖cepsRootR D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)‖ /
        (2 * Real.sqrt v)) / b := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hsector hb.le


include hW hθ hD in
/-- Nonnegative scaled drift gives the decaying negative root required by C-9. -/
theorem cepsScaledRootMinus_re_ge {b lam : ℝ} (hb : 0 < b) (hlam : 0 ≤ lam) {z : ℂ}
    (hμ : |b * lam| ≤ dom.μ₀) (hsmall : |b * lam| ≤ 1 / 2) (hz : 0 ≤ z.re)
    (hq : ‖cepsScaledDiscount b lam z‖ ≤ dom.q₀) :
    dom.scaledRootSectorConst / 2 * (|lam| + Real.sqrt ‖z‖) ≤
      -((cepsRootMinus D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)) / (b : ℂ)).re := by
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hR := cepsScaledRootR_norm_ge dom hW hθ hD hb hμ hsmall hz
  have hdir := cepsRootMinus_re_ge_scale dom hW hθ hD hμ (mul_nonneg hb.le hlam) hq
    (cepsScaledDiscount_re_nonneg hsmall hz)
  rw [Complex.div_ofReal_re]
  calc
    _ = (dom.scaledRootCoercivityConst / 2 * (|lam| + Real.sqrt ‖z‖)) /
        (4 * Real.sqrt v) := by unfold CepsCanonDomain.scaledRootSectorConst; ring
    _ ≤ (‖cepsRootR D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)‖ / b) /
        (4 * Real.sqrt v) := div_le_div_of_nonneg_right hR (by positivity)
    _ = (‖cepsRootR D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)‖ /
        (4 * Real.sqrt v)) / b := by ring
    _ ≤ -(cepsRootMinus D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)).re / b :=
      div_le_div_of_nonneg_right hdir hb.le
    _ = _ := by ring

include hW hθ hD in
/-- Nonpositive scaled drift gives the decaying positive root required by C-9. -/
theorem cepsScaledRootPlus_re_ge {b lam : ℝ} (hb : 0 < b) (hlam : lam ≤ 0) {z : ℂ}
    (hμ : |b * lam| ≤ dom.μ₀) (hsmall : |b * lam| ≤ 1 / 2) (hz : 0 ≤ z.re)
    (hq : ‖cepsScaledDiscount b lam z‖ ≤ dom.q₀) :
    dom.scaledRootSectorConst / 2 * (|lam| + Real.sqrt ‖z‖) ≤
      ((cepsRootPlus D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)) / (b : ℂ)).re := by
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hR := cepsScaledRootR_norm_ge dom hW hθ hD hb hμ hsmall hz
  have hdir := cepsRootPlus_re_ge_scale dom hW hθ hD hμ (mul_nonpos_of_nonneg_of_nonpos hb.le hlam) hq
    (cepsScaledDiscount_re_nonneg hsmall hz)
  rw [Complex.div_ofReal_re]
  calc
    _ = (dom.scaledRootCoercivityConst / 2 * (|lam| + Real.sqrt ‖z‖)) /
        (4 * Real.sqrt v) := by unfold CepsCanonDomain.scaledRootSectorConst; ring
    _ ≤ (‖cepsRootR D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)‖ / b) /
        (4 * Real.sqrt v) := div_le_div_of_nonneg_right hR (by positivity)
    _ = (‖cepsRootR D θ ρW (b * lam : ℝ) (cepsScaledDiscount b lam z)‖ /
        (4 * Real.sqrt v)) / b := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hdir hb.le

end PGM
