import PLAStochastic.Index.CEPS.Scaled.TrueDenominatorRelative
import PLAStochastic.Index.CEPS.Scaled.InversePerturbation
import PLAStochastic.Index.CEPS.Scaled.PairPolynomialRadius

/-! # An order-independent scale disc for the actual denominator

The zeroth drift surrogate alone pays the actual nonzero denominator and
its weighted inverse budget. The disc is chosen from the class and its
Sobolev budget before any requested Taylor order; it is not shrunk anew
with that order.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueDenominatorScaleBase {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  min (dom.pairPolynomialScaleBase 0 M) (1 / (4 * (1 + dom.trueDenominatorRelativeConstant 0 M)))

def CepsCanonDomain.trueDenominatorScaleRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M lam : ℝ) (z : ℂ) : ℝ :=
  dom.trueDenominatorScaleBase M / (1 + |lam| + Real.sqrt ‖z‖)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueDenominatorScaleBase_pos {M : ℝ} (hM : 0 ≤ M) :
    0 < dom.trueDenominatorScaleBase M := by
  have := pairPolynomialScaleBase_pos dom hW hθ hD 0 M
  have := trueDenominatorRelativeConstant_nonneg dom hW hθ hD hM 0
  unfold CepsCanonDomain.trueDenominatorScaleBase
  positivity

include hW hθ hD in
theorem trueDenominatorScaleRadius_pos {M : ℝ} (hM : 0 ≤ M) (lam : ℝ) (z : ℂ) :
    0 < dom.trueDenominatorScaleRadius M lam z :=
  div_pos (trueDenominatorScaleBase_pos dom hW hθ hD hM) (by positivity)

include hW hθ hD in
theorem trueDenominatorScaleRadius_le (M lam : ℝ) (z : ℂ) :
    dom.trueDenominatorScaleRadius M lam z ≤ dom.entranceScaleRadius 0 M lam z :=
  (div_le_div_of_nonneg_right (min_le_left _ _)
    (by positivity : 0 ≤ 1 + |lam| + Real.sqrt ‖z‖)).trans
      (pairPolynomialScaleRadius_le dom hW hθ hD 0 M lam z).2

include hW hθ hD in
theorem cepsScaledTrueDenominator_relative_error_small {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    ‖(cepsScaledTrueDenominator dom ρW lam z b - cepsScaledSurrogateDenominator dom ρW 0 lam z b) /
      cepsScaledSurrogateDenominator dom ρW 0 lam z b‖ ≤ 1 / 2 := by
  let C := dom.trueDenominatorRelativeConstant 0 M
  have hC : 0 ≤ C := trueDenominatorRelativeConstant_nonneg dom hW hθ hD
    ((cepsSobolev_nonneg m η fW).trans hM) 0
  have ht : |b| * (1 + |lam| + Real.sqrt ‖z‖) < dom.trueDenominatorScaleBase M := by
    have hn := mem_ball_zero_iff.mp hb
    rw [norm_real, Real.norm_eq_abs] at hn
    exact (lt_div_iff₀ (by positivity : 0 < 1 + |lam| + Real.sqrt ‖z‖)).mp hn
  have hbase : dom.trueDenominatorScaleBase M ≤ 1 / (4 * (1 + C)) := min_le_right _ _
  have hμ : |b * lam| ≤ 1 / (4 * (1 + C)) := by
    rw [abs_mul]
    nlinarith [abs_nonneg b, abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hsmall : C * |b * lam| ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (1 + C))).mp hμ
    nlinarith [abs_nonneg (b * lam)]
  have h := cepsScaledTrueDenominator_relative_error_budget dom hW hθ hD hf hη hM 0 hm lam hz
    (ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hb)
  exact h.trans (by simpa only [zero_add, pow_one] using hsmall)

include hW hθ hD in
theorem cepsScaledTrueDenominator_ne_zero {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    cepsScaledTrueDenominator dom ρW lam z b ≠ 0 := by
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hb
  exact ceps_ne_zero_of_relative_error
    (cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM 0 (by omega) lam hz
      (ball_subset_ball (min_le_left _ _) hbE))
    (cepsScaledTrueDenominator_relative_error_small dom hW hθ hD hf hη hM hm lam hz hb)

include hW hθ hD in
theorem cepsScaledTrueDenominator_inverse_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    ‖(cepsScaledTrueDenominator dom ρW lam z b)⁻¹‖ ≤
      2 * dom.surrogateSlopePolynomialConstant 0 M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re) := by
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hb
  have hbR := ball_subset_ball (min_le_left _ _) hbE
  have hS := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM 0 (by omega) lam hz hbR
  have hsmall := cepsScaledTrueDenominator_relative_error_small dom hW hθ hD hf hη hM hm lam hz hb
  exact (cepsNorm_inverse_le_of_relative_error hS hsmall).trans
    ((mul_le_mul_of_nonneg_left
      (cepsScaledSurrogateDenominator_inverse_weighted_bound dom hW hθ hD hf hη hM 0
        (by omega) lam hz hbR) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

end PGM
