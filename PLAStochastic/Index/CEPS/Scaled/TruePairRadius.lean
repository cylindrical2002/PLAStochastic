import PLAStochastic.Index.CEPS.Scaled.TrueBridgeDiscount
import PLAStochastic.Index.CEPS.Scaled.RootSector

/-! # A fixed actual scale disc paying the physical width threshold -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.truePairScaleBase {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  min (dom.trueDenominatorScaleBase M) (1 / (4 * (1 + dom.normalWidthThreshold)))

def CepsCanonDomain.truePairScaleRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M lam : ℝ) (z : ℂ) : ℝ :=
  dom.truePairScaleBase M / (1 + |lam| + Real.sqrt ‖z‖)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem truePairScaleBase_pos {M : ℝ} (hM : 0 ≤ M) : 0 < dom.truePairScaleBase M := by
  have := trueDenominatorScaleBase_pos dom hW hθ hD hM
  have hT := (cepsNormal_width_properties dom hW hθ hD (l := dom.normalWidthThreshold) le_rfl).1
  unfold CepsCanonDomain.truePairScaleBase
  positivity

include hW hθ hD in
theorem truePairScaleRadius_pos {M : ℝ} (hM : 0 ≤ M) (lam : ℝ) (z : ℂ) :
    0 < dom.truePairScaleRadius M lam z :=
  div_pos (truePairScaleBase_pos dom hW hθ hD hM) (by positivity)

theorem truePairScaleRadius_le (M lam : ℝ) (z : ℂ) :
    dom.truePairScaleRadius M lam z ≤ dom.trueDenominatorScaleRadius M lam z :=
  div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)

include hW hθ hD in
theorem cepsScaledTruePair_drift_le_half (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.truePairScaleRadius M lam z)) : |b * lam| ≤ 1 / 2 := by
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z)
    (ball_subset_ball (truePairScaleRadius_le dom M lam z) hbs)
  have ht := entranceScaleCurve_product_bound dom hD 0 M lam hbE
  rw [norm_real, Real.norm_eq_abs] at ht
  have hC : 0 ≤ dom.actualScaledRootBound lam z := (norm_nonneg _).trans
    ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).2 0
      (mem_ball_self (actualRootScaleRadius_pos dom hW hθ hD lam z)))
  have hbase : dom.canonScaleBase ≤ 1 := min_le_left _ _
  rw [abs_mul]
  nlinarith [abs_nonneg b, abs_nonneg lam, Real.sqrt_nonneg ‖z‖]

include hW hθ hD in
theorem cepsScaledTruePair_width_threshold (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : 0 < b) (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.truePairScaleRadius M lam z)) :
    dom.normalWidthThreshold ≤ (1 + b * lam) / b := by
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z) hbs
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hbD
  have hprod := entranceScaleCurve_product_bound dom hD 0 M lam hbE
  rw [norm_real, Real.norm_eq_abs, abs_of_pos hb] at hprod
  have hbase : dom.canonScaleBase ≤ 1 := min_le_left _ _
  have hC : 0 ≤ dom.actualScaledRootBound lam z := (norm_nonneg _).trans
    ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).2 0
      (mem_ball_self (actualRootScaleRadius_pos dom hW hθ hD lam z)))
  have hμ : |b * lam| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hb]
    nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hn := mem_ball_zero_iff.mp hbs
  rw [norm_real, Real.norm_eq_abs, abs_of_pos hb] at hn
  have hT := (cepsNormal_width_properties dom hW hθ hD (l := dom.normalWidthThreshold) le_rfl).1
  have hsmall : b ≤ 1 / (4 * (1 + dom.normalWidthThreshold)) := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 1 + |lam| + Real.sqrt ‖z‖)).mp hn
    have hB : dom.truePairScaleBase M ≤ 1 / (4 * (1 + dom.normalWidthThreshold)) := min_le_right _ _
    nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hmul := (le_div_iff₀ (by positivity : 0 < 4 * (1 + dom.normalWidthThreshold))).mp hsmall
  apply (le_div_iff₀ hb).mpr
  nlinarith [neg_le_abs (b * lam)]

include hW hθ hD in
theorem cepsScaledTruePair_curve_bounds (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : 0 < b) (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.truePairScaleRadius M lam z)) :
    |b * lam| ≤ dom.μ₀ ∧ ‖cepsComplexScaledDiscount lam z b‖ < dom.q₀ ∧
      0 ≤ (cepsComplexScaledDiscount lam z b).re ∧
        dom.normalWidthThreshold ≤ (1 + b * lam) / b ∧ 0 < 1 + b * lam := by
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z)
    (ball_subset_ball (truePairScaleRadius_le dom M lam z) hbs)
  have hbC := ball_subset_ball ((min_le_right _ _).trans
    (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))) hbE
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbC
  have hμr : |b * lam| ≤ dom.μ₀ := by
    have ht : ‖((b * lam : ℝ) : ℂ)‖ < dom.μ₀ / 8 := by simpa only [ofReal_mul] using hμ
    rw [norm_real, Real.norm_eq_abs] at ht
    linarith [dom.μ₀_pos]
  have hsmall := cepsScaledTruePair_drift_le_half dom hW hθ hD M lam hz hbs
  have hre := cepsScaledDiscount_re_nonneg hsmall hz
  have hEq : cepsScaledDiscount b lam z = cepsComplexScaledDiscount lam z b := by
    simp only [cepsScaledDiscount, cepsComplexScaledDiscount, ofReal_mul]
  exact ⟨hμr, hq.trans (half_lt_self dom.q₀_pos), hEq ▸ hre,
    cepsScaledTruePair_width_threshold dom hW hθ hD M lam hz hb hbs,
      by linarith [neg_le_abs (b * lam)]⟩

end PGM
