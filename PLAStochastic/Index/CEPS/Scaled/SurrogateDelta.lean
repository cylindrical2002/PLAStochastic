import PLAStochastic.Index.CEPS.Scaled.SurrogatePi
import PLAStochastic.Index.CEPS.Scaled.ComplexRootDifference
import PLAStochastic.Index.CEPS.Normal.DenominatorBound

/-! # Quantitative surrogate denominators throughout a complex scale disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain

def scaledGapBound {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  3 / Real.sqrt (cepsVarLo D / 2)

def scaledComplexSector {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  min 1 (1 / (4 * Real.sqrt v))

def surrogateScaleBase {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min (1 / (4 * Real.sqrt v * dom.scaledGapBound))
    (dom.scaledComplexSector / (4 * (1 + dom.canonSurrogatePiBound N M * dom.scaledGapBound)))

def surrogateScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M lam : ℝ) (z : ℂ) : ℝ :=
  min (dom.canonScaleRadius lam z / 2) (dom.surrogateScaleBase N M / (1 + |lam|))

end CepsCanonDomain

def cepsScaledEffectiveGap (D θ : ℝ) (ρW : Measure ℝ) (lam : ℝ) (z b : ℂ) : ℂ :=
  (cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b) *
    (1 + b * lam)

def cepsScaledSurrogateDelta {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  1 - exp (-cepsScaledEffectiveGap D θ ρW lam z b) * cepsScaledSurrogatePi dom ρW N lam z b

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogate_constants (N : ℕ) (M : ℝ) :
    0 < dom.scaledGapBound ∧ 0 < dom.scaledComplexSector ∧
      0 ≤ dom.canonSurrogatePiBound N M ∧ 0 < dom.surrogateScaleBase N M := by
  have hs : 0 < Real.sqrt (cepsVarLo D / 2) := Real.sqrt_pos.mpr (by linarith [cepsVarLo_pos hD])
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hK : 0 < dom.scaledGapBound := by unfold CepsCanonDomain.scaledGapBound; positivity
  have hc : 0 < dom.scaledComplexSector := lt_min (by norm_num) (by positivity)
  have hP : 0 ≤ dom.canonSurrogatePiBound N M := by
    have := dom.c₀_pos; have := cepsVarLo_pos hD; have := CepsCanonDomain.v_pos hW hθ hD
    unfold CepsCanonDomain.canonSurrogatePiBound
    positivity
  refine ⟨hK, hc, hP, ?_⟩
  unfold CepsCanonDomain.surrogateScaleBase
  exact lt_min (by positivity) (by positivity)

include hW hθ hD in
theorem surrogateScaleRadius_pos (N : ℕ) (M lam : ℝ) (z : ℂ) :
    0 < dom.surrogateScaleRadius N M lam z :=
  lt_min (half_pos (canonScaleRadius_pos dom hW hθ hD lam z))
    (div_pos (cepsScaledSurrogate_constants dom hW hθ hD N M).2.2.2 (by positivity))

theorem surrogateScaleCurve_small (N : ℕ) (M lam : ℝ) {z b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z)) :
    ‖b‖ ≤ dom.surrogateScaleBase N M ∧ ‖b * (lam : ℂ)‖ ≤ dom.surrogateScaleBase N M := by
  have ht : ‖b‖ * (1 + |lam|) < dom.surrogateScaleBase N M :=
    (lt_div_iff₀ (by positivity : 0 < 1 + |lam|)).mp
      ((mem_ball_zero_iff.mp hb).trans_le (min_le_right _ _))
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  exact ⟨by nlinarith [mul_nonneg (norm_nonneg b) (abs_nonneg lam)], by nlinarith [norm_nonneg b]⟩

include hW hθ hD in
theorem cepsScaledEffectiveGap_sector (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z)) :
    dom.scaledComplexSector * ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ≤
      (cepsScaledEffectiveGap D θ ρW lam z b).re := by
  have hbhalf : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2) :=
    ball_subset_ball (min_le_left _ _) hb
  have hbfull := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le) hbhalf
  let a := cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b
  let R := ‖cepsScaledRootCoordinate D θ ρW lam z b‖
  have hsector : R / (2 * Real.sqrt v) ≤ a.re :=
    cepsScaledRootGap_complex_sector dom hW hθ hD lam hz hbhalf
  have hnorm : ‖a‖ ≤ dom.scaledGapBound * R := cepsScaledRootGap_norm_le dom hW hθ hD lam hz hbfull
  have hsmall := (surrogateScaleCurve_small dom N M lam hb).2.trans
    (min_le_left _ _ : dom.surrogateScaleBase N M ≤ 1 / (4 * Real.sqrt v * dom.scaledGapBound))
  have hK := (cepsScaledSurrogate_constants dom hW hθ hD N M).1
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hprod : ‖a * (b * (lam : ℂ))‖ ≤ R / (4 * Real.sqrt v) := by
    rw [norm_mul]
    calc
      _ ≤ (dom.scaledGapBound * R) * (1 / (4 * Real.sqrt v * dom.scaledGapBound)) :=
        mul_le_mul hnorm hsmall (norm_nonneg _) (mul_nonneg hK.le (norm_nonneg _))
      _ = _ := by field_simp
  have hneg := (neg_le_abs (a * (b * (lam : ℂ))).re).trans ((abs_re_le_norm _).trans hprod)
  have he : cepsScaledEffectiveGap D θ ρW lam z b = a + a * (b * lam) := by
    dsimp only [cepsScaledEffectiveGap, a]; ring
  rw [he, add_re]
  have hlow : R / (4 * Real.sqrt v) ≤ a.re + (a * (b * lam)).re := by
    have : R / (2 * Real.sqrt v) = 2 * (R / (4 * Real.sqrt v)) := by ring
    linarith
  have hcle : dom.scaledComplexSector * R ≤ R / (4 * Real.sqrt v) := by
    calc
      dom.scaledComplexSector * R ≤ (1 / (4 * Real.sqrt v)) * R :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ = _ := by ring
  exact hcle.trans hlow

include hW hθ hD in
theorem cepsScaledSurrogateDelta_lower_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z)) :
    dom.scaledComplexSector / 4 * min 1 ‖cepsScaledRootCoordinate D θ ρW lam z b‖ ≤
      ‖cepsScaledSurrogateDelta dom ρW N lam z b‖ := by
  obtain ⟨hK, hc, hP, _⟩ := cepsScaledSurrogate_constants dom hW hθ hD N M
  have hbhalf : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2) :=
    ball_subset_ball (min_le_left _ _) hb
  have hbfull := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le) hbhalf
  let R := ‖cepsScaledRootCoordinate D θ ρW lam z b‖
  let C := dom.canonSurrogatePiBound N M * ‖b‖ * dom.scaledGapBound
  have hfactor : ‖cepsScaledSurrogatePi dom ρW N lam z b - 1‖ ≤ C * R := by
    calc
      _ ≤ _ := cepsScaledSurrogatePi_sub_one_le dom hW hθ hD hf hη hM N hN lam hz hbfull
      _ ≤ (dom.canonSurrogatePiBound N M * ‖b‖) * (dom.scaledGapBound * R) :=
        mul_le_mul_of_nonneg_left (cepsScaledRootGap_norm_le dom hW hθ hD lam hz hbfull)
          (mul_nonneg hP (norm_nonneg b))
      _ = _ := by dsimp only [C]; ring
  have hsmall := (surrogateScaleCurve_small dom N M lam hb).1.trans
    (min_le_right _ _ : dom.surrogateScaleBase N M ≤
      dom.scaledComplexSector / (4 * (1 + dom.canonSurrogatePiBound N M * dom.scaledGapBound)))
  have hpk : 0 ≤ dom.canonSurrogatePiBound N M * dom.scaledGapBound := mul_nonneg hP hK.le
  have hmul := (le_div_iff₀ (by positivity : 0 < 4 * (1 + dom.canonSurrogatePiBound N M * dom.scaledGapBound))).mp hsmall
  have hwidth : 2 * C ≤ dom.scaledComplexSector * 1 := by
    dsimp only [C]
    nlinarith [norm_nonneg b, mul_nonneg (norm_nonneg b) hpk]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  simpa only [cepsScaledSurrogateDelta, mul_one, ofReal_one] using
    cepsNormal_delta_lower_bound (l := 1) (by norm_num) (norm_nonneg _) hc (min_le_left _ _)
      hC (cepsScaledEffectiveGap_sector dom hW hθ hD N M lam hz hb) hfactor hwidth

end PGM
