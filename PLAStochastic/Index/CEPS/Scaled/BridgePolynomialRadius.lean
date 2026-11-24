import PLAStochastic.Index.CEPS.Scaled.CanonPolynomialRadius
import PLAStochastic.Index.CEPS.Scaled.PositiveBridgeBudget

/-! # A reciprocal polynomial scale radius for both bridge decay estimates -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.bridgePolynomialScaleBase {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) : ℝ :=
  min (dom.canonPolynomialScaleBase / 2) (min (dom.surrogateScaleBase N M)
    (min (1 / (4 * (1 + dom.canonSurrogatePiBound N M)))
      (min dom.complexDirectionScaleBase (1 / (48 * Real.sqrt v * dom.complexIndividualRootBound)))))

private theorem polynomial_ratio_le_drift_ratio {B C x y : ℝ}
    (hB : B ≤ C) (hC : 0 ≤ C) (hy : 0 < y) (hxy : y ≤ x) : B / x ≤ C / y :=
  (div_le_div_of_nonneg_right hB (hy.le.trans hxy)).trans
    (div_le_div_of_nonneg_left hC hy hxy)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem bridgePolynomialScaleBase_pos (N : ℕ) (M : ℝ) : 0 < dom.bridgePolynomialScaleBase N M := by
  have hcan := (canonPolynomialScale_constants dom hW hθ hD).2.2.2
  have hsur := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.2.2
  have hP := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.2.1
  have hH := complexIndividualRootBound_pos dom hW hθ hD
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hdir : 0 < dom.complexDirectionScaleBase := by
    unfold CepsCanonDomain.complexDirectionScaleBase
    exact lt_min (centerUnitSectorRadius_pos dom hW hθ hD) (by positivity)
  unfold CepsCanonDomain.bridgePolynomialScaleBase
  positivity

include hW hθ hD in
theorem bridgePolynomialScaleRadius_le (N : ℕ) (M lam : ℝ) (z : ℂ) :
    dom.bridgePolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖) ≤
      dom.positiveCorrectionScaleRadius N M lam z := by
  let B := dom.bridgePolynomialScaleBase N M
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hB : 0 ≤ B := (bridgePolynomialScaleBase_pos dom hW hθ hD N M).le
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hX0 : 0 < X := by linarith
  have hcan : B ≤ dom.canonPolynomialScaleBase / 2 := min_le_left _ _
  have hsur : B ≤ dom.surrogateScaleBase N M := (min_le_right _ _).trans (min_le_left _ _)
  have hreg : B ≤ 1 / (4 * (1 + dom.canonSurrogatePiBound N M)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdir : B ≤ dom.complexDirectionScaleBase :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hpos : B ≤ 1 / (48 * Real.sqrt v * dom.complexIndividualRootBound) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hdrift : 1 + |lam| ≤ X := by dsimp [X]; linarith [Real.sqrt_nonneg ‖z‖]
  have hratio : B / X ≤ B := div_le_self hB hX
  have hc : B / X ≤ dom.canonScaleRadius lam z / 2 := by
    calc
      _ ≤ (dom.canonPolynomialScaleBase / 2) / X := div_le_div_of_nonneg_right hcan hX0.le
      _ = (dom.canonPolynomialScaleBase / X) / 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (canonPolynomialScaleRadius_le dom hW hθ hD lam z) (by norm_num)
  have hs : B / X ≤ dom.surrogateScaleRadius N M lam z := le_min hc
    (polynomial_ratio_le_drift_ratio hsur (hB.trans hsur) (by positivity) hdrift)
  have hr : B / X ≤ dom.surrogateRegularScaleRadius N M lam z := le_min hs (hratio.trans hreg)
  have hd : B / X ≤ dom.complexDirectionScaleRadius N M lam z := le_min hr
    (polynomial_ratio_le_drift_ratio hdir (hB.trans hdir) (by positivity) hdrift)
  exact le_min hd (polynomial_ratio_le_drift_ratio hpos (hB.trans hpos) (by positivity) hdrift)

end PGM
