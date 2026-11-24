import PLAStochastic.Index.CEPS.Scaled.OuterPairHolomorphy
import PLAStochastic.Index.CEPS.Scaled.CanonPolynomialRadius

/-! # A law-independent reciprocal polynomial disc for complete outer pairs -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.outerPairPolynomialScaleBase {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min (dom.pairPolynomialScaleBase N M)
    (min (1 / 2) (min dom.actualRootPolynomialScaleBase
      (min dom.μ₀ dom.rmax / (2 + dom.scaledCoordinateRatioBound))))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem outerPairPolynomialScaleBase_pos (N : ℕ) (M : ℝ) :
    0 < dom.outerPairPolynomialScaleBase N M := by
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  unfold CepsCanonDomain.outerPairPolynomialScaleBase
  exact lt_min (pairPolynomialScaleBase_pos dom hW hθ hD N M)
    (lt_min (by norm_num) (lt_min (canonPolynomialScale_constants dom hW hθ hD).2.2.1
      (div_pos (lt_min dom.μ₀_pos dom.rmax_pos) (by positivity))))

include hW hθ hD in
theorem outerPairPolynomialScaleRadius_le (N : ℕ) (M lam : ℝ) (z : ℂ) :
    dom.outerPairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖) ≤
      dom.outerPairScaleRadius N M lam z := by
  let B := dom.outerPairPolynomialScaleBase N M
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let A := dom.scaledCoordinateRatioBound
  let C := min dom.μ₀ dom.rmax
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hX0 : 0 < X := by linarith
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hC : 0 < C := lt_min dom.μ₀_pos dom.rmax_pos
  have hBP : B ≤ dom.pairPolynomialScaleBase N M := min_le_left _ _
  have hBhalf : B ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hBR : B ≤ dom.actualRootPolynomialScaleBase :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hBJ : B ≤ C / (2 + A) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hRoot : B / X ≤ dom.actualRootScaleRadius lam z :=
    (div_le_div_of_nonneg_right hBR hX0.le).trans (actualRootPolynomialScaleRadius_le dom hW hθ hD lam z)
  have hJoint : B / X ≤ dom.scaledMorseJointRadius lam (1 + dom.scaledRootCoordinateBound lam z) := by
    have hS := scaledRootCoordinateBound_le_polynomial dom hW hθ hD lam z
    have hden : 1 + |lam| + (1 + dom.scaledRootCoordinateBound lam z) ≤ (2 + A) * X := by
      have hl : 1 + |lam| ≤ X := by dsimp [X]; linarith [Real.sqrt_nonneg ‖z‖]
      change dom.scaledRootCoordinateBound lam z ≤ A * X at hS
      nlinarith
    have hY : 0 < 1 + |lam| + (1 + dom.scaledRootCoordinateBound lam z) := by
      have : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
      positivity
    calc
      B / X ≤ (C / (2 + A)) / X := div_le_div_of_nonneg_right hBJ hX0.le
      _ = C / ((2 + A) * X) := by rw [div_div]
      _ ≤ C / (1 + |lam| + (1 + dom.scaledRootCoordinateBound lam z)) :=
        div_le_div_of_nonneg_left hC.le hY hden
      _ = _ := by simp only [CepsCanonDomain.scaledMorseJointRadius, norm_real, Real.norm_eq_abs]; rfl
  have hWidth : B / X ≤ 1 / (2 * (1 + |lam|)) := by
    calc
      _ ≤ (1 / 2) / X := div_le_div_of_nonneg_right hBhalf hX0.le
      _ = 1 / (2 * X) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left zero_le_one (by positivity) (by dsimp [X]; nlinarith [Real.sqrt_nonneg ‖z‖])
  exact le_min (div_le_div_of_nonneg_right hBP hX0.le)
    (le_min (le_min hRoot hJoint) hWidth)

end PGM
