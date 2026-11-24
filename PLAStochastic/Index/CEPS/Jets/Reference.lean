import PLAStochastic.Index.CEPS.Jets.Shrink

/-!
# X8: the reference step law and the jet line

The step `W = 1 - X` of the reference law `Λ` has density `y ↦ f_Λ(1 - y)` and lies in a step
class `(D, θ, v)` (`isStepLaw_of_density`). We fix such constants and a canonical domain
(`cepsRef`), and take its line abscissa `c₀` as the line of all contour jets (`cepsJetLine`).
On that line, at the origin `(μ, q) = (0, 0)`, the canonical bounds hold for `Λ`:
`Re F̃ ≥ d₀`, `‖F̃‖ ≤ CF` and `‖1 - M^Λ‖ ≥ min(g, v₋ c₀²/32)`.
-/

noncomputable section

open MeasureTheory Complex
open PGM.WienerHopf

namespace PGM

/-- The density `y ↦ f_Λ(1 - y)` of the reference step `W = 1 - X`. -/
def cepsRefStepDensity (y : ℝ) : ℝ := cepsLambdaDensity (1 - y)

/-- The reference step law. -/
def cepsRefStep : Measure ℝ := volume.withDensity fun y => ENNReal.ofReal (cepsRefStepDensity y)

/-- Fixed step-class constants and a canonical domain for the reference step. -/
structure CepsRefData where
  D : ℝ
  θ : ℝ
  v : ℝ
  hD : 0 < D
  hθ : 0 < θ
  hv : 0 < v
  hW : IsStepLaw cepsRefStep cepsRefStepDensity D θ v
  dom : CepsCanonDomain D θ v

theorem cepsRefData_nonempty : Nonempty CepsRefData := by
  obtain ⟨D, θ, hD, hθ, hb⟩ := cepsLambdaDensity_exponential_bound
  have hW := isStepLaw_of_density (ν := cepsLambda) (f := cepsLambdaDensity)
    (vhi := BrownianAffine.optimalDispersionConstant) contDiff_cepsLambdaDensity.continuous.measurable
    cepsLambdaDensity_nonneg (fun _ hx => cepsLambdaDensity_of_nonpos hx) hb
    cepsLambda_eq_withDensity lawMean_cepsLambda lawVar_cepsLambda.le hθ hD.le
  have hv : 0 < BrownianAffine.optimalDispersionConstant := lawVar_cepsLambda ▸ lawVar_cepsLambda_pos
  have hD' : 0 < D * Real.exp θ := by positivity
  exact ⟨⟨D * Real.exp θ, θ, BrownianAffine.optimalDispersionConstant, hD', hθ, hv, hW,
    Classical.choice (cepsCanonDomain_exists hD' hθ hv)⟩⟩

/-- The fixed reference data. -/
def cepsRef : CepsRefData := Classical.choice cepsRefData_nonempty

/-- The line `Re s = c_*` of the contour jets. -/
def cepsJetLine : ℝ := cepsRef.dom.c₀

theorem cepsJetLine_pos : 0 < cepsJetLine := cepsRef.dom.c₀_pos

theorem cepsJetLine_le_one : cepsJetLine ≤ 1 := by
  have h := cepsRef.dom.c₀_le
  have h1 := cepsRef.dom.ρA_one
  unfold cepsJetLine
  linarith

/-- The reference transform is the reference step transform. -/
theorem stepTransform_cepsRefStep (s : ℂ) :
    stepTransform cepsRefStep s = cepsJetTransform cepsLambdaDensity s := by
  rw [stepTransform_eq_integral cepsRef.hW, cepsJetTransform]
  have := integral_sub_left_eq_self
    (fun x : ℝ => cexp (s * (1 - x)) * (cepsLambdaDensity x : ℂ)) (μ := volume) 1
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [cepsRefStepDensity]
  push_cast
  rw [sub_sub_cancel]
  ring

/-- Reference bounds on the jet line at the origin. -/
theorem cepsRef_line_bounds (y : ℝ) :
    cepsRef.dom.d₀ ≤ (cepsJetF (cepsJetLine + y * I)
        (cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I))).re ∧
      ‖cepsJetF (cepsJetLine + y * I)
        (cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I))‖ ≤ cepsRef.dom.CF ∧
      min cepsRef.dom.g (cepsVarLo cepsRef.D * (cepsJetLine / 2) ^ 2 / 32) ≤
        ‖1 - cepsJetTransform cepsLambdaDensity (cepsJetLine + y * I)‖ := by
  have hre : ((cepsJetLine : ℂ) + y * I).re = cepsJetLine := by simp
  have h1 : 0 < ((cepsJetLine : ℂ) + y * I).re := by rw [hre]; exact cepsJetLine_pos
  have h2 : ((cepsJetLine : ℂ) + y * I).re ≤ 2 * cepsRef.dom.c₀ := by
    rw [hre]; unfold cepsJetLine; linarith [cepsRef.dom.c₀_pos]
  obtain ⟨a, b⟩ := cepsRef.dom.re_cepsJetF_ge_of_band cepsRef.hW cepsRef.hθ cepsRef.hD h1 h2
  have c := cepsRef.dom.norm_one_sub_stepTransform_ge_of_band cepsRef.hW cepsRef.hθ cepsRef.hD h1 h2
  rw [stepTransform_cepsRefStep] at a b c
  rw [hre] at c
  exact ⟨a, b, c⟩

end PGM
