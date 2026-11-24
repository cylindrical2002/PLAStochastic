import PLAStochastic.Index.GEP.OrbitClosure.Main
import PLAStochastic.ForMathlib.Probability.Distributions.LogExponential

/-!
# The actual exponential reference-law orbit and its base scale regularity

The laws are the existing actual normalised ALG-OPT layer-map iterates. Their
common density-envelope and moment class are unconditional. The base layer has
an unconditional two-thirds scale Hellinger bound; the same bound at positive
layer indices still requires the actual spatial derivative recurrence.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

def kepReferenceLaw (eps : ℝ) (j : ℕ) : ProbabilityMeasure ℝ :=
  (lawPhi eps)^[j] expPM

theorem kepReferenceLaw_zero (eps : ℝ) : kepReferenceLaw eps 0 = expPM := rfl

theorem kepReferenceLaw_succ (eps : ℝ) (j : ℕ) :
    kepReferenceLaw eps (j + 1) = lawPhi eps (kepReferenceLaw eps j) :=
  Function.iterate_succ_apply' _ _ _

theorem kepReferenceLaw_regular :
    ∃ D θ vlo vhi eps0 : ℝ, 0 < D ∧ 0 < θ ∧ 0 < vlo ∧ vlo ≤ vhi ∧
      ∀ eps, eps0 ≤ eps → ∀ j, RegLaw D θ vlo vhi (kepReferenceLaw eps j) := by
  obtain ⟨D, θ, vlo, vhi, e0, hD, hθ, hvlo, hv, h⟩ :=
    orbitClosure 1 1 1 1 one_pos one_pos one_pos le_rfl
  exact ⟨D, θ, vlo, vhi, e0, hD, hθ, hvlo, hv,
    fun eps heps j => h eps heps expPM regLaw_expPM j⟩

theorem kepReferenceLaw_zero_scale_budget :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ eps s : ℝ,
      let P : Measure ℝ := (kepReferenceLaw eps 0 : Measure ℝ)
      let : IsProbabilityMeasure (P.map (fun x => Real.exp s * x)) :=
        Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
      measureHellinger (P.map (fun x => Real.exp s * x)) P ≤ K * |s| ^ (2 / 3 : ℝ) := by
  refine ⟨2 * Real.sqrt (2 * ∫ y, |logExpSecond y|) + Real.sqrt (∫ y, |logExpFirst y|) / 2,
    by positivity, ?_⟩
  intro eps s
  exact measureHellinger_exp_one_scale_two_thirds s

end

end PGM
