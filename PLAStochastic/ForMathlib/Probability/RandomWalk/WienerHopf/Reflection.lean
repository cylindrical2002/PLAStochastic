import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Discount
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Markov

/-! # Reflection of the canonical random-walk path and entrance transforms -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Complex
namespace PGM.WienerHopf

def reflectPath (ω : ℕ → ℝ) : ℕ → ℝ := fun i => -ω i

@[fun_prop] theorem measurable_reflectPath : Measurable reflectPath := by
  exact measurable_pi_lambda _ fun i => (measurable_pi_apply i).neg

theorem partialSum_reflectPath (n : ℕ) (ω : ℕ → ℝ) :
    partialSum n (reflectPath ω) = -partialSum n ω := by
  simp only [partialSum, reflectPath, Finset.sum_neg_distrib]

theorem firstEntry_reflectPath (A : Set ℝ) (ω : ℕ → ℝ) :
    firstEntry A (reflectPath ω) = firstEntry (Neg.neg ⁻¹' A) ω := by
  classical
  have hp : ∀ n : ℕ, (0 < n ∧ partialSum n (reflectPath ω) ∈ A) ↔
      (0 < n ∧ partialSum n ω ∈ Neg.neg ⁻¹' A) := by
    intro n
    rw [partialSum_reflectPath]
    rfl
  by_cases h₁ : ∃ n : ℕ, 0 < n ∧ partialSum n (reflectPath ω) ∈ A
  · have h₂ := h₁.imp fun n hn => (hp n).mp hn
    simp only [firstEntry, dif_pos h₁, dif_pos h₂]
    congr 1
    exact Nat.find_congr' (fun {n} => hp n)
  · have h₂ : ¬ ∃ n : ℕ, 0 < n ∧ partialSum n ω ∈ Neg.neg ⁻¹' A :=
      fun h => h₁ (h.imp fun n hn => (hp n).mpr hn)
    simp only [firstEntry, dif_neg h₁, dif_neg h₂]

theorem entryValue_reflectPath (A : Set ℝ) (ω : ℕ → ℝ) :
    entryValue A (reflectPath ω) = -entryValue (Neg.neg ⁻¹' A) ω := by
  simp only [entryValue, firstEntry_reflectPath, partialSum_reflectPath]

theorem pathLaw_map_reflectPath (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (pathLaw ρ).map reflectPath = pathLaw (ρ.map Neg.neg) := by
  exact Measure.infinitePi_map_pi (fun _ : ℕ => ρ) (fun _ => measurable_neg)

theorem driftStep_map_neg (ρ : Measure ℝ) (μ : ℝ) :
    (driftStep ρ μ).map Neg.neg = driftStep (ρ.map Neg.neg) (-μ) := by
  unfold driftStep
  rw [Measure.map_map measurable_neg (by fun_prop), Measure.map_map (by fun_prop) measurable_neg]
  congr 1
  funext x
  simp only [Function.comp_apply]
  ring

end PGM.WienerHopf
