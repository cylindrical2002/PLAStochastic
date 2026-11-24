import PLAStochastic.Index.KEP.ReferenceScale.LawOrbit
import PLAStochastic.ForMathlib.Probability.Stopping.StoppedTelescoping

/-!
# An exact cutoff telescoping identity for the actual reference output

For every bounded measurable output test, the true next reference law equals
the free cutoff expectation plus surviving increments minus finite stopped
corrections. The long series is absolutely integrable. All stopping-time
finiteness and integrability inputs are discharged on the actual reference orbit.
The further decomposition of these prefixes into facet graphs is not asserted.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

def kepReferenceOutputIncrement (eps : ℝ) (j : ℕ) (φ : ℝ → ℝ) (k : ℕ)
    (g : ℕ → ℝ) : ℝ :=
  stoppedIncrement (fun g => (gapSegLen eps g).toNat)
    (fun k g => φ (gapKeys g k / lawC eps (kepReferenceLaw eps j))) k g

theorem kepReference_output_cutoff_telescoping :
    ∃ eps0 : ℝ, ∀ eps, eps0 ≤ eps → ∀ j : ℕ,
      ∀ φ : ℝ → ℝ, Measurable φ → ∀ B : ℝ, 0 ≤ B → (∀ x, |φ x| ≤ B) → ∀ M : ℕ,
        (∀ᵐ g ∂iidLaw (kepReferenceLaw eps j), gapSegLen eps g ≠ ⊤) ∧
        Summable (fun k : ℕ => ∫ g, kepReferenceOutputIncrement eps j φ (k + M) g
          ∂iidLaw (kepReferenceLaw eps j)) ∧
        (∫ x, φ x ∂(kepReferenceLaw eps (j + 1) : Measure ℝ)) =
          (∫ g, φ (gapKeys g M / lawC eps (kepReferenceLaw eps j))
            ∂iidLaw (kepReferenceLaw eps j)) +
          (∑' k : ℕ, ∫ g, kepReferenceOutputIncrement eps j φ (k + M) g
            ∂iidLaw (kepReferenceLaw eps j)) -
          ∑ k ∈ range M, ∫ g, (if (gapSegLen eps g).toNat ≤ k then
            φ (gapKeys g (k + 1) / lawC eps (kepReferenceLaw eps j)) -
              φ (gapKeys g k / lawC eps (kepReferenceLaw eps j)) else 0)
            ∂iidLaw (kepReferenceLaw eps j) := by
  obtain ⟨D, theta, vlo, vhi, e0, hD, ht, hvlo, hvhi, hreg⟩ := kepReferenceLaw_regular
  refine ⟨max e0 (epsZero (regB vhi) (regBeta D theta vlo)), ?_⟩
  intro eps he j φ hφ B hB hb M
  have he0 : e0 ≤ eps := (le_max_left _ _).trans he
  have heps : epsZero (regB vhi) (regBeta D theta vlo) ≤ eps := (le_max_right _ _).trans he
  obtain ⟨-, -, -, -, hfin, hiT, -, -, -⟩ :=
    momClass_setup (regV_pos hvlo) heps ((hreg eps he0 j).momClass ht hvlo)
  let Y := fun k g => φ (gapKeys g k / lawC eps (kepReferenceLaw eps j))
  have hY (k : ℕ) : Measurable (Y k) :=
    hφ.comp (((measurable_pi_apply k).comp measurable_gapKeys).div_const _)
  have hT : Measurable (fun g : ℕ → ℝ => (gapSegLen eps g).toNat) :=
    measurable_from_top.comp (isStoppingRule_gapSegLen eps).measurable
  obtain ⟨hs, hidentity⟩ := integral_stopped_value_telescoping hT hiT hY hB
    (fun k g => hb _) M
  refine ⟨hfin, hs, ?_⟩
  have hmap : (kepReferenceLaw eps (j + 1) : Measure ℝ) =
      (iidLaw (kepReferenceLaw eps j)).map
        (fun g => stopSum eps g / lawC eps (kepReferenceLaw eps j)) := by
    rw [kepReferenceLaw_succ]
    rfl
  rw [hmap, integral_map ((measurable_stopSum eps).div_const _).aemeasurable hφ.aestronglyMeasurable]
  exact hidentity

end

end PGM
