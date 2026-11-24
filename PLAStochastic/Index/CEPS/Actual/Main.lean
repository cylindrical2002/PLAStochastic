import PLAStochastic.Index.CEPS.Actual.Representation
import PLAStochastic.Index.CEPS.Actual.Strip
import PLAStochastic.Index.CEPS.Actual.FirstPassage
import PLAStochastic.Index.CEPS.Actual.Drawup
import PLAStochastic.Index.CEPS.Actual.Hadamard
import PLAStochastic.Index.CEPS.Actual.SegmentTail
import PLAStochastic.Index.GEP.OrbitClosure.OrbitMoments
import PLAStochastic.Index.GEP.OrbitClosure.RegularClass

/-!
# P-CEPS WP8: exact actual-side identities (assembly)

Lemma S-1 of `research/2026-10-02-lean-ceps/blueprint-CS.md` on the regular class: for `RegLaw`
inputs and `ε ≥ ε₀` the first segment is a.s. finite with integrable length
(`momClass_setup`), so theorem (E) and its domination hold for every bounded density version `f`
of `ν` (`ceps_exact_marked_rep_of_regLaw`). A regular law has such a version
(`RegLaw.exists_cepsGapDensity`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- **Theorem (E) on the regular class.** For `RegLaw D θ vlo vhi ν`, `ε ≥ ε₀`, any bounded density
`f` of `ν` vanishing on `(-∞, 0]`, and `Re t ≥ 0`:
`E e^{-tS_T} = φ(t)^{⌊2ε⌋+1} - (1 - φ(t)) ∫_{(-1,∞)} J_t`, with `J_t` integrable,
`∫ ‖J_t‖ ≤ ∫ ‖J_0‖` and `∫ ‖J_0‖ = E T - ⌊2ε⌋ - 1`. -/
theorem ceps_exact_marked_rep_of_regLaw {D θ vlo vhi eps : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (heps : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {t : ℂ} (ht : 0 ≤ t.re) :
    ∫ g, Complex.exp (-t * stopSum eps g) ∂(iidLaw ν) =
        cepsLaplace ν t ^ (⌊2 * eps⌋₊ + 1) -
          (1 - cepsLaplace ν t) * ∫ μ in Ioi (-1 : ℝ), cepsActualPair ν f eps t μ ∧
      IntegrableOn (cepsActualPair ν f eps t) (Ioi (-1 : ℝ)) ∧
      ∫ μ in Ioi (-1 : ℝ), ‖cepsActualPair ν f eps t μ‖ ≤
        ∫ μ in Ioi (-1 : ℝ), ‖cepsActualPair ν f eps 0 μ‖ ∧
      ∫ μ in Ioi (-1 : ℝ), ‖cepsActualPair ν f eps 0 μ‖ = lawC eps ν - ((⌊2 * eps⌋₊ : ℝ) + 1) := by
  obtain ⟨-, he1, -, -, hfin, hT, -⟩ := momClass_setup (regV_pos hvlo) heps (hν.momClass hθ hvlo)
  have hpos : 0 < eps := by linarith
  exact ⟨hf.ceps_exact_marked_rep hpos hfin hT ht,
    hf.ceps_exact_marked_rep_domination hpos hfin hT ht⟩

end

end PGM
