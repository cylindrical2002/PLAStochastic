import PLAStochastic.Index.CEPS.Total.LevelClass

/-! # Every continuous density of a level law carries the same level data -/

noncomputable section
open MeasureTheory
namespace PGM

theorem CepsLevelDensity.eq_of_continuous {n : ℕ} {ν : ProbabilityMeasure ℝ}
    {f g : ℝ → ℝ} (hg : CepsLevelDensity n ν g) (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x)) : f = g := by
  obtain ⟨hgm, hg0, -, -, hνg, -, -, -, hgS, -⟩ := hg
  have hgc : Continuous g := by
    have hh := hgS.contDiff.continuous.comp (f := fun x : ℝ => 1 - x) (by fun_prop)
    convert hh using 1
    funext x
    congr 1
    ring
  exact (hf.ae_eq_iff_eq volume hgc).mp
    (ae_eq_of_withDensity_eq hf.measurable hgm hf0 hg0 (hν.symm.trans hνg))

theorem CepsLevel.of_continuous_density {n : ℕ} {ν : ProbabilityMeasure ℝ}
    (h : CepsLevel n ν) {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x)) :
    CepsLevelDensity n ν f := by
  obtain ⟨g, hg⟩ := h
  rw [hg.eq_of_continuous hf hf0 hν]
  exact hg

end PGM
