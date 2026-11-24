import PLAStochastic.Index.GEP.Kernel.LinearSurvival.PathPotential
import PLAStochastic.Index.GEP.Kernel.LinearSurvival.SurvivalMoments

/-! # The signed affine walk on the original iid probability space -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- Coordinatewise affine centering realizes the transformed iid law exactly. -/
theorem linearSurvival_affine_map (ν : ProbabilityMeasure ℝ) (a ρ : ℝ) :
    (iidLaw ν).map (fun g : ℕ → ℝ => fun i => a * (g i - 1) - ρ) =
      iidLaw (kernelSurvivalLaw ν a ρ) := by
  simpa only [iidLaw, kernelSurvivalLaw, ProbabilityMeasure.toMeasure_map] using
    (Measure.infinitePi_map_pi (μ := fun _ : ℕ => (ν : Measure ℝ))
      (f := fun _ : ℕ => fun x : ℝ => a * (x - 1) - ρ) (by intro i; fun_prop))

theorem linearSurvival_affine_gapKeys (a ρ : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    gapKeys (fun i => a * (g i - 1) - ρ) n =
      a * (gapKeys g n - n) - ρ * n := by
  simp only [gapKeys, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  ring

/-- Equality of the actual finite-horizon probabilities, with the drift placed
in the boundary on the original gap space. -/
theorem linearSurvival_affine_probability (ν : ProbabilityMeasure ℝ)
    (a ρ δ : ℝ) (n : ℕ) :
    (iidLaw (kernelSurvivalLaw ν a ρ)).real (linearSurvivalStay δ n) =
      (iidLaw ν).real {g | ∀ j ≤ n, a * (gapKeys g j - j) ≤ δ + ρ * j} := by
  rw [← linearSurvival_affine_map ν a ρ]
  simp only [Measure.real]
  rw [Measure.map_apply (by fun_prop) (measurableSet_linearSurvivalStay δ n)]
  congr 2
  ext g
  simp only [mem_preimage, linearSurvivalStay, mem_ofPred_eq, linearSurvival_affine_gapKeys]
  constructor <;> intro hg j hj <;> have h := hg j hj <;> linarith

end
end PGM
