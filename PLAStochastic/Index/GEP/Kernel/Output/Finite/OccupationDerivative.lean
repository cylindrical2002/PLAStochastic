import PLAStochastic.Index.GEP.Kernel.Output.Finite.FacetBound

/-!
# The concrete output occupation derivative on the positive half-line

`OutTest` controls the test only at nonnegative physical sums. We use the
prescribed zero extension of the derivative outside the positive half-line,
without imposing any regularity of the test at negative arguments.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval ENNReal

theorem output_aePrimitive_positive {J j : ℝ → ℝ} (hp : AEPrimitive J j) :
    AEPrimitive J ((Ioi (0 : ℝ)).indicator j) := by
  refine ⟨fun R => ?_, hp.2.choose, ?_⟩
  · rw [intervalIntegrable_iff]
    exact (hp.1 R).def'.indicator measurableSet_Ioi
  filter_upwards [hp.2.choose_spec, ae_restrict_mem measurableSet_Ioi] with x hx hx0
  rw [hx]
  congr 1
  rw [intervalIntegral.integral_of_le hx0.le, intervalIntegral.integral_of_le hx0.le]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht.1) j).symm

theorem output_aePrimitive_congr_positive {J j j' : ℝ → ℝ} (hp : AEPrimitive J j)
    (he : j =ᵐ[volume.restrict (Ioi (0 : ℝ))] j') :
    AEPrimitive J ((Ioi (0 : ℝ)).indicator j') := by
  apply flux_aePrimitive_congr_derivative (output_aePrimitive_positive hp)
  exact (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioi).mp he

def outputOccupationDerivative (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ≥0∞) (ψ : ℝ → ℝ) (C : ℝ) (k i : ℕ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (fun x => outputOccupationDirect eps ν ψ C k i x +
    kernelIFWeightedPrefixKernel ν f eps k i
      (fun g => kernelBoundaryReward ν C ψ (gapKeys g k)) x)

/-- The actual occupation primitive uses the actual weighted facet kernel.
No substitute boundary kernel remains in this statement. -/
theorem output_occupation_concrete_derivative {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i : ℕ} (heps : 0 < eps) (hk : 2 ≤ k) (hik : i < k)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) :
    AEPrimitive (outputOccupationTerm eps ν ψ C k i)
      (outputOccupationDerivative eps ν f ψ C k i) := by
  obtain ⟨j, B, hj, hB, hp⟩ := output_occupation_boundary hν hθ eps hψ hη hC hηθ hk hik
  have hK := output_occupation_facet_aePrimitive hν hθ hf hνf heps hk hik hψ hη hC hηθ
  have he := kernel_aePrimitive_unique hj hK
  apply output_aePrimitive_congr_positive hp
  filter_upwards [hB, he] with x hx hy
  exact congrArg (fun z => outputOccupationDirect eps ν ψ C k i x + z) (hx.trans hy)

end
end PGM
