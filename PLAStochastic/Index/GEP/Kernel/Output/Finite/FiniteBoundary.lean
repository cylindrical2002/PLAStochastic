import PLAStochastic.Index.GEP.Kernel.Output.Finite.PrefixBoundary
import PLAStochastic.Index.GEP.Kernel.Output.Finite.OutTestPrefix

/-!
# The identified finite output boundary under the original regular law

The boundary is the derivative of the actual endpoint reward CDF, uniformly
for the original measurable output tests. The interior derivative uses only
`ψ`; no derivative of `ψ` and no global endpoint moment is assumed.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

theorem output_prefix_outTest_boundary {ν : ProbabilityMeasure ℝ}
    (hac : (ν : Measure ℝ) ≪ volume) (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    (P : Measure (ℕ → ℝ)) [IsFiniteMeasure P] (hP : P ≪ iidLaw ν)
    (eps : ℝ) {k : ℕ} (hk : 2 ≤ k) (i : ℕ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    {S : (ℕ → ℝ) → ℝ} (hS : Measurable S) (hS0 : ∀ᵐ g ∂P, 0 ≤ S g)
    (hExp : Integrable (fun g => Real.exp ((2 * η / C) * S g)) P) :
    ∃ j B : ℝ → ℝ,
      AEPrimitive (outputPrefixBoundaryCDF P eps k i
        (fun g x => testFn ψ ((S g + x) / C))) j ∧
      B =ᵐ[volume.restrict (Ioi (0 : ℝ))] j ∧
      AEPrimitive
        (fluxPrefixWeighted P eps k i (fun g x => testFn ψ ((S g + x) / C)))
        (fun x => fluxPrefixWeighted P eps k i (fun g x => ψ ((S g + x) / C) / C) x + B x) := by
  apply output_prefix_boundary_primitive hac hpos P hP eps hk i
    (BF := fun R g => (M / η * Real.exp ((2 * η / C) * max 0 R)) *
      Real.exp ((2 * η / C) * S g))
    (Bf := fun R g => (M / C * Real.exp ((2 * η / C) * max 0 R)) *
      Real.exp ((2 * η / C) * S g))
  · exact hψ.measurable_testFn.comp ((hS.comp measurable_fst).add measurable_snd |>.div_const C)
  · exact (hψ.1.comp ((hS.comp measurable_fst).add measurable_snd |>.div_const C)).div_const C
  · intro R
    exact hExp.const_mul _
  · intro R
    exact hExp.const_mul _
  · intro R
    filter_upwards [hS0] with g hg x hx
    exact (flux_testFn_shift_bounds hψ hη hC hg hx).1
  · intro R
    filter_upwards [hS0] with g hg x hx
    exact (flux_testFn_shift_bounds hψ hη hC hg hx).2
  · filter_upwards [hS0] with g hg a b ha hab
    exact flux_testFn_shift_primitive hψ hC hg ha hab

theorem output_prefix_actual_boundary {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    (P : Measure (ℕ → ℝ)) [IsFiniteMeasure P] (hP : P ≤ iidLaw ν)
    (eps : ℝ) {k i t : ℕ} (hk : 2 ≤ k) (hit : i < t)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) :
    ∃ j B : ℝ → ℝ,
      AEPrimitive (outputPrefixBoundaryCDF P eps k i
        (fun g x => testFn ψ (gapKeys (Function.update g i x) t / C))) j ∧
      B =ᵐ[volume.restrict (Ioi (0 : ℝ))] j ∧
      AEPrimitive
        (fluxPrefixWeighted P eps k i
          (fun g x => testFn ψ (gapKeys (Function.update g i x) t / C)))
        (fun x => fluxPrefixWeighted P eps k i
          (fun g x => ψ (gapKeys (Function.update g i x) t / C) / C) x + B x) := by
  obtain ⟨ρ, _, _, _, _, hρ⟩ := hν.density
  have hac : (ν : Measure ℝ) ≪ volume := by
    rw [hρ]
    exact withDensity_absolutelyContinuous _ _
  have hgs : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving
      |>.ae hν.ae_pos
  have hS0 : ∀ᵐ g ∂P, 0 ≤ fluxUnmarkedSum t i g := by
    filter_upwards [hP.absolutelyContinuous hgs] with g hg
    exact (fluxUnmarkedSum_nonneg_le (fun j => (hg j).le) t i).1
  have hκθ : 2 * η / C ≤ θ / 2 := by
    have he : 2 * η / C = 2 * (η / C) := by ring
    rw [he]
    linarith
  obtain ⟨j, B, hBj, hBeq, hB⟩ := output_prefix_outTest_boundary hac hν.ae_pos P hP.absolutelyContinuous
    eps hk i hψ hη hC (measurable_fluxUnmarkedSum t i) hS0
    ((flux_regLaw_unmarked_exp hν hθ (by positivity) hκθ t i).mono_measure hP)
  refine ⟨j, B, ?_, hBeq, ?_⟩
  · simpa only [flux_gapKeys_update hit] using hBj
  · simpa only [flux_gapKeys_update hit] using hB


end
end PGM
