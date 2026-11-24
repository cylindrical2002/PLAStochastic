import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.PrefixBound
import PLAStochastic.Index.GEP.Kernel.Output.Finite.OutTestPrefix

/-!
# Quantitative actual output primitives

For each finite stopping piece, the derivative mass is controlled by the
exponential moment of the original unmarked partial sum. This is the estimate
used with the predetermined surviving windows when summing the stopping pieces.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval

theorem flux_prefix_outTest_primitive_bound {ν : ProbabilityMeasure ℝ}
    (hac : (ν : Measure ℝ) ≪ volume) (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    (P : Measure (ℕ → ℝ)) [IsFiniteMeasure P] (hP : P ≪ iidLaw ν)
    (eps : ℝ) {k : ℕ} (hk : 2 ≤ k) (i : ℕ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    {S : (ℕ → ℝ) → ℝ} (hS : Measurable S) (hS0 : ∀ᵐ g ∂P, 0 ≤ S g)
    (hExp : Integrable (fun g => Real.exp ((2 * η / C) * S g)) P) :
    ∃ j : ℝ → ℝ,
      AEPrimitive (fluxPrefixWeighted P eps k i (fun g x => testFn ψ ((S g + x) / C))) j ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖j x‖) ≤
        ((|R| * (M / C) + 2 * (M / η)) * Real.exp ((2 * η / C) * max 0 R)) *
          ∫ g, Real.exp ((2 * η / C) * S g) ∂P := by
  let BF := fun R g => (M / η * Real.exp ((2 * η / C) * max 0 R)) *
    Real.exp ((2 * η / C) * S g)
  let Bf := fun R g => (M / C * Real.exp ((2 * η / C) * max 0 R)) *
    Real.exp ((2 * η / C) * S g)
  have hh : ∃ j : ℝ → ℝ,
      AEPrimitive (fluxPrefixWeighted P eps k i (fun g x => testFn ψ ((S g + x) / C))) j ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖j x‖) ≤
        |R| * (∫ g, Bf R g ∂P) + 2 * ∫ g, BF R g ∂P := by
    apply flux_prefix_moving_weight_primitive_bound hac hpos P hP eps hk i
      (f := fun g x => ψ ((S g + x) / C) / C)
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
  obtain ⟨j, hj, hb⟩ := hh
  refine ⟨j, hj, fun R => (hb R).trans_eq ?_⟩
  dsimp only [BF, Bf]
  rw [integral_const_mul, integral_const_mul]
  ring

/-- The bound applies to the original inserted partial sum and every marked
coordinate, including the final gap of the prospective stopped block. -/
theorem flux_prefix_output_partial_bound {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    (P : Measure (ℕ → ℝ)) [IsFiniteMeasure P] (hP : P ≤ iidLaw ν)
    (eps : ℝ) {k i t : ℕ} (hk : 2 ≤ k) (hit : i < t)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) :
    ∃ j : ℝ → ℝ,
      AEPrimitive (fluxPrefixWeighted P eps k i
        (fun g x => testFn ψ (gapKeys (Function.update g i x) t / C))) j ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖j x‖) ≤
        ((|R| * (M / C) + 2 * (M / η)) * Real.exp ((2 * η / C) * max 0 R)) *
          ∫ g, Real.exp ((2 * η / C) * fluxUnmarkedSum t i g) ∂P := by
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
  obtain ⟨j, hj, hb⟩ := flux_prefix_outTest_primitive_bound hac hν.ae_pos P hP.absolutelyContinuous
    eps hk i hψ hη hC (measurable_fluxUnmarkedSum t i) hS0
    ((flux_regLaw_unmarked_exp hν hθ (by positivity) hκθ t i).mono_measure hP)
  refine ⟨j, ?_, hb⟩
  simpa only [flux_gapKeys_update hit] using hj

end
end PGM
