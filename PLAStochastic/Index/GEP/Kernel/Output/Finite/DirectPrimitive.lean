import PLAStochastic.Index.GEP.Kernel.Output.Finite.OccupationDerivative

/-!
# Direct primitives before the marked stopping boundary

These formulas differentiate only an inserted physical sum. The path measure
can already be restricted to any event independent of the inserted value.
All derivative representatives are extended by zero to negative values.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval ENNReal

theorem output_integral_primitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] {F f : Ω → ℝ → ℝ}
    (h0 : Integrable (fun ω => F ω 0) P)
    (hprod : ∀ R : ℝ, Integrable
      (fun p : Ω × ℝ => (Ioi (0 : ℝ)).indicator (f p.1) p.2)
      (P.prod (volume.restrict (Ι (0 : ℝ) R))))
    (hF : ∀ᵐ ω ∂P, ∀ x : ℝ, 0 ≤ x →
      (∫ t in (0 : ℝ)..x, f ω t) = F ω x - F ω 0) :
    AEPrimitive (fun x => ∫ ω, F ω x ∂P)
      (fun x => ∫ ω, (Ioi (0 : ℝ)).indicator (f ω) x ∂P) := by
  refine ⟨fun R => ?_, ∫ ω, F ω 0 ∂P, ?_⟩
  · rw [intervalIntegrable_iff]
    exact (hprod R).integral_prod_right
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 0 < x at hx
    have hi : Integrable (fun ω => ∫ t in (0 : ℝ)..x,
        (Ioi (0 : ℝ)).indicator (f ω) t) P := by
      simpa only [intervalIntegral.integral_of_le hx.le, uIoc_of_le hx.le] using
        (hprod x).integral_prod_left
    have he : ∀ᵐ ω ∂P, F ω x = F ω 0 +
        ∫ t in (0 : ℝ)..x, (Ioi (0 : ℝ)).indicator (f ω) t := by
      filter_upwards [hF] with ω hω
      have heI : (∫ t in (0 : ℝ)..x, (Ioi (0 : ℝ)).indicator (f ω) t) =
          ∫ t in (0 : ℝ)..x, f ω t := by
        rw [intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_of_le hx.le]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht.1) _
      rw [heI, hω x hx.le]
      ring
    rw [integral_congr_ae he, integral_add h0 hi,
      ← intervalIntegral_integral_swap (μ := P) (a := 0) (b := x)
        (f := fun t ω => (Ioi (0 : ℝ)).indicator (f ω) t) (hprod x).swap]

theorem output_partial_direct_primitive {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    (P : Measure (ℕ → ℝ)) [IsFiniteMeasure P] (hP : P ≤ iidLaw ν)
    {i t : ℕ} (hit : i < t) {η M C : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C) (hηθ : η / C ≤ θ / 4) :
    AEPrimitive
      (fun x => ∫ g, testFn ψ (gapKeys (Function.update g i x) t / C) ∂P)
      ((Ioi (0 : ℝ)).indicator
        (fun x => ∫ g, ψ (gapKeys (Function.update g i x) t / C) / C ∂P)) := by
  simp_rw [flux_gapKeys_update hit]
  have hκθ : 2 * η / C ≤ θ / 2 := by
    calc
      2 * η / C = 2 * (η / C) := by ring
      _ ≤ θ / 2 := by linarith
  have hExp := (flux_regLaw_unmarked_exp hν hθ (by positivity) hκθ t i).mono_measure hP
  have hall : ∀ᵐ g ∂P, ∀ j, 0 < g j := by
    apply ae_mono hP
    change ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving
      |>.ae hν.ae_pos
  have h0 : Integrable (fun g => testFn ψ ((fluxUnmarkedSum t i g + 0) / C)) P := by
    simpa only [flux_gapKeys_update hit] using
      (flux_partial_outTest_integrable hν hθ hψ hη hC hηθ hit (by norm_num : (0 : ℝ) ≤ 0)).mono_measure hP
  have hprod (R : ℝ) : Integrable
      (fun p : (ℕ → ℝ) × ℝ => (Ioi (0 : ℝ)).indicator
        (fun x => ψ ((fluxUnmarkedSum t i p.1 + x) / C) / C) p.2)
      (P.prod (volume.restrict (Ι (0 : ℝ) R))) := by
    change Integrable ({p : (ℕ → ℝ) × ℝ | 0 < p.2}.indicator
      (fun p => ψ ((fluxUnmarkedSum t i p.1 + p.2) / C) / C)) _
    apply flux_section_integrable_prod_of_local_bound P
      (A := {p : (ℕ → ℝ) × ℝ | 0 < p.2})
      (f := fun g x => ψ ((fluxUnmarkedSum t i g + x) / C) / C)
      (B := fun R g => (M / C * Real.exp ((2 * η / C) * max 0 R)) *
        Real.exp ((2 * η / C) * fluxUnmarkedSum t i g))
      (measurableSet_lt measurable_const measurable_snd)
      (Eventually.of_forall fun _ _ h => h.le)
      ((hψ.1.comp (((measurable_fluxUnmarkedSum t i).comp measurable_fst).add measurable_snd
        |>.div_const C)).div_const C)
      (fun _ => hExp.const_mul _) ?_ R
    intro R
    filter_upwards [hall] with g hg x hx
    exact (flux_testFn_shift_bounds hψ hη hC
      (fluxUnmarkedSum_nonneg_le (fun j => (hg j).le) t i).1 hx).2
  have hp := output_integral_primitive P h0 hprod (by
    filter_upwards [hall] with g hg x hx
    exact flux_testFn_shift_primitive hψ hC
      (fluxUnmarkedSum_nonneg_le (fun j => (hg j).le) t i).1 le_rfl hx)
  convert hp using 1
  funext x
  by_cases hx : 0 < x
  · simp only [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
  · simp only [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), integral_zero]

end
end PGM
