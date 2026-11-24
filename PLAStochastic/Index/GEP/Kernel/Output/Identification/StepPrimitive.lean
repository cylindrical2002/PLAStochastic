import PLAStochastic.Index.GEP.Kernel.Output.Identification.StepSummation

/-!
# The exact derivative of every birth/occupation term

All indices, including the initial prefix and the marked birth coordinate,
are included. Only the genuine post-mark facets contribute a boundary term.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval ENNReal

theorem output_aePrimitive_congr_fun {J J' j : ℝ → ℝ} (hp : AEPrimitive J j)
    (he : J' =ᵐ[volume.restrict (Ioi (0 : ℝ))] J) : AEPrimitive J' j := by
  refine ⟨hp.1, hp.2.choose, ?_⟩
  filter_upwards [he, hp.2.choose_spec] with x hx hy
  exact hx.trans hy

theorem output_aePrimitive_sub {J K j k : ℝ → ℝ}
    (hJ : AEPrimitive J j) (hK : AEPrimitive K k) :
    AEPrimitive (fun x => J x-K x) (fun x => j x-k x) := by
  simpa only [neg_one_mul, ← sub_eq_add_neg] using hJ.add (hK.const_mul (-1))

def outputStepDerivative (eps : ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (ψ : ℝ → ℝ) (C : ℝ) (a : ℕ × ℕ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (fun x =>
    (∫ g, outputStep eps (fun s => ψ (s/C)/C) a x g ∂iidLaw ν) +
      outputIFTerm eps ν f ψ C a x)

theorem output_step_concrete_primitive {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} (heps : 1 ≤ eps) {η M C : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C) (hηθ : η/C ≤ θ/4)
    (a : ℕ × ℕ) :
    AEPrimitive (fun x => ∫ g, outputStep eps (fun s => testFn ψ (s/C)) a x g ∂iidLaw ν)
      (outputStepDerivative eps ν f ψ C a) := by
  classical
  rcases a with ⟨k,i⟩
  by_cases he : i = k
  · subst i
    have hp := output_partial_direct_primitive hν hθ ((iidLaw ν).restrict (survSet eps k))
      Measure.restrict_le_self (Nat.lt_succ_self k) hψ hη hC hηθ
    have hJ : (fun x => ∫ g, outputStep eps (fun s => testFn ψ (s/C)) (k,k) x g ∂iidLaw ν) =
        (fun x => ∫ g in survSet eps k, testFn ψ (gapKeys (Function.update g k x) (k+1)/C) ∂iidLaw ν) := by
      funext x
      simp_rw [output_step_birth]
      exact integral_indicator (measurableSet_survSet eps k)
    rw [hJ]
    convert hp using 1
    funext x
    unfold outputStepDerivative
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      simp only [outputIFTerm, lt_self_iff_false, if_false, add_zero]
      simp_rw [output_step_birth]
      exact integral_indicator (measurableSet_survSet eps k)
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  · by_cases hik : i < k
    · by_cases hk : 2 ≤ k
      · have hp := output_occupation_concrete_derivative hν hθ hf hνf (eps := eps)
          (by linarith) hk hik hψ hη hC hηθ
        have hD : outputStepDerivative eps ν f ψ C (k,i) =
            outputOccupationDerivative eps ν f ψ C k i := by
          unfold outputStepDerivative outputOccupationDerivative
          congr 1
          funext x
          simp_rw [output_step_after eps _ hik]
          simp only [outputIFTerm, hik, if_true, outputOccupationDirect]
        rw [hD]
        apply output_aePrimitive_congr_fun hp
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        simp_rw [output_step_after eps _ hik]
        exact (output_occupation_eq_increment hν hθ eps hψ hη hC hηθ hik hx.le).symm
      · have hk1 : k = 1 := by omega
        have hi0 : i = 0 := by omega
        subst k i
        have hS (g : ℕ → ℝ) : g ∈ survSet eps 1 := by
          change (1 : ℕ∞) < gapSegLen eps g
          exact lt_of_lt_of_le (by norm_num : (1 : ℕ∞) < 3) (three_le_segLen heps (gapKeys g))
        have hs (F : ℝ → ℝ) (x : ℝ) (g : ℕ → ℝ) :
            outputStep eps F (1,0) x g = F (gapKeys (Function.update g 0 x) 2) -
              F (gapKeys (Function.update g 0 x) 1) := by
          rw [output_step_after eps F (by omega : 0 < 1), incInd, indicator_of_mem (hS _)]
        have hp := output_aePrimitive_sub
          (output_partial_direct_primitive hν hθ (iidLaw ν) le_rfl (by omega : 0 < 2) hψ hη hC hηθ)
          (output_partial_direct_primitive hν hθ (iidLaw ν) le_rfl (by omega : 0 < 1) hψ hη hC hηθ)
        have hd : outputStepDerivative eps ν f ψ C (1,0) =
            (Ioi (0 : ℝ)).indicator (fun x =>
              (∫ g, ψ (gapKeys (Function.update g 0 x) 2/C)/C ∂iidLaw ν) -
              (∫ g, ψ (gapKeys (Function.update g 0 x) 1/C)/C ∂iidLaw ν)) := by
          funext x
          unfold outputStepDerivative
          by_cases hx : x ∈ Ioi (0 : ℝ)
          · rw [indicator_of_mem hx, indicator_of_mem hx]
            simp only [outputIFTerm, Nat.zero_lt_succ, if_true,
              output_IF_weighted_prefix_zero_of_lt_two ν f eps (by omega : 1 < 2), add_zero]
            simp_rw [hs]
            exact integral_sub
              (output_partial_derivative_integrable hν hθ hψ hη hC hηθ (by omega : 0 < 2) hx.le)
              (output_partial_derivative_integrable hν hθ hψ hη hC hηθ (by omega : 0 < 1) hx.le)
          · rw [indicator_of_notMem hx, indicator_of_notMem hx]
        rw [hd]
        apply output_aePrimitive_congr_fun
          (output_aePrimitive_congr_positive hp (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            simp only [indicator_of_mem hx]))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        simp_rw [hs]
        exact integral_sub
          (flux_partial_outTest_integrable hν hθ hψ hη hC hηθ (by omega : 0 < 2) hx.le)
          (flux_partial_outTest_integrable hν hθ hψ hη hC hηθ (by omega : 0 < 1) hx.le)
    · have hle : ¬ i ≤ k := by omega
      have hz (F : ℝ → ℝ) (x : ℝ) : outputStep eps F (k,i) x = fun _ => 0 := by
        funext g
        exact if_neg hle
      simp only [hz, integral_zero, outputStepDerivative, outputIFTerm, hik, if_false,
        add_zero, indicator_zero]
      exact ⟨fun R => (integrable_zero _ _ _).intervalIntegrable, 0,
        Eventually.of_forall fun x => by simp⟩

end
end PGM
