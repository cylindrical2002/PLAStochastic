import PLAStochastic.Index.GEP.Kernel.Output.Finite.BoundaryReward
import PLAStochastic.Index.GEP.RawDisc.Telescoping

/-!
# The actual inserted occupation term and its boundary reward

The next-gap Fubini identity remains valid after fixing any other gap. Thus the
reward used in the output boundary flux is the actual expected one-step output
increment, rather than an assumed coarea weight.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

theorem flux_inserted_increment_eq_reward (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) {i k : ℕ} (hik : i ≠ k) (x : ℝ)
    (hint : Integrable (fun g => incInd eps F k (Function.update g i x)) (iidLaw ν)) :
    (∫ g, incInd eps F k (Function.update g i x) ∂(iidLaw ν)) =
      ∫ g, (survSet eps k).indicator (fun h => incFn F ν (gapKeys h k))
        (Function.update g i x) ∂(iidLaw ν) := by
  classical
  have hm : Measurable (fun g => incInd eps F k (Function.update g i x)) :=
    (measurable_incInd eps hF k).comp
      ((measurable_update_pair i).comp (measurable_const.prodMk measurable_id))
  have hcomm (g : ℕ → ℝ) (y : ℝ) :
      Function.update (Function.update g k y) i x = Function.update (Function.update g i x) k y := by
    funext m
    by_cases hmi : m = i <;> by_cases hmk : m = k <;> simp_all
  have h := integral_piLaw_insert (fun _ => ν) k hm hint
  change (∫ g, incInd eps F k (Function.update g i x) ∂(iidLaw ν)) =
    ∫ g, ∫ y, incInd eps F k (Function.update (Function.update g k y) i x)
      ∂(ν : Measure ℝ) ∂(iidLaw ν) at h
  rw [h]
  apply integral_congr_ae
  refine Eventually.of_forall fun g => ?_
  simp_rw [hcomm]
  let g' := Function.update g i x
  change (∫ y, incInd eps F k (Function.update g' k y) ∂(ν : Measure ℝ)) =
    (survSet eps k).indicator (fun h => incFn F ν (gapKeys h k)) g'
  by_cases hs : g' ∈ survSet eps k
  · have hs' : ∀ y, Function.update g' k y ∈ survSet eps k := fun y =>
      (mem_survSet_update le_rfl g' y).2 hs
    simp only [incInd, indicator_of_mem (hs' _), indicator_of_mem hs,
      gapKeys_update_succ, gapKeys_update_self]
    rfl
  · have hs' : ∀ y, Function.update g' k y ∉ survSet eps k := fun y hy =>
      hs ((mem_survSet_update le_rfl g' y).1 hy)
    simp only [incInd, indicator_of_notMem (hs' _), indicator_of_notMem hs, integral_zero]

/-- At the fixed output scale, the inserted occupation reward is exactly the
`kernelBoundaryReward` for which the regular-class estimate has been proved. -/
theorem flux_inserted_output_increment (eps C : ℝ) (ν : ProbabilityMeasure ℝ)
    {η M : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) {i k : ℕ} (hik : i ≠ k) (x : ℝ)
    (hint : Integrable
      (fun g => incInd eps (fun s => testFn ψ (s / C)) k (Function.update g i x)) (iidLaw ν)) :
    (∫ g, incInd eps (fun s => testFn ψ (s / C)) k (Function.update g i x) ∂(iidLaw ν)) =
      ∫ g, (survSet eps k).indicator
        (fun h => kernelBoundaryReward ν C ψ (gapKeys h k)) (Function.update g i x) ∂(iidLaw ν) :=
  flux_inserted_increment_eq_reward eps ν
    (hψ.measurable_testFn.comp (measurable_id.div_const C)) hik x hint

end

end PGM
