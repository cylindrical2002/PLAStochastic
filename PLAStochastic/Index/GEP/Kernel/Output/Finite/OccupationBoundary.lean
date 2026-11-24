import PLAStochastic.Index.GEP.Kernel.Output.Finite.StopBoundary
import PLAStochastic.Index.GEP.Kernel.Output.Finite.InsertedOccupation

/-!
# Actual finite occupation increments and their endpoint boundary

After a marked gap, the next iid gap can be integrated out. The resulting
occupation reward is exactly `kernelBoundaryReward`. Its spatial primitive
separates the true derivative increment from the endpoint reward CDF; the
latter still records the genuine next-gap increment before slope coarea.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
set_option maxHeartbeats 800000

/-- The genuine occupation reward after inserting one earlier gap. -/
def outputOccupationTerm (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ)
    (C : ℝ) (k i : ℕ) (x : ℝ) : ℝ :=
  fluxPrefixWeighted (iidLaw ν) eps k i
    (fun g x => kernelBoundaryReward ν C ψ (gapKeys (Function.update g i x) k)) x

/-- The direct derivative increment on the same original inserted path. -/
def outputOccupationDirect (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ)
    (C : ℝ) (k i : ℕ) (x : ℝ) : ℝ :=
  ∫ g, incInd eps (fun s => ψ (s/C)/C) k (Function.update g i x) ∂iidLaw ν

/-- The difference of actual endpoint output rewards across the next gap. -/
def outputOccupationBoundaryCDF (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ)
    (C : ℝ) (k i : ℕ) (x : ℝ) : ℝ :=
  outputPrefixBoundaryCDF (iidLaw ν) eps k i
    (fun g z => testFn ψ (gapKeys (Function.update g i z) (k+1) / C)) x -
  outputPrefixBoundaryCDF (iidLaw ν) eps k i
    (fun g z => testFn ψ (gapKeys (Function.update g i z) k / C)) x

/-- Integrating the original increment is the difference of the original
weighted survival integrals, without modifying the inserted stopping event. -/
theorem output_inserted_increment_eq_sub (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (F : ℝ → ℝ) (k i : ℕ) (x : ℝ)
    (h1 : Integrable (fun g => F (gapKeys (Function.update g i x) (k+1))) (iidLaw ν))
    (h0 : Integrable (fun g => F (gapKeys (Function.update g i x) k)) (iidLaw ν)) :
    (∫ g, incInd eps F k (Function.update g i x) ∂iidLaw ν) =
      fluxPrefixWeighted (iidLaw ν) eps k i (fun g z => F (gapKeys (Function.update g i z) (k+1))) x -
      fluxPrefixWeighted (iidLaw ν) eps k i (fun g z => F (gapKeys (Function.update g i z) k)) x := by
  have hS : MeasurableSet {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)} :=
    (measurableSet_lt_gapSegLen eps k).preimage
      ((measurable_update_pair i).comp (measurable_const.prodMk measurable_id))
  unfold fluxPrefixWeighted
  rw [← integral_sub (h1.indicator hS) (h0.indicator hS)]
  apply integral_congr_ae
  exact Eventually.of_forall fun g => by
    simp only [incInd, survSet, indicator_apply, mem_ofPred_eq]
    split_ifs <;> ring

theorem output_inserted_increment_integrable (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (F : ℝ → ℝ) (k i : ℕ) (x : ℝ)
    (h1 : Integrable (fun g => F (gapKeys (Function.update g i x) (k+1))) (iidLaw ν))
    (h0 : Integrable (fun g => F (gapKeys (Function.update g i x) k)) (iidLaw ν)) :
    Integrable (fun g => incInd eps F k (Function.update g i x)) (iidLaw ν) := by
  have hS : MeasurableSet {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)} :=
    (measurableSet_lt_gapSegLen eps k).preimage
      ((measurable_update_pair i).comp (measurable_const.prodMk measurable_id))
  exact (h1.sub h0).indicator hS

/-- Next-gap Fubini identifies the actual expected output increment with the
occupation reward. The required moments follow directly from `RegLaw`. -/
theorem output_occupation_eq_increment {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (eps : ℝ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η/C ≤ θ/4) {k i : ℕ} (hik : i < k) {x : ℝ} (hx : 0 ≤ x) :
    outputOccupationTerm eps ν ψ C k i x =
      ∫ g, incInd eps (fun s => testFn ψ (s/C)) k (Function.update g i x) ∂iidLaw ν := by
  have hI := output_inserted_increment_integrable eps ν (fun s => testFn ψ (s/C)) k i x
    (flux_partial_outTest_integrable hν hθ hψ hη hC hηθ (by omega : i < k+1) hx)
    (flux_partial_outTest_integrable hν hθ hψ hη hC hηθ hik hx)
  exact (flux_inserted_output_increment eps C ν hψ hik.ne x hI).symm

/-- The finite genuine occupation term has an identified endpoint boundary,
with the original direct derivative increment kept separate. -/
theorem output_occupation_boundary {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (eps : ℝ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η/C ≤ θ/4) {k i : ℕ} (hk : 2 ≤ k) (hik : i < k) :
    ∃ j B : ℝ → ℝ,
      AEPrimitive (outputOccupationBoundaryCDF eps ν ψ C k i) j ∧
      B =ᵐ[volume.restrict (Ioi (0 : ℝ))] j ∧
      AEPrimitive (outputOccupationTerm eps ν ψ C k i)
        (fun x => outputOccupationDirect eps ν ψ C k i x + B x) := by
  let fp : (ℕ → ℝ) → ℝ → ℝ := fun g x => ψ (gapKeys (Function.update g i x) (k+1)/C)/C
  let fn : (ℕ → ℝ) → ℝ → ℝ := fun g x => ψ (gapKeys (Function.update g i x) k/C)/C
  obtain ⟨jp, Bp, ⟨hjp, cp, hcp⟩, hBp, hIp, dp, hdp⟩ :=
    output_prefix_actual_boundary hν hθ (iidLaw ν) le_rfl eps hk
      (by omega : i < k+1) hψ hη hC hηθ
  obtain ⟨jn, Bn, ⟨hjn, cn, hcn⟩, hBn, hIn, dn, hdn⟩ :=
    output_prefix_actual_boundary hν hθ (iidLaw ν) le_rfl eps hk hik hψ hη hC hηθ
  let H : ℝ → ℝ := fun x => fluxPrefixWeighted (iidLaw ν) eps k i fp x -
    fluxPrefixWeighted (iidLaw ν) eps k i fn x
  let B : ℝ → ℝ := fun x => H x + (Bp x-Bn x) - outputOccupationDirect eps ν ψ C k i x
  have heH (x : ℝ) (hx : 0 ≤ x) : outputOccupationDirect eps ν ψ C k i x = H x :=
    output_inserted_increment_eq_sub eps ν (fun s => ψ (s/C)/C) k i x
      (output_partial_derivative_integrable hν hθ hψ hη hC hηθ (by omega : i < k+1) hx)
      (output_partial_derivative_integrable hν hθ hψ hη hC hηθ hik hx)
  refine ⟨fun x => jp x-jn x, B, ?_, ?_, ?_⟩
  · refine ⟨fun R => (hjp R).sub (hjn R), cp-cn, ?_⟩
    filter_upwards [hcp, hcn] with x hpx hnx
    change _ - _ = _
    rw [hpx, hnx, intervalIntegral.integral_sub (hjp x) (hjn x)]
    ring
  · filter_upwards [hBp, hBn, ae_restrict_mem measurableSet_Ioi] with x hpx hnx hx
    dsimp only [B]
    rw [heH x hx.le, hpx, hnx]
    ring
  · have he : (fun x => outputOccupationDirect eps ν ψ C k i x + B x) =
        fun x => (fluxPrefixWeighted (iidLaw ν) eps k i fp x + Bp x) -
          (fluxPrefixWeighted (iidLaw ν) eps k i fn x + Bn x) := by
      funext x
      dsimp [B, H]
      ring
    rw [he]
    refine ⟨fun R => (hIp R).sub (hIn R), dp-dn, ?_⟩
    filter_upwards [hdp, hdn, ae_restrict_mem measurableSet_Ioi] with x hpx hnx hx
    rw [output_occupation_eq_increment hν hθ eps hψ hη hC hηθ hik hx.le,
      output_inserted_increment_eq_sub eps ν (fun s => testFn ψ (s/C)) k i x
        (flux_partial_outTest_integrable hν hθ hψ hη hC hηθ (by omega : i < k+1) hx.le)
        (flux_partial_outTest_integrable hν hθ hψ hη hC hηθ hik hx.le)]
    rw [hpx, hnx, intervalIntegral.integral_sub (hIp x) (hIn x)]
    ring

end
end PGM
