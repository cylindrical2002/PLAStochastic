import PLAStochastic.Index.GEP.Kernel.Output.Finite.FiniteBoundary
import PLAStochastic.Index.GEP.Kernel.Output.Finite.StopPiece

/-!
# The genuine finite stopping piece: direct term and identified boundary

The stop event is the difference of the two actual survival events. The direct
term is the original stopped test derivative, while the boundary is identified
with the difference of the two actual endpoint reward CDFs. The final marked
gap is allowed, including when it lies outside the shorter prefix.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
set_option maxHeartbeats 800000

/-- The direct derivative of a finite stopped output piece. -/
def outputStoppedDirect (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ)
    (C : ℝ) (t i : ℕ) (x : ℝ) : ℝ :=
  ∫ g, {g | gapSegLen eps (Function.update g i x) = t}.indicator
    (fun g => ψ (stopSum eps (Function.update g i x) / C) / C) g ∂iidLaw ν

/-- The boundary CDF of the finite stopping piece, at the same output scale. -/
def outputStoppedBoundaryCDF (eps : ℝ) (ν : ProbabilityMeasure ℝ) (ψ : ℝ → ℝ)
    (C : ℝ) (t i : ℕ) (x : ℝ) : ℝ :=
  outputPrefixBoundaryCDF (iidLaw ν) eps (t-1) i
    (fun g z => testFn ψ (gapKeys (Function.update g i z) t / C)) x -
  outputPrefixBoundaryCDF (iidLaw ν) eps t i
    (fun g z => testFn ψ (gapKeys (Function.update g i z) t / C)) x

theorem output_partial_derivative_integrable {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {t i : ℕ} (hit : i < t) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g => ψ (gapKeys (Function.update g i x) t / C) / C) (iidLaw ν) := by
  have hκθ : 2 * η / C ≤ θ / 2 := by
    have he : 2 * η / C = 2 * (η / C) := by ring
    rw [he]
    linarith
  have hExp := flux_regLaw_unmarked_exp hν hθ (by positivity : 0 ≤ 2 * η / C) hκθ t i
  have hgs : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving
      |>.ae hν.ae_pos
  simp_rw [flux_gapKeys_update hit]
  refine (hExp.const_mul (M / C * Real.exp ((2 * η / C) * max 0 x))).mono'
    ((hψ.1.comp (((measurable_fluxUnmarkedSum t i).add_const x).div_const C)).div_const C
      |>.aestronglyMeasurable) ?_
  filter_upwards [hgs] with g hg
  exact (flux_testFn_shift_bounds hψ hη hC
    (fluxUnmarkedSum_nonneg_le (fun j => (hg j).le) t i).1 ⟨hx, le_max_right _ _⟩).2

theorem output_stopped_integral_eq_partial (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (F : ℝ → ℝ) (C : ℝ) (t i : ℕ) (x : ℝ) :
    (∫ g, {g | gapSegLen eps (Function.update g i x) = t}.indicator
      (fun g => F (stopSum eps (Function.update g i x) / C)) g ∂iidLaw ν) =
    ∫ g, {g | gapSegLen eps (Function.update g i x) = t}.indicator
      (fun g => F (gapKeys (Function.update g i x) t / C)) g ∂iidLaw ν := by
  apply integral_congr_ae
  exact Eventually.of_forall fun g => by
    simp only [indicator_apply, mem_ofPred_eq]
    split_ifs with ht
    · rw [stopSum, ht, ENat.toNat_natCast]
    · rfl

/-- The finite stopped output has its actual direct derivative and an endpoint
boundary. All analytic hypotheses are discharged on the original regular law. -/
theorem output_stop_piece_boundary {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (eps : ℝ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {t i : ℕ} (ht : 3 ≤ t) (hit : i < t) :
    ∃ j B : ℝ → ℝ,
      AEPrimitive (outputStoppedBoundaryCDF eps ν ψ C t i) j ∧
      B =ᵐ[volume.restrict (Ioi (0 : ℝ))] j ∧
      AEPrimitive (fluxOutputPiece eps ν ψ C t i)
        (fun x => outputStoppedDirect eps ν ψ C t i x + B x) := by
  let F : (ℕ → ℝ) → ℝ → ℝ := fun g x =>
    testFn ψ (gapKeys (Function.update g i x) t / C)
  let f : (ℕ → ℝ) → ℝ → ℝ := fun g x =>
    ψ (gapKeys (Function.update g i x) t / C) / C
  obtain ⟨jp, Bp, ⟨hjp, cp, hcp⟩, hBp, hIp, dp, hdp⟩ :=
    output_prefix_actual_boundary hν hθ (iidLaw ν) le_rfl eps (k := t-1)
      (by omega) hit hψ hη hC hηθ
  obtain ⟨jn, Bn, ⟨hjn, cn, hcn⟩, hBn, hIn, dn, hdn⟩ :=
    output_prefix_actual_boundary hν hθ (iidLaw ν) le_rfl eps (k := t)
      (by omega) hit hψ hη hC hηθ
  let H : ℝ → ℝ := fun x =>
    fluxPrefixWeighted (iidLaw ν) eps (t-1) i f x -
      fluxPrefixWeighted (iidLaw ν) eps t i f x
  let B : ℝ → ℝ := fun x => H x + (Bp x-Bn x) - outputStoppedDirect eps ν ψ C t i x
  have heH (x : ℝ) (hx : 0 ≤ x) : outputStoppedDirect eps ν ψ C t i x = H x := by
    unfold outputStoppedDirect
    rw [output_stopped_integral_eq_partial eps ν (fun y => ψ y / C) C t i x]
    exact flux_stop_integral_eq_sub (iidLaw ν) (F := f) (eps := eps) (i := i) (x := x)
      (by omega : 0 < t) (output_partial_derivative_integrable hν hθ hψ hη hC hηθ hit hx)
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
  · have he : (fun x => outputStoppedDirect eps ν ψ C t i x + B x) =
        fun x => (fluxPrefixWeighted (iidLaw ν) eps (t-1) i f x + Bp x) -
          (fluxPrefixWeighted (iidLaw ν) eps t i f x + Bn x) := by
      funext x
      dsimp [B, H]
      ring
    rw [he]
    refine ⟨fun R => (hIp R).sub (hIn R), dp-dn, ?_⟩
    filter_upwards [hdp, hdn, ae_restrict_mem measurableSet_Ioi] with x hpx hnx hx
    unfold fluxOutputPiece
    rw [output_stopped_integral_eq_partial eps ν (testFn ψ) C t i x]
    rw [flux_stop_integral_eq_sub (iidLaw ν) (F := F) (eps := eps) (i := i) (x := x)
      (by omega : 0 < t) (flux_partial_outTest_integrable hν hθ hψ hη hC hηθ hit hx.le)]
    rw [hpx, hnx, intervalIntegral.integral_sub (hIp x) (hIn x)]
    ring

end
end PGM
