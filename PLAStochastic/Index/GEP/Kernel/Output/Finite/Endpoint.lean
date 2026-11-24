import PLAStochastic.Index.GEP.Kernel.Output.Finite.OccupationBoundary

/-!
# Next-gap integration on the actual output endpoint measures

The lower and upper endpoints of the prefix section, and their active events,
do not depend on the next gap. Local CDF truncation gives all needed endpoint
moments from `RegLaw`. Thus the occupation boundary has the actual averaged
increment `kernelBoundaryReward` at each endpoint.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
set_option maxHeartbeats 800000

theorem output_endpoint_testFn_integrable {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {i t : ℕ} (hit : i < t)
    {A : Set (ℕ → ℝ)} (hA : MeasurableSet A)
    {E : (ℕ → ℝ) → ℝ} (hE : Measurable E) {R : ℝ}
    (hER : ∀ g ∈ A, E g ∈ Icc (0 : ℝ) (max 0 R)) :
    Integrable (A.indicator (fun g => testFn ψ (gapKeys (Function.update g i (E g)) t / C)))
      (iidLaw ν) := by
  have hκθ : 2 * η / C ≤ θ / 2 := by
    calc
      2 * η / C = 2 * (η / C) := by ring
      _ ≤ θ / 2 := by linarith
  have hExp := (flux_regLaw_unmarked_exp hν hθ (by positivity) hκθ t i).const_mul
    (M / η * Real.exp ((2 * η / C) * max 0 R))
  have hgs : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving
      |>.ae hν.ae_pos
  simp_rw [flux_gapKeys_update hit]
  refine hExp.mono' ((hψ.measurable_testFn.comp
    (((measurable_fluxUnmarkedSum t i).add hE).div_const C)).indicator hA).aestronglyMeasurable ?_
  filter_upwards [hgs] with g hg
  by_cases hgA : g ∈ A
  · rw [indicator_of_mem hgA]
    exact (flux_testFn_shift_bounds hψ hη hC
      (fluxUnmarkedSum_nonneg_le (fun j => (hg j).le) t i).1 (hER g hgA)).1
  · rw [indicator_of_notMem hgA, norm_zero]
    exact mul_nonneg (mul_nonneg (div_nonneg hψ.nonneg' hη.le) (Real.exp_pos _).le)
      (Real.exp_pos _).le

/-- Fubini after imposing an event and an inserted endpoint which both ignore
the next gap. The hypotheses are verified below for the original PLA endpoints. -/
theorem output_endpoint_increment_eq_reward (ν : ProbabilityMeasure ℝ)
    {F : ℝ → ℝ} (hF : Measurable F) {i k : ℕ} (hik : i ≠ k)
    {A : Set (ℕ → ℝ)} (hA : MeasurableSet A)
    {E : (ℕ → ℝ) → ℝ} (hE : Measurable E)
    (hAu : ∀ g y, Function.update g k y ∈ A ↔ g ∈ A)
    (hEu : ∀ g y, E (Function.update g k y) = E g)
    (h1 : Integrable (A.indicator (fun g => F (gapKeys (Function.update g i (E g)) (k+1))))
      (iidLaw ν))
    (h0 : Integrable (A.indicator (fun g => F (gapKeys (Function.update g i (E g)) k)))
      (iidLaw ν)) :
    (∫ g in A, F (gapKeys (Function.update g i (E g)) (k+1)) ∂iidLaw ν) -
        (∫ g in A, F (gapKeys (Function.update g i (E g)) k) ∂iidLaw ν) =
      ∫ g in A, incFn F ν (gapKeys (Function.update g i (E g)) k) ∂iidLaw ν := by
  classical
  let H : (ℕ → ℝ) → ℝ := A.indicator (fun g =>
    F (gapKeys (Function.update g i (E g)) (k+1)) -
    F (gapKeys (Function.update g i (E g)) k))
  have hU : Measurable (fun g => Function.update g i (E g)) :=
    (measurable_update_pair i).comp (hE.prodMk measurable_id)
  have hHm : Measurable H := ((hF.comp
    (((measurable_pi_apply (k+1)).comp measurable_gapKeys).comp hU)).sub
    (hF.comp (((measurable_pi_apply k).comp measurable_gapKeys).comp hU))).indicator hA
  have hHI : Integrable H (iidLaw ν) := by
    refine (h1.sub h0).congr ?_
    exact Eventually.of_forall fun g => by simp only [H, Pi.sub_apply, indicator_sub]
  have hdiff :
      (∫ g in A, F (gapKeys (Function.update g i (E g)) (k+1)) ∂iidLaw ν) -
          (∫ g in A, F (gapKeys (Function.update g i (E g)) k) ∂iidLaw ν) =
        ∫ g, H g ∂iidLaw ν := by
    rw [← integral_indicator hA, ← integral_indicator hA, ← integral_sub h1 h0]
    apply integral_congr_ae
    exact Eventually.of_forall fun g => by simp only [H, indicator_sub]
  rw [hdiff]
  have hins := integral_piLaw_insert (fun _ => ν) k hHm hHI
  change (∫ g, H g ∂iidLaw ν) =
    ∫ g, ∫ y, H (Function.update g k y) ∂(ν : Measure ℝ) ∂iidLaw ν at hins
  rw [hins, ← integral_indicator hA]
  apply integral_congr_ae
  refine Eventually.of_forall fun g => ?_
  have hcomm (y : ℝ) : Function.update (Function.update g k y) i (E g) =
      Function.update (Function.update g i (E g)) k y := by
    funext m
    by_cases hmi : m = i <;> by_cases hmk : m = k <;> simp_all
  by_cases hgA : g ∈ A
  · have hgu : ∀ y, Function.update g k y ∈ A := fun y => (hAu g y).2 hgA
    simp only [H, indicator_of_mem (hgu _), indicator_of_mem hgA, hEu, hcomm,
      gapKeys_update_succ, gapKeys_update_self]
    rfl
  · have hgu : ∀ y, Function.update g k y ∉ A := fun y hy => hgA ((hAu g y).1 hy)
    simp only [H, indicator_of_notMem (hgu _), indicator_of_notMem hgA, integral_zero]

theorem output_endpoint_outTest_eq_reward {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {i k : ℕ} (hik : i < k)
    {A : Set (ℕ → ℝ)} (hA : MeasurableSet A)
    {E : (ℕ → ℝ) → ℝ} (hE : Measurable E) {R : ℝ}
    (hER : ∀ g ∈ A, E g ∈ Icc (0 : ℝ) (max 0 R))
    (hAu : ∀ g y, Function.update g k y ∈ A ↔ g ∈ A)
    (hEu : ∀ g y, E (Function.update g k y) = E g) :
    (∫ g in A, testFn ψ (gapKeys (Function.update g i (E g)) (k+1)/C) ∂iidLaw ν) -
        (∫ g in A, testFn ψ (gapKeys (Function.update g i (E g)) k/C) ∂iidLaw ν) =
      ∫ g in A, kernelBoundaryReward ν C ψ (gapKeys (Function.update g i (E g)) k)
        ∂iidLaw ν :=
  output_endpoint_increment_eq_reward ν
    (hψ.measurable_testFn.comp (measurable_id.div_const C)) hik.ne hA hE hAu hEu
    (output_endpoint_testFn_integrable hν hθ hψ hη hC hηθ (by omega) hA hE hER)
    (output_endpoint_testFn_integrable hν hθ hψ hη hC hηθ hik hA hE hER)

/-- Endpoint CDFs only need locally bounded endpoint rewards. In particular, no
global moment of the random endpoint is required. -/
theorem output_endpoint_cdf_eq_reward {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {i k : ℕ} (hik : i < k)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    {E : (ℕ → ℝ) → ℝ} (hE : Measurable E)
    (hE0 : ∀ g ∈ S, 0 ≤ E g)
    (hSu : ∀ g y, Function.update g k y ∈ S ↔ g ∈ S)
    (hEu : ∀ g y, E (Function.update g k y) = E g) (x : ℝ) :
    (∫ g in {g | E g ≤ x}, testFn ψ (gapKeys (Function.update g i (E g)) (k+1)/C)
        ∂(iidLaw ν).restrict S) -
        (∫ g in {g | E g ≤ x}, testFn ψ (gapKeys (Function.update g i (E g)) k/C)
          ∂(iidLaw ν).restrict S) =
      ∫ g in {g | E g ≤ x}, kernelBoundaryReward ν C ψ
        (gapKeys (Function.update g i (E g)) k) ∂(iidLaw ν).restrict S := by
  have hcut : MeasurableSet {g | E g ≤ x} := measurableSet_le hE measurable_const
  simp only [Measure.restrict_restrict hcut]
  apply output_endpoint_outTest_eq_reward hν hθ hψ hη hC hηθ hik (hcut.inter hS) hE
    (R := x)
  · intro g hg
    exact ⟨hE0 g hg.2, hg.1.trans (le_max_right _ _)⟩
  · intro g y
    simp only [mem_inter_iff, mem_ofPred_eq, hEu, hSu]
  · exact hEu

theorem output_prefix_rhs_update_next (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k)
    (g : ℕ → ℝ) (y : ℝ) :
    fluxPrefixRHS eps k i q (Function.update g k y) = fluxPrefixRHS eps k i q g := by
  unfold fluxPrefixRHS
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (by
    have := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    omega : j ≠ k)]

/-- The actual occupation endpoint CDF carries `Δφ_C`, the next-gap averaged
output increment, at the original lower and upper endpoints. -/
theorem output_occupation_boundary_eq_reward {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (eps : ℝ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {i k : ℕ} (hik : i < k) (x : ℝ) :
    outputOccupationBoundaryCDF eps ν ψ C k i x =
      outputPrefixBoundaryCDF (iidLaw ν) eps k i
        (fun g z => kernelBoundaryReward ν C ψ (gapKeys (Function.update g i z) k)) x := by
  classical
  let c : FluxFacetIndex k → ℝ := fun q => fluxFacetCoef eps q i
  let d := fluxPrefixRHS eps k i
  have hd : ∀ q, Measurable (d q) := fun q => measurable_fluxPrefixRHS eps k i q
  have hdu : ∀ q g y, d q (Function.update g k y) = d q g :=
    output_prefix_rhs_update_next eps k i
  have hLu : ∀ g y, fluxPolyLower c d (Function.update g k y) = fluxPolyLower c d g := by
    intro g y
    simp only [fluxPolyLower, hdu]
  have hZu : ∀ g y, Function.update g k y ∈ fluxPolyZeroOK c d ↔ g ∈ fluxPolyZeroOK c d := by
    intro g y
    simp only [fluxPolyZeroOK, mem_ofPred_eq, hdu]
  unfold outputOccupationBoundaryCDF outputPrefixBoundaryCDF
  change outputPolyBoundaryCDF (iidLaw ν) c d _ x -
    outputPolyBoundaryCDF (iidLaw ν) c d _ x = outputPolyBoundaryCDF (iidLaw ν) c d _ x
  by_cases hp : (fluxPos c).Nonempty
  · have hUu : ∀ g y, fluxPolyUpper c d hp (Function.update g k y) = fluxPolyUpper c d hp g := by
      intro g y
      simp only [fluxPolyUpper, hdu]
    have hAu : ∀ g y, Function.update g k y ∈ fluxPolyActive c d hp ↔ g ∈ fluxPolyActive c d hp := by
      intro g y
      simp only [fluxPolyActive, mem_inter_iff, mem_ofPred_eq, hZu, hLu, hUu]
    have hL := output_endpoint_cdf_eq_reward hν hθ hψ hη hC hηθ hik
      (measurableSet_fluxPolyActive c hd hp) (measurable_fluxPolyLower c hd)
      (fun g _ => fluxPolyLower_nonneg c d g) hAu hLu x
    have hU := output_endpoint_cdf_eq_reward hν hθ hψ hη hC hηθ hik
      (measurableSet_fluxPolyActive c hd hp) (measurable_fluxPolyUpper c hd hp)
      (fun g hg => (fluxPolyLower_nonneg c d g).trans hg.2) hAu hUu x
    simp only [outputPolyBoundaryCDF, dif_pos hp]
    linear_combination hL - hU
  · simp only [outputPolyBoundaryCDF, dif_neg hp]
    exact output_endpoint_cdf_eq_reward hν hθ hψ hη hC hηθ hik
      (measurableSet_fluxPolyZeroOK c hd) (measurable_fluxPolyLower c hd)
      (fun g _ => fluxPolyLower_nonneg c d g) hZu hLu x

end
end PGM
