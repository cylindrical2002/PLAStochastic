import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.Prefix
import PLAStochastic.Index.GEP.Kernel.Output.Finite.TestPrimitive
import PLAStochastic.Index.GEP.PointwiseSmall.DirectionKernels

/-!
# Actual output tests on finite inserted PLA prefixes

The moving-weight section theorem is applied to the original `OutTest` primitive.
Its analytic hypotheses follow from the ordinary exponential moment of the
unmarked partial sum, and hence from `RegLaw` for every finite prefix.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

theorem flux_testFn_shift_bounds {η M C s x R : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C) (hs : 0 ≤ s)
    (hx : x ∈ Icc (0 : ℝ) (max 0 R)) :
    ‖testFn ψ ((s + x) / C)‖ ≤
        (M / η * Real.exp ((2 * η / C) * max 0 R)) * Real.exp ((2 * η / C) * s) ∧
      ‖ψ ((s + x) / C) / C‖ ≤
        (M / C * Real.exp ((2 * η / C) * max 0 R)) * Real.exp ((2 * η / C) * s) := by
  have hM := hψ.nonneg'
  have hd : 0 ≤ 2 * η / C := by positivity
  have hy : 0 ≤ s + x := add_nonneg hs hx.1
  have he : Real.exp (2 * η * (s + x) / C) ≤
      Real.exp ((2 * η / C) * max 0 R) * Real.exp ((2 * η / C) * s) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      2 * η * (s + x) / C = (2 * η / C) * x + (2 * η / C) * s := by ring
      _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hx.2 hd]
  constructor
  · rw [Real.norm_eq_abs]
    calc
      _ ≤ M / η * Real.exp (2 * η * (s + x) / C) := pw_testFn_div_le hψ hη hC hy
      _ ≤ _ := by simpa [mul_assoc] using mul_le_mul_of_nonneg_left he (div_nonneg hM hη.le)
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hC]
    calc
      _ ≤ (M * Real.exp (η * ((s + x) / C))) / C :=
        div_le_div_of_nonneg_right (hψ.2 _ (div_nonneg hy hC.le)) hC.le
      _ ≤ (M * Real.exp (2 * η * (s + x) / C)) / C := by
        gcongr
        have heq : 2 * η * (s + x) / C = 2 * (η * ((s + x) / C)) := by ring
        rw [heq]
        linarith [mul_nonneg hη.le (div_nonneg hy hC.le)]
      _ = M / C * Real.exp (2 * η * (s + x) / C) := by ring
      _ ≤ _ := by simpa [mul_assoc] using mul_le_mul_of_nonneg_left he (div_nonneg hM hC.le)

/-- The actual test primitive has the finite-prefix interior-plus-boundary
identity, with all analytic assumptions reduced to a usual path moment. -/
theorem flux_prefix_outTest_aePrimitive {ν : ProbabilityMeasure ℝ}
    (hac : (ν : Measure ℝ) ≪ volume) (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    (P : Measure (ℕ → ℝ)) [IsFiniteMeasure P] (hP : P ≪ iidLaw ν)
    (eps : ℝ) {k i : ℕ} (hk : 2 ≤ k) (hi : i < k)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    {S : (ℕ → ℝ) → ℝ} (hS : Measurable S) (hS0 : ∀ᵐ g ∂P, 0 ≤ S g)
    (hExp : Integrable (fun g => Real.exp ((2 * η / C) * S g)) P) :
    ∃ B : ℝ → ℝ,
      AEPrimitive
        (fluxPrefixWeighted P eps k i (fun g x => testFn ψ ((S g + x) / C)))
        (fun x => fluxPrefixWeighted P eps k i (fun g x => ψ ((S g + x) / C) / C) x + B x) := by
  apply flux_prefix_moving_weight_aePrimitive hac hpos P hP eps hk hi
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

/-- The partial sum excluding the marked insertion coordinate. -/
def fluxUnmarkedSum (t i : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ j ∈ (Finset.range t).erase i, g j

theorem measurable_fluxUnmarkedSum (t i : ℕ) : Measurable (fluxUnmarkedSum t i) := by
  unfold fluxUnmarkedSum
  fun_prop

theorem flux_gapKeys_update {g : ℕ → ℝ} {i t : ℕ} (hit : i < t) (x : ℝ) :
    gapKeys (Function.update g i x) t = fluxUnmarkedSum t i g + x := by
  rw [gapKeys, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hit), Function.update_self]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _

theorem fluxUnmarkedSum_nonneg_le {g : ℕ → ℝ} (hg : ∀ j, 0 ≤ g j) (t i : ℕ) :
    0 ≤ fluxUnmarkedSum t i g ∧ fluxUnmarkedSum t i g ≤ gapKeys g t := by
  constructor
  · exact Finset.sum_nonneg fun j _ => hg j
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i (Finset.range t))
      (fun j _ _ => hg j)

/-- Every finite unmarked sum has the exponential moment required by the
weighted output section under the original regular-law hypotheses. -/
theorem flux_regLaw_unmarked_exp {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) {κ : ℝ} (hκ : 0 ≤ κ) (hκθ : κ ≤ θ / 2)
    (t i : ℕ) : Integrable (fun g => Real.exp (κ * fluxUnmarkedSum t i g)) (iidLaw ν) := by
  have hgs : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving
      |>.ae hν.ae_pos
  refine (integrable_exp_gapKeys (hν.expMom hθ).integrable t).mono'
    (((measurable_fluxUnmarkedSum t i).const_mul κ).exp.aestronglyMeasurable) ?_
  filter_upwards [hgs] with g hg
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  obtain ⟨hS0, hSK⟩ := fluxUnmarkedSum_nonneg_le (fun j => (hg j).le) t i
  exact (mul_le_mul_of_nonneg_left hSK hκ).trans
    (mul_le_mul_of_nonneg_right hκθ (hS0.trans hSK))

/-- Under `RegLaw`, the finite-prefix reward is the actual output test at the
actual inserted partial sum. No section, density or integrability assumptions
are added to the model. A restriction of the iid path law is also allowed. -/
theorem flux_prefix_output_partial_aePrimitive {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    (P : Measure (ℕ → ℝ)) [IsFiniteMeasure P] (hP : P ≤ iidLaw ν)
    (eps : ℝ) {k i t : ℕ} (hk : 2 ≤ k) (hi : i < k) (hit : i < t)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) :
    ∃ B : ℝ → ℝ,
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
  obtain ⟨B, hB⟩ := flux_prefix_outTest_aePrimitive hac hν.ae_pos P hP.absolutelyContinuous
    eps hk hi hψ hη hC (measurable_fluxUnmarkedSum t i) hS0
    ((flux_regLaw_unmarked_exp hν hθ (by positivity) hκθ t i).mono_measure hP)
  refine ⟨B, ?_⟩
  simpa only [flux_gapKeys_update hit] using hB

end

end PGM
