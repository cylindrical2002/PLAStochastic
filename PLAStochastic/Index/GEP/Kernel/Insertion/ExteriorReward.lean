import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.OutputRewardBound
import PLAStochastic.Index.GEP.Kernel.Insertion.Coefficient

/-! # A pointwise exterior reward for the near-slope coefficient

The original output test is controlled only at nonnegative physical sums.
Zero extension below zero gives a pointwise coefficient envelope and agrees
with the original reward almost everywhere on the actual positive path law.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
set_option maxHeartbeats 1000000

def kernelPositiveBoundaryReward (ν : ProbabilityMeasure ℝ) (C : ℝ)
    (ψ : ℝ → ℝ) : ℝ → ℝ := (Ici 0).indicator (kernelBoundaryReward ν C ψ)

theorem measurable_kernelPositiveBoundaryReward {η M : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (ν : ProbabilityMeasure ℝ) (C : ℝ) :
    Measurable (kernelPositiveBoundaryReward ν C ψ) :=
  (measurable_kernelBoundaryReward hψ ν C).indicator measurableSet_Ici

theorem measurable_kernelIFPhysicalSum_joint {k : ℕ} (q : FluxFacetIndex k) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => kernelIFPhysicalSum p.1 q p.2) := by
  unfold kernelIFPhysicalSum gapKeys
  fun_prop

theorem kernel_positive_reward_physical_ae {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (C : ℝ) (ψ : ℝ → ℝ) {a : ℝ} (ha : 0 < a)
    {k : ℕ} {q : FluxFacetIndex k} (hq : fluxFacetValid q) :
    (fun g => kernelPositiveBoundaryReward ν C ψ (kernelIFPhysicalSum a q g)) =ᵐ[iidLaw ν]
      (fun g => kernelBoundaryReward ν C ψ (kernelIFPhysicalSum a q g)) := by
  have hg : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving.ae hν.ae_pos
  filter_upwards [hg] with g hg
  exact indicator_of_mem (kernel_IF_physical_sum_nonneg ha hq (fun j _ => (hg j).le)) _

theorem kernel_positive_reward_le_time {D θ vlo vhi η M C a eps : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η / C ≤ θ / 4) (ha : 0 < a) {k : ℕ} (q : FluxFacetIndex k)
    {g : ℕ → ℝ} (hout : kernelIFOuterSurvival eps a q g ≠ 0) :
    |kernelPositiveBoundaryReward ν C ψ (kernelIFPhysicalSum a q g)| ≤
      M * (8*D/θ^2) / C * Real.exp (η * ((k : ℝ)+2*eps)/(a*C)) := by
  have hM := hψ.nonneg
  have hD := hν.D_nonneg
  by_cases hs : 0 ≤ kernelIFPhysicalSum a q g
  · rw [kernelPositiveBoundaryReward, indicator_of_mem (show kernelIFPhysicalSum a q g ∈ Ici (0 : ℝ) from hs)]
    have hl : krAlive (Icc 0 (2*eps)) (-1) (-a) q.1 (eps-fluxFacetSign q*eps)
        (kernelReversePrefix g q.1) = 1 := by
      rcases kernel_krAlive_zero_or_one (Icc 0 (2*eps)) (-1) (-a)
        (eps-fluxFacetSign q*eps) (kernelReversePrefix g q.1) q.1 with hz | ho
      · exact False.elim (hout (by simp only [kernelIFOuterSurvival, hz, zero_mul]))
      · exact ho
    have hr : krAlive (Icc 0 (2*eps)) 1 a (k-q.2.2.1) (eps-fluxFacetSign q*eps)
        (fun j => g (j+q.2.2.1)) = 1 := by
      rcases kernel_krAlive_zero_or_one (Icc 0 (2*eps)) 1 a
        (eps-fluxFacetSign q*eps) (fun j => g (j+q.2.2.1)) (k-q.2.2.1) with hz | ho
      · exact False.elim (hout (by simp only [kernelIFOuterSurvival, hz, mul_zero]))
      · exact ho
    have hleft := (kernel_krAlive_eq_one_iff _ _ _ _ _ _).mp hl _ le_rfl
    have hright := (kernel_krAlive_eq_one_iff _ _ _ _ _ _).mp hr _ le_rfl
    exact kernelBoundaryReward_le_of_residual hν hθ hψ hη hC hscale hs ha hleft.2 hright.1
      (kernel_IF_physical_sum_residual ha.ne' (eps-fluxFacetSign q*eps) q g)
  · rw [kernelPositiveBoundaryReward, indicator_of_notMem (show kernelIFPhysicalSum a q g ∉ Ici (0 : ℝ) from hs), abs_zero]
    positivity

/-- The exponent in the actual output reward fits the coefficient time weight
with a class-scale choice, before any input tail exponent is selected. -/
theorem kernel_near_reward_exponent {η C a w ε : ℝ} (_hη : 0 ≤ η) (_hC : 0 < C)
    (ha : 1/2 ≤ a) (hw : 1 ≤ w) (hε : 0 ≤ ε)
    (hscale : η/C ≤ ε/(2*w^2)) (k : ℕ) :
    η*((k : ℝ)+w)/(a*C) ≤ ε + ε*(k : ℝ)/w^2 := by
  have hw0 : 0 < w := by linarith
  have ha0 : 0 < a := by linarith
  have hc : η/C/a ≤ ε/w^2 := by
    apply (div_le_iff₀ ha0).mpr
    have hh : ε/(2*w^2) ≤ ε/w^2*a := by
      have he := mul_le_mul_of_nonneg_left ha (show 0 ≤ ε/w^2 by positivity)
      calc
        ε/(2*w^2) = ε/w^2*(1/2) := by ring
        _ ≤ ε/w^2*a := he
    exact hscale.trans hh
  have ht := mul_le_mul_of_nonneg_right hc (show 0 ≤ (k : ℝ)+w by positivity)
  have hww : ε/w ≤ ε := div_le_self hε hw
  have heq : ε/w^2*((k : ℝ)+w) = ε*(k : ℝ)/w^2+ε/w := by field_simp
  calc
    _ = η/C/a*((k : ℝ)+w) := by ring
    _ ≤ ε/w^2*((k : ℝ)+w) := ht
    _ = ε*(k : ℝ)/w^2+ε/w := heq
    _ ≤ _ := by linarith

theorem kernel_positive_reward_near_bound {D θ vlo vhi η M C a w ε : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) (ha : 1/2 ≤ a) (hw : 1 ≤ w) (hε : 0 ≤ ε)
    (hnear : η/C ≤ ε/(2*w^2)) {k : ℕ} (q : FluxFacetIndex k) {g : ℕ → ℝ}
    (hout : kernelIFOuterSurvival (w/2) a q g ≠ 0) :
    |kernelPositiveBoundaryReward ν C ψ (kernelIFPhysicalSum a q g)| ≤
      (M*(8*D/θ^2)/C*Real.exp ε)*Real.exp (ε*(k : ℝ)/w^2) := by
  have hh := kernel_positive_reward_le_time hν hθ hψ hη hC hscale
    (show 0 < a by linarith) q hout
  have hw' : 2*(w/2)=w := by ring
  rw [hw'] at hh
  have hM := hψ.nonneg
  have hD := hν.D_nonneg
  exact hh.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (kernel_near_reward_exponent hη hC ha hw hε hnear k)) (by positivity)).trans_eq
      (by rw [Real.exp_add]; ring))

end
end PGM
