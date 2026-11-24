import PLAStochastic.Index.GEP.Kernel.Influence.Signed.CoareaIntegral
import PLAStochastic.Index.GEP.Kernel.Influence.Signed.SlopeMass

/-! # Actual signed coarea on an arbitrary measurable slope region -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1400000

theorem measurable_kernelIFOuterSurvival_joint (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => kernelIFOuterSurvival eps p.1 q p.2) := by
  unfold kernelIFOuterSurvival
  apply Measurable.mul
  · apply measurable_krAlive_param measurableSet_Icc measurable_const measurable_fst.neg measurable_const
    unfold kernelReversePrefix
    fun_prop
  · apply measurable_krAlive_param measurableSet_Icc measurable_const measurable_fst measurable_const
    fun_prop

def kernelIFLeftSignedPinFactor (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps x : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (a : ℝ) : ℝ :=
  kernelFacetQ eps q *
    (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x (i-q.1) (q.2.1-i-1)
      (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps) *
    krDens (Icc 0 (2*eps)) ν f 1 a (q.2.2.1-q.2.1)
      (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps))

def kernelIFRightSignedPinFactor (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps x : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (a : ℝ) : ℝ :=
  kernelFacetP eps q *
    (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.1-q.1)
      (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps) *
    kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x (i-q.2.1) (q.2.2.1-i-1)
      (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps))

theorem kernel_IF_left_total_densityOn_factor (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ u, 0 ≤ f u) (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k) (i : ℕ)
    (hQ : 0 ≤ kernelFacetQ eps q) (H : ℝ → ℝ≥0∞) (x : ℝ) :
    kernelIFLeftTotalPinDensityOn ν f eps S q i H x =
      ∫⁻ a in S, ENNReal.ofReal (kernelIFLeftSignedPinFactor ν f eps x q i a) *
        (∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * H (kernelIFPhysicalSum a q g) ∂iidLaw ν)
          ∂volume.restrict (Ioi (0 : ℝ)) := by
  apply lintegral_congr
  intro a
  simp only [kernelIFLeftSignedPinFactor, ENNReal.ofReal_mul hQ,
    ENNReal.ofReal_mul (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _)]
  ac_rfl

theorem kernel_IF_right_total_densityOn_factor (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ u, 0 ≤ f u) (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k) (i : ℕ)
    (hP : 0 ≤ kernelFacetP eps q) (H : ℝ → ℝ≥0∞) (x : ℝ) :
    kernelIFRightTotalPinDensityOn ν f eps S q i H x =
      ∫⁻ a in S, ENNReal.ofReal (kernelIFRightSignedPinFactor ν f eps x q i a) *
        (∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * H (kernelIFPhysicalSum a q g) ∂iidLaw ν)
          ∂volume.restrict (Ioi (0 : ℝ)) := by
  apply lintegral_congr
  intro a
  simp only [kernelIFRightSignedPinFactor, ENNReal.ofReal_mul hP,
    ENNReal.ofReal_mul (krDens_nonneg ν hf0 _ _ _)]
  ac_rfl

theorem kernel_IF_left_signed_densityOn_integral (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k) (i : ℕ)
    (hQ : 0 ≤ kernelFacetQ eps q) {H : ℝ → ℝ} (hH : Measurable H) (x : ℝ)
    (hfin : kernelIFLeftTotalPinDensityOn ν f eps S q i (fun s => ENNReal.ofReal |H s|) x ≠ ∞) :
    IntegrableOn (fun a => kernelIFLeftSignedPinFactor ν f eps x q i a *
      ∫ g, kernelIFOuterSurvival eps a q g * H (kernelIFPhysicalSum a q g) ∂iidLaw ν)
        S (volume.restrict (Ioi (0 : ℝ))) ∧
    (kernelIFLeftTotalPinDensityOn ν f eps S q i (fun s => ENNReal.ofReal (H s)) x).toReal -
      (kernelIFLeftTotalPinDensityOn ν f eps S q i (fun s => ENNReal.ofReal (-H s)) x).toReal =
        ∫ a in S, kernelIFLeftSignedPinFactor ν f eps x q i a *
          ∫ g, kernelIFOuterSurvival eps a q g * H (kernelIFPhysicalSum a q g) ∂iidLaw ν
            ∂volume.restrict (Ioi (0 : ℝ)) := by
  have hc : Measurable (kernelIFLeftSignedPinFactor ν f eps x q i) := by
    unfold kernelIFLeftSignedPinFactor
    exact measurable_const.mul ((measurable_kernelMarkedFullDens_param ν measurableSet_Icc hf
      measurable_const measurable_id measurable_const measurable_const measurable_const _ _).mul
      (measurable_krDens_param ν measurableSet_Icc hf measurable_const measurable_id
        measurable_const measurable_const _))
  have hc0 (a : ℝ) : 0 ≤ kernelIFLeftSignedPinFactor ν f eps x q i a :=
    mul_nonneg hQ (mul_nonneg (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _)
      (krDens_nonneg ν hf0 _ _ _))
  have hH' : Measurable (fun p : ℝ × (ℕ → ℝ) => H (kernelIFPhysicalSum p.1 q p.2)) :=
    hH.comp (by unfold kernelIFPhysicalSum gapKeys; fun_prop)
  have hh := kernel_IF_signed_iterated_weight ((volume.restrict (Ioi (0 : ℝ))).restrict S) (iidLaw ν)
    hc hc0 (measurable_kernelIFOuterSurvival_joint eps q)
    (fun p => kernel_IF_outer_survival_nonneg eps p.1 q p.2) hH'
    (by rwa [kernel_IF_left_total_densityOn_factor ν hf0 eps S q i hQ] at hfin)
  rw [kernel_IF_left_total_densityOn_factor ν hf0 eps S q i hQ,
    kernel_IF_left_total_densityOn_factor ν hf0 eps S q i hQ]
  exact hh

theorem kernel_IF_right_signed_densityOn_integral (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k) (i : ℕ)
    (hP : 0 ≤ kernelFacetP eps q) {H : ℝ → ℝ} (hH : Measurable H) (x : ℝ)
    (hfin : kernelIFRightTotalPinDensityOn ν f eps S q i (fun s => ENNReal.ofReal |H s|) x ≠ ∞) :
    IntegrableOn (fun a => kernelIFRightSignedPinFactor ν f eps x q i a *
      ∫ g, kernelIFOuterSurvival eps a q g * H (kernelIFPhysicalSum a q g) ∂iidLaw ν)
        S (volume.restrict (Ioi (0 : ℝ))) ∧
    (kernelIFRightTotalPinDensityOn ν f eps S q i (fun s => ENNReal.ofReal (H s)) x).toReal -
      (kernelIFRightTotalPinDensityOn ν f eps S q i (fun s => ENNReal.ofReal (-H s)) x).toReal =
        ∫ a in S, kernelIFRightSignedPinFactor ν f eps x q i a *
          ∫ g, kernelIFOuterSurvival eps a q g * H (kernelIFPhysicalSum a q g) ∂iidLaw ν
            ∂volume.restrict (Ioi (0 : ℝ)) := by
  have hc : Measurable (kernelIFRightSignedPinFactor ν f eps x q i) := by
    unfold kernelIFRightSignedPinFactor
    exact measurable_const.mul ((measurable_krDens_param ν measurableSet_Icc hf
      measurable_const measurable_id measurable_const measurable_const _).mul
      (measurable_kernelMarkedFullDens_param ν measurableSet_Icc hf measurable_const measurable_id
        measurable_const measurable_const measurable_const _ _))
  have hc0 (a : ℝ) : 0 ≤ kernelIFRightSignedPinFactor ν f eps x q i a :=
    mul_nonneg hP (mul_nonneg (krDens_nonneg ν hf0 _ _ _)
      (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _))
  have hH' : Measurable (fun p : ℝ × (ℕ → ℝ) => H (kernelIFPhysicalSum p.1 q p.2)) :=
    hH.comp (by unfold kernelIFPhysicalSum gapKeys; fun_prop)
  have hh := kernel_IF_signed_iterated_weight ((volume.restrict (Ioi (0 : ℝ))).restrict S) (iidLaw ν)
    hc hc0 (measurable_kernelIFOuterSurvival_joint eps q)
    (fun p => kernel_IF_outer_survival_nonneg eps p.1 q p.2) hH'
    (by rwa [kernel_IF_right_total_densityOn_factor ν hf0 eps S q i hP] at hfin)
  rw [kernel_IF_right_total_densityOn_factor ν hf0 eps S q i hP,
    kernel_IF_right_total_densityOn_factor ν hf0 eps S q i hP]
  exact hh

end
end PGM
