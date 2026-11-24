import PLAStochastic.Swing.Gaussian.Bridge.ActualDensity

/-! Explicit change-of-measure identities for finite Gaussian bridge prefixes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- A measurable bridge-prefix event and endpoint event factor exactly under the
    finite Gaussian bridge density.  This is the concrete change-of-measure
    interface used when replacing the bridge prefix by an ordinary Gaussian
    walk prefix. -/
theorem gaussianBridgePrefix_change_of_measure
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M N : ℕ}
    (hMN : M < N) {A : Set (Fin M → ℝ)} {B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ ((fun ω => (gaussianBridgeIncrementPrefix X N M ω,
      cumulativeSamples X N ω)) ⁻¹' (A ×ˢ B)) =
      ((Measure.pi (fun _ : Fin M => gaussianReal 0 1)).withDensity
        (gaussianBridgeProductDensity M ((N-M : ℕ) : ℝ≥0))) A *
        gaussianReal 0 (N : ℝ≥0) B := by
  have hmeas : Measurable (fun ω =>
      (gaussianBridgeIncrementPrefix X N M ω, cumulativeSamples X N ω)) :=
    (gaussianBridgeIncrementPrefix_measurable hX N M).prodMk
      (show Measurable (cumulativeSamples X N) by
        unfold cumulativeSamples
        fun_prop)
  have hprod : MeasurableSet (A ×ˢ B) := hA.prod hB
  rw [← Measure.map_apply hmeas hprod,
    gaussianBridgeIncrementPrefix_endpoint_density hX hi hG hMN,
    Measure.prod_apply hprod]
  have hsec (z : Fin M → ℝ) :
      gaussianReal 0 (N : ℝ≥0) (Prod.mk z ⁻¹' (A ×ˢ B)) =
        A.indicator (fun _ => gaussianReal 0 (N : ℝ≥0) B) z := by
    by_cases hz : z ∈ A
    · have hset : Prod.mk z ⁻¹' (A ×ˢ B) = B := by
        ext y
        simp [hz]
      rw [hset, Set.indicator_of_mem hz]
    · have hset : Prod.mk z ⁻¹' (A ×ˢ B) = ∅ := by
        ext y
        simp [hz]
      rw [hset, measure_empty]
      simp [Set.indicator, hz]
  simp_rw [hsec]
  rw [lintegral_indicator hA, setLIntegral_const]
  ac_rfl



/-- The marginal version of the previous identity: every measurable bridge
    prefix event is evaluated against its explicit Radon--Nikodym density. -/
theorem gaussianBridgePrefix_prefix_change_of_measure
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M N : ℕ}
    (hMN : M < N) {A : Set (Fin M → ℝ)} (hA : MeasurableSet A) :
    μ ((gaussianBridgeIncrementPrefix X N M) ⁻¹' A) =
      ((Measure.pi (fun _ : Fin M => gaussianReal 0 1)).withDensity
        (gaussianBridgeProductDensity M ((N-M : ℕ) : ℝ≥0))) A := by
  rw [← Measure.map_apply (gaussianBridgeIncrementPrefix_measurable hX N M) hA,
    gaussianBridgeIncrementPrefix_density hX hi hG hMN]

/-! Joint tests may depend on the endpoint, so retain the map-level identity
for arbitrary measurable sets rather than reducing to rectangles. -/
theorem gaussianBridgePrefix_joint_change_of_measure
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M N : ℕ}
    (hMN : M < N) {H : Set ((Fin M → ℝ) × ℝ)} (hH : MeasurableSet H) :
    μ ((fun ω => (gaussianBridgeIncrementPrefix X N M ω,
      cumulativeSamples X N ω)) ⁻¹' H) =
      (((Measure.pi (fun _ : Fin M => gaussianReal 0 1)).withDensity
        (gaussianBridgeProductDensity M ((N-M : ℕ) : ℝ≥0))).prod
        (gaussianReal 0 (N : ℝ≥0))) H := by
  rw [← Measure.map_apply
    ((gaussianBridgeIncrementPrefix_measurable hX N M).prodMk
      (show Measurable (cumulativeSamples X N) by
        unfold cumulativeSamples
        fun_prop)) hH,
    gaussianBridgeIncrementPrefix_endpoint_density hX hi hG hMN]

end SwingRepair
