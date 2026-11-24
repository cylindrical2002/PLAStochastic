import PLAStochastic.Affine.Extrema.OrderedVector
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal

/-! # Uniqueness from continuous compact tests inside the actual open extrema domain -/
noncomputable section
open MeasureTheory Set Function
open scoped ENNReal NNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Finiteness only on compact subsets of the open set suffices. The candidate measure
need not be assumed finite near the boundary, or globally finite. -/
theorem measure_eq_of_open_compact_tests {U : Set ExtremaVector} (hU : IsOpen U)
    {μ ν : Measure ExtremaVector} [IsFiniteMeasure μ]
    (hμ : μ Uᶜ = 0) (hν : ν Uᶜ = 0)
    (hνK : ∀ K : Set ExtremaVector, IsCompact K → K ⊆ U → ν K < ⊤)
    (hTest : ∀ φ : ExtremaVector → ℝ, Continuous φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ x, 0 ≤ φ x) →
      (∫⁻ x, ENNReal.ofReal (φ x) ∂μ) = ∫⁻ x, ENNReal.ofReal (φ x) ∂ν) : μ = ν := by
  let μU : Measure U := μ.comap Subtype.val
  let νU : Measure U := ν.comap Subtype.val
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have : IsFiniteMeasureOnCompacts νU := by
    constructor
    intro K hK
    change ν.comap Subtype.val K < ⊤
    rw [comap_subtype_coe_apply hU.measurableSet]
    exact hνK _ (hK.image continuous_subtype_val) (Subtype.coe_image_subset _ _)
  have hsub : μU = νU := by
    apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
    intro f
    let φ : ExtremaVector → ℝ := Subtype.val.extend (fun x : U => (f x : ℝ)) 0
    have hfr : (f.toReal : U → ℝ) = (fun x : U => (f x : ℝ)) := by
      funext x
      exact CompactlySupportedContinuousMap.toReal_apply f x
    have hcR : Continuous (fun x : U => (f x : ℝ)) := by rw [← hfr]; exact f.toReal.continuous
    have hsR : HasCompactSupport (fun x : U => (f x : ℝ)) := by rw [← hfr]; exact f.toReal.hasCompactSupport
    have hc : Continuous φ := HasCompactSupport.continuous_extend_zero hU hcR hsR
    have hs : HasCompactSupport φ := hsR.extend_zero continuous_subtype_val
    have hsupport : tsupport φ ⊆ U :=
      (hsR.tsupport_extend_zero_subset continuous_subtype_val).trans
        (Subtype.coe_image_subset _ _)
    have hpos : ∀ x, 0 ≤ φ x := by
      intro x
      by_cases hx : x ∈ U
      · have hxφ : φ x = (f ⟨x,hx⟩ : ℝ) :=
          Subtype.val_injective.extend_apply _ _ (⟨x,hx⟩ : U)
        rw [hxφ]
        exact (f ⟨x,hx⟩).coe_nonneg
      · simp only [φ,extend_apply' _ _ _ (by simpa using hx : x ∉ range (Subtype.val : U → ExtremaVector)), Pi.zero_apply, le_refl]
    have hφval (x : U) : φ x = (f x : ℝ) := by
      exact Subtype.val_injective.extend_apply _ _ x
    have hμint : (∫⁻ x : U, ENNReal.ofReal (f x : ℝ) ∂μU) =
        ∫⁻ x, ENNReal.ofReal (φ x) ∂μ := by
      simp_rw [← hφval]
      dsimp only [μU]
      rw [lintegral_subtype_comap (μ := μ) hU.measurableSet (fun x => ENNReal.ofReal (φ x)),
        Measure.restrict_eq_self_of_ae_mem hμ]
    have hνint : (∫⁻ x : U, ENNReal.ofReal (f x : ℝ) ∂νU) =
        ∫⁻ x, ENNReal.ofReal (φ x) ∂ν := by
      simp_rw [← hφval]
      dsimp only [νU]
      rw [lintegral_subtype_comap (μ := ν) hU.measurableSet (fun x => ENNReal.ofReal (φ x)),
        Measure.restrict_eq_self_of_ae_mem hν]
    have heq := hμint.trans ((hTest φ hc hs hsupport hpos).trans hνint.symm)
    simpa only [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x : U => (f x).coe_nonneg))
      hcR.aestronglyMeasurable] using congrArg ENNReal.toReal heq
  have hm := congrArg (fun ρ : Measure U => ρ.map (Subtype.val : U → ExtremaVector)) hsub
  simpa only [μU,νU,map_comap_subtype_coe hU.measurableSet,
    Measure.restrict_eq_self_of_ae_mem hμ,Measure.restrict_eq_self_of_ae_mem hν] using hm

end BrownianAffine
