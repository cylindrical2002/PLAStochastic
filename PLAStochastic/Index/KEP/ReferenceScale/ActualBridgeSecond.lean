import PLAStochastic.Index.KEP.ReferenceScale.ActualBridgeWard
import PLAStochastic.Index.KEP.ReferenceScale.BridgeSecondWard

/-!
# Second Ward identities on the actual reference orbit

The reference Gamma density supplies all classical derivative inputs. The
physical first derivative is the logarithmic-slope derivative divided by slope;
its derivative has the original second spatial derivative and explicit pin
flux derivatives. No layer-uniform bound is asserted by these identities.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem hasDerivAt_kepLogBridgeSlope_second_ward {f f' f'' : ℝ → ℝ}
    (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hd : ∀ t, HasDerivAt f (f' t) t) (hdd : ∀ t, HasDerivAt f' (f'' t) t)
    {σ w : ℝ} (hσ : σ ^ 2 = 1) (hw : 0 ≤ w) (s : ℝ) (n : ℕ) (x y : ℝ) :
    let p := kepLogStep f σ
    let p' := kepLogStepFirst f' σ
    let p'' := kepLogStepSecond f'' σ
    let q := kepLogStepSlope f f' σ
    let c := (n + 1 : ℕ) * σ + x - y
    HasDerivAt (fun v => kepFixedBridgeSlope p q w v n x y)
      (kepFixedBridge p w s n x y - 3 * c * kepFixedBridgeRight p p' w s n x y +
        c ^ 2 * kepFixedBridgeRight p p'' w s n x y +
        kepBridgeTransportFlux p w σ s n x y - c * kepBridgeFluxRight p p' w σ s n x y -
        kepBridgeFluxSlope p q w σ s n x y) s := by
  dsimp only
  exact hasDerivAt_kepFixedBridgeSlope_second_ward
    (continuous_kepLogStep hf σ) (continuous_kepLogStepFirst hf' σ)
    (continuous_kepLogStepSecond hf'' σ) (continuous_kepLogStepSlope hf hf' σ)
    (continuous_kepLogStepMixed hf' hf'' σ)
    (hasDerivAt_kepLogStep_right hd σ) (hasDerivAt_kepLogStepFirst_right hdd σ)
    (hasDerivAt_kepLogStep_slope hd σ) (hasDerivAt_kepLogStepFirst_slope hdd hσ)
    (hasDerivAt_kepLogStepSlope_right hd hdd hσ) (kepLogStepSlope_eq hσ) hw s n x y

theorem hasDerivAt_kepPhysicalBridgeSlope_second_ward {f f' f'' : ℝ → ℝ}
    (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hd : ∀ t, HasDerivAt f (f' t) t) (hdd : ∀ t, HasDerivAt f' (f'' t) t)
    {σ w a : ℝ} (hσ : σ ^ 2 = 1) (hw : 0 ≤ w) (ha : 0 < a)
    (n : ℕ) (x y : ℝ) :
    let p := kepLogStep f σ
    let p' := kepLogStepFirst f' σ
    let p'' := kepLogStepSecond f'' σ
    let q := kepLogStepSlope f f' σ
    let c := (n + 1 : ℕ) * σ + x - y
    let s := Real.log a
    HasDerivAt (fun b => kepFixedBridgeSlope p q w (Real.log b) n x y / b)
      ((2 * kepFixedBridge p w s n x y - 4 * c * kepFixedBridgeRight p p' w s n x y +
        c ^ 2 * kepFixedBridgeRight p p'' w s n x y +
        2 * kepBridgeTransportFlux p w σ s n x y - c * kepBridgeFluxRight p p' w σ s n x y -
        kepBridgeFluxSlope p q w σ s n x y) / a ^ 2) a := by
  have hh := ((hasDerivAt_kepLogBridgeSlope_second_ward hf hf' hf'' hd hdd hσ hw
    (Real.log a) n x y).comp a (Real.hasDerivAt_log ha.ne')).div (hasDerivAt_id a) ha.ne'
  dsimp only
  convert hh using 1 <;> first | rfl |
    (dsimp only [Function.comp_apply, id_eq]
     rw [kepFixedBridge_transport (continuous_kepLogStep hf σ)
      (continuous_kepLogStepFirst hf' σ) (hasDerivAt_kepLogStep_right hd σ)
      (kepLogStepSlope_eq hσ) hw]; field_simp [ha.ne']; ring)

/-- All analytic inputs are discharged on the unchanged actual reference law. -/
theorem kepReference_physicalBridgeSlope_second_ward {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {σ w a : ℝ} (hσ : σ = 1 ∨ σ = -1) (hw : 0 ≤ w) (ha : 0 < a)
    (n : ℕ) (x y : ℝ) :
    let f := (kepReferenceDensity heps hj).density
    let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    let p := kepLogStep f σ
    let p' := kepLogStepFirst f' σ
    let p'' := kepLogStepSecond f'' σ
    let q := kepLogStepSlope f f' σ
    let c := (n + 1 : ℕ) * σ + x - y
    let s := Real.log a
    HasDerivAt (fun b => kepFixedBridgeSlope p q w (Real.log b) n x y / b)
      ((2 * kepFixedBridge p w s n x y - 4 * c * kepFixedBridgeRight p p' w s n x y +
        c ^ 2 * kepFixedBridgeRight p p'' w s n x y +
        2 * kepBridgeTransportFlux p w σ s n x y - c * kepBridgeFluxRight p p' w σ s n x y -
        kepBridgeFluxSlope p q w σ s n x y) / a ^ 2) a := by
  have hc := kepReferenceDensity_classical heps hj
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  exact hasDerivAt_kepPhysicalBridgeSlope_second_ward
    (continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt)
    hc.2.2.2.1 hc.2.1 hc.2.2.1 hσ2 hw ha n x y

/-- A second derivative of the actual pointwise `krDens`, including the
boundary endpoints; every input is discharged by the actual reference law. -/
theorem kepReference_krDens_second_slope_ward {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {σ w a : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : 0 < a) (n : ℕ)
    {x y : ℝ} (hx : x ∈ Icc 0 w) (hy : y ∈ Icc 0 w) :
    let ν := kepReferenceLaw eps j
    let f := (kepReferenceDensity heps hj).density
    let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    let p := kepLogStep f σ
    let p' := kepLogStepFirst f' σ
    let p'' := kepLogStepSecond f'' σ
    let q := kepLogStepSlope f f' σ
    let c := (n + 1 : ℕ) * σ + x - y
    let s := Real.log a
    HasDerivAt (deriv (fun b => krDens (Icc 0 w) ν f σ (σ * b) (n + 1) x y))
      ((2 * kepFixedBridge p w s n x y - 4 * c * kepFixedBridgeRight p p' w s n x y +
        c ^ 2 * kepFixedBridgeRight p p'' w s n x y +
        2 * kepBridgeTransportFlux p w σ s n x y - c * kepBridgeFluxRight p p' w σ s n x y -
        kepBridgeFluxSlope p q w σ s n x y) / a ^ 2) a := by
  have hc := kepReferenceDensity_classical heps hj
  have hν : (kepReferenceLaw eps j : Measure ℝ) = volume.withDensity
      (fun t => ENNReal.ofReal ((kepReferenceDensity heps hj).density t)) := by
    rw [← kepReferenceDensity_toMeasure heps hj]
    rfl
  apply (kepReference_physicalBridgeSlope_second_ward heps hj hσ (hx.1.trans hx.2)
    ha n x y).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with b hb
  exact deriv_krDens_slope_eq_logBridge (kepReferenceLaw eps j)
    (continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt)
    hc.2.1 (kepReferenceDensity heps hj).nonneg (kepReferenceDensity_le_span heps hj)
    hν hσ hb n hx hy

end

end PGM
