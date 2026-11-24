import PLAStochastic.Index.KEP.ReferenceScale.BridgePins
import PLAStochastic.Index.KEP.ReferenceScale.GammaWeighted

/-!
# Ward differentiation of the unchanged actual killed kernel

The physical slope is positive in both orientations; the signed parameters in
`krDens` are `(sigma, sigma * a)`. The flux sum retains all internal pins at both
endpoints. Spatial derivatives are those of the smooth fixed-endpoint extension.
The actual density representative has the same slope derivative even when an
endpoint is on the boundary, since the endpoint indicators do not depend on slope.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

def kepActualBridgeLogFlux (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w σ a : ℝ) (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ l ∈ Finset.range n,
    ((w - x - (l + 1 : ℕ) * σ) *
        krDens (Icc 0 w) ν f σ (σ * a) (l + 1) x w *
        krDens (Icc 0 w) ν f σ (σ * a) (n - l) w y -
      (-x - (l + 1 : ℕ) * σ) *
        krDens (Icc 0 w) ν f σ (σ * a) (l + 1) x 0 *
        krDens (Icc 0 w) ν f σ (σ * a) (n - l) 0 y)

theorem kepLogBridge_eq_krDens (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {D w σ : ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t) (hfD : ∀ t, f t ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)))
    (hσ : σ = 1 ∨ σ = -1) (s : ℝ) (n : ℕ)
    {x y : ℝ} (hx : x ∈ Icc 0 w) (hy : y ∈ Icc 0 w) :
    kepFixedBridge (kepLogStep f σ) w s n x y =
      krDens (Icc 0 w) ν f σ (σ * Real.exp s) (n + 1) x y := by
  have hs : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  rw [kepFixedBridge_congr_at (q := fun _ => kepStepSpatial f σ (σ * Real.exp s))
    (t := 0) (fun z => kepLogStep_eq_kepStepSpatial hσ s z)]
  exact kepFixedBridge_eq_krDens ν hf hf0 hfD hν (mul_ne_zero hs (Real.exp_ne_zero s)) n hx hy

theorem kepBridgeTransportFlux_eq_actual (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {D w σ : ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t) (hfD : ∀ t, f t ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)))
    (hσ : σ = 1 ∨ σ = -1) (s : ℝ) (n : ℕ)
    {x y : ℝ} (hx : x ∈ Icc 0 w) (hy : y ∈ Icc 0 w) :
    kepBridgeTransportFlux (kepLogStep f σ) w σ s n x y =
      kepActualBridgeLogFlux ν f w σ (Real.exp s) n x y := by
  rw [kepBridgeTransportFlux_eq_sum (continuous_kepLogStep hf σ)]
  unfold kepActualBridgeLogFlux
  apply Finset.sum_congr rfl
  intro l hl
  have hw : 0 ≤ w := hx.1.trans hx.2
  have hwmem : w ∈ Icc (0 : ℝ) w := ⟨hw, le_rfl⟩
  have h0mem : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw⟩
  have hlen : n - 1 - l + 1 = n - l := by
    have := Finset.mem_range.mp hl
    omega
  rw [kepLogBridge_eq_krDens ν hf.measurable hf0 hfD hν hσ s l hx hwmem,
    kepLogBridge_eq_krDens ν hf.measurable hf0 hfD hν hσ s (n - 1 - l) hwmem hy,
    kepLogBridge_eq_krDens ν hf.measurable hf0 hfD hν hσ s l hx h0mem,
    kepLogBridge_eq_krDens ν hf.measurable hf0 hfD hν hσ s (n - 1 - l) h0mem hy, hlen]

/-- The physical-slope Ward identity for every positive bridge length, in
both orientations, and at boundary as well as interior endpoints. -/
theorem hasDerivAt_krDens_slope_ward (ν : ProbabilityMeasure ℝ) {f f' : ℝ → ℝ}
    {D w σ a : ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ t, HasDerivAt f (f' t) t)
    (hf0 : ∀ t, 0 ≤ f t) (hfD : ∀ t, f t ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)))
    (hσ : σ = 1 ∨ σ = -1) (ha : 0 < a) (n : ℕ)
    {x y : ℝ} (hx : x ∈ Icc 0 w) (hy : y ∈ Icc 0 w) :
    HasDerivAt (fun b => krDens (Icc 0 w) ν f σ (σ * b) (n + 1) x y)
      (-krDens (Icc 0 w) ν f σ (σ * a) (n + 1) x y / a +
        ((n + 1 : ℕ) * σ + x - y) / a *
          kepFixedBridgeRight (kepLogStep f σ) (kepLogStepFirst f' σ) w (Real.log a) n x y -
        kepActualBridgeLogFlux ν f w σ a n x y / a) a := by
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hw : 0 ≤ w := hx.1.trans hx.2
  have hs := hasDerivAt_kepFixedBridge_slope
    (continuous_kepLogStep hf σ) (continuous_kepLogStepSlope hf hf' σ)
    (hasDerivAt_kepLogStep_slope hd σ) w (Real.log a) n x y
  rw [kepFixedBridge_transport (continuous_kepLogStep hf σ)
    (continuous_kepLogStepFirst hf' σ) (hasDerivAt_kepLogStep_right hd σ)
    (kepLogStepSlope_eq hσ2) hw,
    kepLogBridge_eq_krDens ν hf.measurable hf0 hfD hν hσ (Real.log a) n hx hy,
    kepBridgeTransportFlux_eq_actual ν hf hf0 hfD hν hσ (Real.log a) n hx hy,
    Real.exp_log ha] at hs
  have hh := hs.comp a (Real.hasDerivAt_log ha.ne')
  have he :
      (-krDens (Icc 0 w) ν f σ (σ * a) (n + 1) x y +
        ((n + 1 : ℕ) * σ + x - y) *
          kepFixedBridgeRight (kepLogStep f σ) (kepLogStepFirst f' σ) w (Real.log a) n x y -
        kepActualBridgeLogFlux ν f w σ a n x y) * a⁻¹ =
      -krDens (Icc 0 w) ν f σ (σ * a) (n + 1) x y / a +
        ((n + 1 : ℕ) * σ + x - y) / a *
          kepFixedBridgeRight (kepLogStep f σ) (kepLogStepFirst f' σ) w (Real.log a) n x y -
        kepActualBridgeLogFlux ν f w σ a n x y / a := by ring
  rw [he] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with b hb
  dsimp only [Function.comp_apply]
  rw [kepLogBridge_eq_krDens ν hf.measurable hf0 hfD hν hσ (Real.log b) n hx hy,
    Real.exp_log hb]

/-- The smooth representative's endpoint derivative is the actual derivative
on the open band. Boundary pins still use its continuous endpoint values. -/
theorem hasDerivAt_krDens_right_logBridge (ν : ProbabilityMeasure ℝ) {f f' : ℝ → ℝ}
    {D w σ a : ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ t, HasDerivAt f (f' t) t)
    (hf0 : ∀ t, 0 ≤ f t) (hfD : ∀ t, f t ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)))
    (hσ : σ = 1 ∨ σ = -1) (ha : 0 < a) (n : ℕ)
    {x y : ℝ} (hx : x ∈ Icc 0 w) (hy : y ∈ Ioo 0 w) :
    HasDerivAt (fun z => krDens (Icc 0 w) ν f σ (σ * a) (n + 1) x z)
      (kepFixedBridgeRight (kepLogStep f σ) (kepLogStepFirst f' σ) w (Real.log a) n x y) y := by
  apply (hasDerivAt_kepFixedBridge_right (continuous_kepLogStep hf σ)
    (continuous_kepLogStepFirst hf' σ) (hasDerivAt_kepLogStep_right hd σ)
    w (Real.log a) n x y).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
  rw [kepLogBridge_eq_krDens ν hf.measurable hf0 hfD hν hσ (Real.log a) n hx
    ⟨hz.1.le, hz.2.le⟩, Real.exp_log ha]

/-- A pointwise bound for the selected continuous density representative.
Its dependence on the layer scale is harmless for finite-path identification. -/
theorem kepReferenceDensity_le_span {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j) (x : ℝ) :
    (kepReferenceDensity heps hj).density x ≤ kepReferenceSpan eps j := by
  have heps2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hp0 := kepReferenceWeights_nonneg eps j
  have hp := kepReferenceWeights_summable heps2 hj
  have hsum := kepReferenceWeights_sum heps2 hj
  rw [kepReferenceDensity_density]
  unfold gammaScaledMixture
  have hmix : gammaMixtureDensity (kepReferenceWeights eps j) 3
      (kepReferenceSpan eps j * x) ≤ 1 := by
    rw [gammaMixtureDensity, ← hsum]
    exact (summable_gammaMixtureDensity hp0 hp 3 _).tsum_le_tsum
      (fun n => (mul_le_mul_of_nonneg_left (gammaNatDensity_le_one _ _) (hp0 n)).trans_eq
        (mul_one _)) hp
  exact (mul_le_mul_of_nonneg_left hmix (kepReferenceSpan_pos heps j).le).trans_eq
    (mul_one _)

theorem deriv_krDens_slope_eq_logBridge (ν : ProbabilityMeasure ℝ) {f f' : ℝ → ℝ}
    {D w σ a : ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ t, HasDerivAt f (f' t) t)
    (hf0 : ∀ t, 0 ≤ f t) (hfD : ∀ t, f t ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)))
    (hσ : σ = 1 ∨ σ = -1) (ha : 0 < a) (n : ℕ)
    {x y : ℝ} (hx : x ∈ Icc 0 w) (hy : y ∈ Icc 0 w) :
    deriv (fun b => krDens (Icc 0 w) ν f σ (σ * b) (n + 1) x y) a =
      kepFixedBridgeSlope (kepLogStep f σ) (kepLogStepSlope f f' σ) w
        (Real.log a) n x y / a := by
  rw [(hasDerivAt_krDens_slope_ward ν hf hf' hd hf0 hfD hν hσ ha n hx hy).deriv]
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [kepFixedBridge_transport (continuous_kepLogStep hf σ)
    (continuous_kepLogStepFirst hf' σ) (hasDerivAt_kepLogStep_right hd σ)
    (kepLogStepSlope_eq hσ2) (hx.1.trans hx.2),
    kepLogBridge_eq_krDens ν hf.measurable hf0 hfD hν hσ (Real.log a) n hx hy,
    kepBridgeTransportFlux_eq_actual ν hf hf0 hfD hν hσ (Real.log a) n hx hy,
    Real.exp_log ha]
  ring

/-- The actual reference law supplies all analytic and density inputs to the
finite-path physical-slope Ward identity. No Ward certificate is assumed. -/
theorem kepReference_krDens_slope_ward {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {w σ a : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : 0 < a) (n : ℕ)
    {x y : ℝ} (hx : x ∈ Icc 0 w) (hy : y ∈ Icc 0 w) :
    let ν := kepReferenceLaw eps j
    let f := (kepReferenceDensity heps hj).density
    let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    HasDerivAt (fun b => krDens (Icc 0 w) ν f σ (σ * b) (n + 1) x y)
      (-krDens (Icc 0 w) ν f σ (σ * a) (n + 1) x y / a +
        ((n + 1 : ℕ) * σ + x - y) / a *
          kepFixedBridgeRight (kepLogStep f σ) (kepLogStepFirst f' σ) w (Real.log a) n x y -
        kepActualBridgeLogFlux ν f w σ a n x y / a) a := by
  have hc := kepReferenceDensity_classical heps hj
  dsimp only
  apply hasDerivAt_krDens_slope_ward (D := kepReferenceSpan eps j)
    (kepReferenceLaw eps j)
    (continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt)
    hc.2.1 (kepReferenceDensity heps hj).nonneg (kepReferenceDensity_le_span heps hj)
    _ hσ ha n hx hy
  rw [← kepReferenceDensity_toMeasure heps hj]
  rfl

end

end PGM
