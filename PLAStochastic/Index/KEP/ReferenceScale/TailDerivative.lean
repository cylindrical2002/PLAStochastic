import PLAStochastic.Index.KEP.ReferenceScale.TailPins

/-!
# Actual derivatives and the material derivative of exterior tails

The same test calculus applies to zero-step tails. In that case the transport
velocity vanishes at the Dirac point; the parameter derivative of the test is
still present. Actual reference rows discharge every input-density hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem kepTailTest_congr (p : ℝ → ℝ → ℝ) (w s : ℝ) (n : ℕ) (x : ℝ)
    {φ ψ : ℝ → ℝ} (h : ∀ y, φ y = ψ y) :
    kepTailTest p w s n x φ = kepTailTest p w s n x ψ := by
  cases n with
  | zero => exact h x
  | succ n =>
    apply integral_congr_ae
    exact ae_of_all _ fun y => by dsimp only; rw [h]

theorem kepTailTest_zero_test (p : ℝ → ℝ → ℝ) (w s : ℝ) (n : ℕ) (x : ℝ) :
    kepTailTest p w s n x (fun _ => 0) = 0 := by
  cases n <;> simp [kepTailTest]

theorem continuous_kepTailTest
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    {p : ℝ → ℝ → ℝ} (hp : Continuous (Function.uncurry p))
    {τ : X → ℝ} (hτ : Continuous τ) {Φ : X → ℝ → ℝ}
    (hΦ : Continuous (Function.uncurry Φ)) (w : ℝ) (n : ℕ) (x : ℝ) :
    Continuous (fun t => kepTailTest p w (τ t) n x (Φ t)) := by
  cases n with
  | zero => exact hΦ.comp (continuous_id.prodMk continuous_const)
  | succ n =>
    apply continuous_integral_Ioc_of_continuous (a := 0) (b := w)
    exact ((continuous_kepFixedBridge hp w n).comp
      ((hτ.comp continuous_fst).prodMk (continuous_const.prodMk continuous_snd))).mul hΦ

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_kepTailTest_parameter {p Φ Φ' : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p))
    (hΦ : Continuous (Function.uncurry Φ)) (hΦ' : Continuous (Function.uncurry Φ'))
    (hΦd : ∀ t y, HasDerivAt (fun u => Φ u y) (Φ' t y) t)
    (w s : ℝ) (n : ℕ) (x t : ℝ) :
    HasDerivAt (fun u => kepTailTest p w s n x (Φ u))
      (kepTailTest p w s n x (Φ' t)) t := by
  cases n with
  | zero => exact hΦd t x
  | succ n =>
    have hk : Continuous (kepFixedBridge p w s n x) :=
      (continuous_kepFixedBridge hp w n).comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    exact hasDerivAt_integral_Ioc_of_continuous
      (F := fun u y => kepFixedBridge p w s n x y * Φ u y)
      (F' := fun u y => kepFixedBridge p w s n x y * Φ' u y)
      ((hk.comp continuous_snd).mul hΦ) ((hk.comp continuous_snd).mul hΦ')
      (fun u y => (hΦd u y).const_mul _) 0 w t

set_option backward.isDefEq.respectTransparency.types false in
/-- Weak material derivative, with both actual test derivatives. -/
theorem hasDerivAt_kepTailTest_transport {p p' q Φ Φs Φy : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (hp' : Continuous (Function.uncurry p'))
    (hq : Continuous (Function.uncurry q))
    (hpd : ∀ s t, HasDerivAt (p s) (p' s t) t)
    (hps : ∀ s t, HasDerivAt (fun r => p r t) (q s t) s)
    {σ : ℝ} (hward : ∀ s t, q s t = -p s t + (σ - t) * p' s t)
    (hΦ : Continuous (Function.uncurry Φ)) (hΦs : Continuous (Function.uncurry Φs))
    (hΦy : Continuous (Function.uncurry Φy))
    (hΦds : ∀ s y, HasDerivAt (fun r => Φ r y) (Φs s y) s)
    (hΦdy : ∀ s y, HasDerivAt (Φ s) (Φy s y) y)
    {w : ℝ} (hw : 0 ≤ w) (s : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun r => kepTailTest p w r n x (Φ r))
      (kepTailTest p w s n x
        (fun y => Φs s y + (y - x - (n : ℝ) * σ) * Φy s y) +
          kepTailFluxTest p w σ s n x (Φ s)) s := by
  have hh := hasDerivAt_kepTailTest hp hq hps hΦ hΦs hΦds w s n x
  have hφ : Continuous (Φ s) := hΦ.comp (continuous_const.prodMk continuous_id)
  have hφy : Continuous (Φy s) := hΦy.comp (continuous_const.prodMk continuous_id)
  have hφs : Continuous (Φs s) := hΦs.comp (continuous_const.prodMk continuous_id)
  rw [kepTailSlopeTest_transport hp hp' hpd hward hw s n x hφ hφy (hΦdy s),
    ← add_assoc] at hh
  have hvel : Continuous (fun y => (y - x - (n : ℝ) * σ) * Φy s y) := by fun_prop
  have hadd := kepTailTest_add hp w s n x hφs hvel
  change kepTailTest p w s n x (fun y => Φs s y +
    (y - x - (n : ℝ) * σ) * Φy s y) = _ at hadd
  rw [← hadd] at hh
  exact hh

/-- Actual reference killed rows have the physical-slope weak derivative.
The flux includes the terminal Dirac terms and works also for `n = 0`. -/
theorem kepReference_krRow_slope_transport {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {w σ a : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : 0 < a) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc 0 w) {φ φ' : ℝ → ℝ}
    (hφ : Continuous φ) (hφ' : Continuous φ')
    (hdφ : ∀ y, HasDerivAt φ (φ' y) y) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    let ν := kepReferenceLaw eps j
    let f := (kepReferenceDensity heps hj).density
    HasDerivAt (fun b => krRow (Icc 0 w) (ν : Measure ℝ) σ (σ * b) n φ x)
      ((kepTailTest (kepLogStep f σ) w (Real.log a) n x
        (fun y => (y - x - (n : ℝ) * σ) * φ' y) +
          kepActualTailLogFlux ν f w σ a n x φ) / a) a := by
  have hc := kepReferenceDensity_classical heps hj
  let f := (kepReferenceDensity heps hj).density
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt
  have hf' : Continuous f' := continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hν : (kepReferenceLaw eps j : Measure ℝ) =
      volume.withDensity (fun t => ENNReal.ofReal (f t)) := by
    rw [← kepReferenceDensity_toMeasure heps hj]
    rfl
  have hh := hasDerivAt_kepTailTest_transport
    (continuous_kepLogStep hf σ) (continuous_kepLogStepFirst hf' σ)
    (continuous_kepLogStepSlope hf hf' σ) (hasDerivAt_kepLogStep_right hc.2.1 σ)
    (hasDerivAt_kepLogStep_slope hc.2.1 σ) (kepLogStepSlope_eq hσ2)
    (Φ := fun _ y => φ y) (Φs := fun _ _ => 0) (Φy := fun _ y => φ' y)
    (hφ.comp continuous_snd) continuous_const (hφ'.comp continuous_snd)
    (fun s y => hasDerivAt_const s (φ y)) (fun _ y => hdφ y)
    (hx.1.trans hx.2) (Real.log a) n x
  simp only [zero_add] at hh
  rw [kepReference_tailFluxTest_eq_actual heps hj hσ (Real.log a) n hx hφ hM,
    Real.exp_log ha] at hh
  have hcomp := hh.comp a (Real.hasDerivAt_log ha.ne')
  simp only [Function.comp_def, div_eq_mul_inv] at *
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with b hb
  rw [kepTailTest_eq_krRow (kepReferenceLaw eps j) hf.measurable
    (kepReferenceDensity heps hj).nonneg (kepReferenceDensity_le_span heps hj)
    hν hσ (Real.log b) n hx hφ.measurable hM, Real.exp_log hb]

end

end PGM
