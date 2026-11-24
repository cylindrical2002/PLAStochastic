import PLAStochastic.Index.KEP.ReferenceScale.GraphFluxAssembly

/-!
# Complete finite second graph transfer on the actual reference orbit

The entire first-flux derivative test is eliminated by the finite pin graph
sum. Pins with nonpositive physical numerator vanish identically, as do their
actual first derivatives, so they cannot create a zero-denominator problem.
Both zero-step tail cases and all four outward boundary signs are retained.
This identity still needs weighted estimates and the infinite path summation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepGraphLeftPinRemainder (pA qA pB : ℝ → ℝ → ℝ) (w lo hi D : ℝ) (i r : ℕ)
    (xA xB : ℝ) (R R' φ : ℝ → ℝ) (l : ℕ) (b : ℝ) : ℝ :=
  let d := kepGapNumerator (-1) (l + 1) xA b
  let U := kepGraphPinScalar pA w D d l xA b R
  let U' := kepGraphPinScalarFirst pA qA w D d l xA b R R'
  kepLogGraphIntegral pA pB w lo hi (D + d) (i - 1 - l) r b xB
    (fun s => Real.exp s * (U s + U' s) / (D + d)) φ +
    kepLogGraphFluxIntegral pA pB w lo hi (D + d) (i - 1 - l) r b xB U φ

def kepGraphRightPinRemainder (pA pB qB : ℝ → ℝ → ℝ) (w lo hi D : ℝ) (i r : ℕ)
    (xA xB : ℝ) (R R' φ : ℝ → ℝ) (l : ℕ) (b : ℝ) : ℝ :=
  let d := kepGapNumerator 1 (l + 1) xB b
  let U := kepGraphPinScalar pB w D d l xB b R
  let U' := kepGraphPinScalarFirst pB qB w D d l xB b R R'
  kepLogGraphIntegral pA pB w lo hi (D + d) i (r - 1 - l) xA b
    (fun s => Real.exp s * (U s + U' s) / (D + d)) φ +
    kepLogGraphFluxIntegral pA pB w lo hi (D + d) i (r - 1 - l) xA b U φ

theorem kepReference_pinned_graph_transfer_all {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {φ φ' R R' : ℝ → ℝ} (hφ : Continuous φ) (hφ' : Continuous φ')
    (hdφ : ∀ y, HasDerivAt φ (φ' y) y) (hR : Continuous R) (hR' : Continuous R')
    (hdR : ∀ s, HasDerivAt R (R' s) s)
    {w lo hi D : ℝ} (hw : 0 ≤ w) (hlh : lo ≤ hi) (hD : 0 < D)
    (hlo : R lo = 0) (hhi : R hi = 0) (i r l : ℕ) (xA xB x b : ℝ) :
    let f := (kepReferenceDensity heps hj).density
    let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    let d := kepGapNumerator σ (l + 1) x b
    let U := kepGraphPinScalar (kepLogStep f σ) w D d l x b R
    let U' := kepGraphPinScalarFirst (kepLogStep f σ) (kepLogStepSlope f f' σ)
      w D d l x b R R'
    kepLogGraphIntegral (kepLogStep f (-1)) (kepLogStep f 1)
      w lo hi (D + d) i r xA xB U φ' =
    kepLogGraphIntegral (kepLogStep f (-1)) (kepLogStep f 1) w lo hi (D + d) i r xA xB
      (fun s => Real.exp s * (U s + U' s) / (D + d)) φ +
    kepLogGraphFluxIntegral (kepLogStep f (-1)) (kepLogStep f 1)
      w lo hi (D + d) i r xA xB U φ := by
  let A := kepReferenceTailDynamics heps hj (σ := -1) (Or.inr rfl)
  let B := kepReferenceTailDynamics heps hj (σ := 1) (Or.inl rfl)
  let C := kepReferenceTailDynamics heps hj hσ
  let d := kepGapNumerator σ (l + 1) x b
  by_cases hd : 0 ≤ d
  · exact kepLogPinnedGraphIntegral_derivative_transfer A B C
      hφ hφ' hdφ hR hR' hdR hw hlh hD hd hlo hhi i r l xA xB x b
  · have hzero (s : ℝ) : kepFixedBridge C.step w s l x b = 0 :=
      kepFixedBridge_eq_zero_of_numerator_nonpos
        (kepReferenceDensity_classical heps hj).1 w σ s l x b (le_of_lt (lt_of_not_ge hd))
    have hzero' (s : ℝ) : kepFixedBridgeSlope C.step C.slope w s l x b = 0 := by
      have hh := hasDerivAt_kepFixedBridge_slope C.continuous_step C.continuous_slope
        C.slope_derivative w s l x b
      have he : (fun t => kepFixedBridge C.step w t l x b) = fun _ => (0 : ℝ) := funext hzero
      rw [he] at hh
      exact hh.unique (hasDerivAt_const s 0)
    have hU : kepGraphPinScalar C.step w D d l x b R = fun _ => 0 := by
      funext s
      simp [kepGraphPinScalar, hzero s]
    have hU' : kepGraphPinScalarFirst C.step C.slope w D d l x b R R' = fun _ => 0 := by
      funext s
      simp [kepGraphPinScalarFirst, hzero s, hzero' s]
    change kepLogGraphIntegral A.step B.step w lo hi (D + d) i r xA xB
      (kepGraphPinScalar C.step w D d l x b R) φ' =
      kepLogGraphIntegral A.step B.step w lo hi (D + d) i r xA xB
        (fun s => Real.exp s * (kepGraphPinScalar C.step w D d l x b R s +
          kepGraphPinScalarFirst C.step C.slope w D d l x b R R' s) / (D + d)) φ +
      kepLogGraphFluxIntegral A.step B.step w lo hi (D + d) i r xA xB
        (kepGraphPinScalar C.step w D d l x b R) φ
    rw [hU, hU']
    simp [kepLogGraphIntegral, kepLogGraphFluxIntegral]

/-- The full integrated finite flux no longer contains a differentiated test. -/
theorem kepReference_graph_flux_derivative_transfer {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {φ φ' R R' : ℝ → ℝ} (hφ : Continuous φ) (hφ' : Continuous φ')
    (hdφ : ∀ y, HasDerivAt φ (φ' y) y) (hR : Continuous R) (hR' : Continuous R')
    (hdR : ∀ s, HasDerivAt R (R' s) s)
    {w lo hi D : ℝ} (hw : 0 ≤ w) (hlh : lo ≤ hi) (hD : 0 < D)
    (hlo : R lo = 0) (hhi : R hi = 0) (i r : ℕ) (xA xB : ℝ) :
    let f := (kepReferenceDensity heps hj).density
    let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    let pA := kepLogStep f (-1)
    let pB := kepLogStep f 1
    kepLogGraphFluxIntegral pA pB w lo hi D i r xA xB R φ' =
      kepGraphBoundarySum i r w
        (kepGraphLeftPinRemainder pA (kepLogStepSlope f f' (-1)) pB
          w lo hi D i r xA xB R R' φ)
        (kepGraphRightPinRemainder pA pB (kepLogStepSlope f f' 1)
          w lo hi D i r xA xB R R' φ) := by
  let A := kepReferenceTailDynamics heps hj (σ := -1) (Or.inr rfl)
  let B := kepReferenceTailDynamics heps hj (σ := 1) (Or.inl rfl)
  dsimp only
  change kepLogGraphFluxIntegral A.step B.step w lo hi D i r xA xB R φ' =
    kepGraphBoundarySum i r w
      (kepGraphLeftPinRemainder A.step A.slope B.step w lo hi D i r xA xB R R' φ)
      (kepGraphRightPinRemainder A.step B.step B.slope w lo hi D i r xA xB R R' φ)
  rw [kepLogGraphFluxIntegral_eq_pin_integrals A.continuous_step B.continuous_step hR hφ']
  have hL (l : ℕ) (b : ℝ) : kepGraphLeftPinIntegral A.step B.step w lo hi D i r xA xB R φ' l b =
      kepGraphLeftPinRemainder A.step A.slope B.step w lo hi D i r xA xB R R' φ l b :=
    kepReference_pinned_graph_transfer_all heps hj (Or.inr rfl)
      hφ hφ' hdφ hR hR' hdR hw hlh hD hlo hhi (i - 1 - l) r l b xB xA b
  have hRpin (l : ℕ) (b : ℝ) : kepGraphRightPinIntegral A.step B.step w lo hi D i r xA xB R φ' l b =
      kepGraphRightPinRemainder A.step B.step B.slope w lo hi D i r xA xB R R' φ l b :=
    kepReference_pinned_graph_transfer_all heps hj (Or.inl rfl)
      hφ hφ' hdφ hR hR' hdR hw hlh hD hlo hhi i (r - 1 - l) l xA b xB b
  change kepGraphBoundarySum i r w
    (kepGraphLeftPinIntegral A.step B.step w lo hi D i r xA xB R φ')
    (kepGraphRightPinIntegral A.step B.step w lo hi D i r xA xB R φ') = _
  unfold kepGraphBoundarySum
  simp_rw [hL, hRpin]

/-- Complete finite second transfer. Every right-hand test is `φ`; there is
no remaining `φ'` or `φ''` in a boundary, zero-step or ineffective pin term. -/
theorem kepReference_graph_second_transfer {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {φ φ' φ'' R R' R'' : ℝ → ℝ}
    (hφ : Continuous φ) (hφ' : Continuous φ') (hφ'' : Continuous φ'')
    (hdφ : ∀ y, HasDerivAt φ (φ' y) y) (hddφ : ∀ y, HasDerivAt φ' (φ'' y) y)
    (hR : Continuous R) (hR' : Continuous R') (hR'' : Continuous R'')
    (hdR : ∀ s, HasDerivAt R (R' s) s) (hddR : ∀ s, HasDerivAt R' (R'' s) s)
    {w lo hi D : ℝ} (hw : 0 ≤ w) (hlh : lo ≤ hi) (hD : 0 < D)
    (hlo : R lo = 0) (hhi : R hi = 0) (hlo' : R' lo = 0) (hhi' : R' hi = 0)
    (i r : ℕ) (xA xB : ℝ) :
    let f := (kepReferenceDensity heps hj).density
    let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    let pA := kepLogStep f (-1)
    let pB := kepLogStep f 1
    kepLogGraphIntegral pA pB w lo hi D i r xA xB R φ'' =
      kepLogGraphIntegral pA pB w lo hi D i r xA xB
        (fun s => Real.exp (2 * s) * (2 * R s + 3 * R' s + R'' s) / D ^ 2) φ +
      kepLogGraphFluxIntegral pA pB w lo hi D i r xA xB
        (kepGraphTransferredScalar D R R') φ +
      kepGraphBoundarySum i r w
        (kepGraphLeftPinRemainder pA (kepLogStepSlope f f' (-1)) pB
          w lo hi D i r xA xB R R' φ)
        (kepGraphRightPinRemainder pA pB (kepLogStepSlope f f' 1)
          w lo hi D i r xA xB R R' φ) := by
  have hh := kepReference_graph_second_transfer_with_flux heps hj
    hφ hφ' hφ'' hdφ hddφ hR hR' hR'' hdR hddR hw hlh hD.ne' hlo hhi hlo' hhi' i r xA xB
  dsimp only at hh ⊢
  rw [kepReference_graph_flux_derivative_transfer heps hj
    hφ hφ' hdφ hR hR' hdR hw hlh hD hlo hhi i r xA xB] at hh
  exact hh

end

end PGM
