import PLAStochastic.Index.KEP.ReferenceScale.GraphSecondTransfer

/-!
# Exterior graph transfers on the actual Exp reference orbit

All input-density smoothness and positive-support facts are supplied by the
proved Gamma representation. Test and cutoff derivatives remain ordinary
calculus assumptions. These identities do not yet prove a layer-uniform norm
bound or sum the full greedy-output path expansion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_graph_first_transfer {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {φ φ' R R' : ℝ → ℝ} (hφ : Continuous φ) (hφ' : Continuous φ')
    (hdφ : ∀ y, HasDerivAt φ (φ' y) y) (hR : Continuous R) (hR' : Continuous R')
    (hdR : ∀ s, HasDerivAt R (R' s) s)
    {w lo hi D : ℝ} (hw : 0 ≤ w) (hlh : lo ≤ hi) (hD : D ≠ 0)
    (hlo : R lo = 0) (hhi : R hi = 0) (i r : ℕ) (xA xB : ℝ) :
    let f := (kepReferenceDensity heps hj).density
    kepLogGraphIntegral (kepLogStep f (-1)) (kepLogStep f 1) w lo hi D i r xA xB R φ' =
      kepLogGraphIntegral (kepLogStep f (-1)) (kepLogStep f 1) w lo hi D i r xA xB
        (fun s => Real.exp s * (R s + R' s) / D) φ +
      kepLogGraphFluxIntegral (kepLogStep f (-1)) (kepLogStep f 1)
        w lo hi D i r xA xB R φ := by
  exact kepLogGraphIntegral_derivative_transfer
    (kepReferenceTailDynamics heps hj (Or.inr rfl))
    (kepReferenceTailDynamics heps hj (Or.inl rfl))
    hφ hφ' hdφ hR hR' hdR hw hlh hD hlo hhi i r xA xB

theorem kepReference_graph_second_transfer_with_flux {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {φ φ' φ'' R R' R'' : ℝ → ℝ}
    (hφ : Continuous φ) (hφ' : Continuous φ') (hφ'' : Continuous φ'')
    (hdφ : ∀ y, HasDerivAt φ (φ' y) y) (hddφ : ∀ y, HasDerivAt φ' (φ'' y) y)
    (hR : Continuous R) (hR' : Continuous R') (hR'' : Continuous R'')
    (hdR : ∀ s, HasDerivAt R (R' s) s) (hddR : ∀ s, HasDerivAt R' (R'' s) s)
    {w lo hi D : ℝ} (hw : 0 ≤ w) (hlh : lo ≤ hi) (hD : D ≠ 0)
    (hlo : R lo = 0) (hhi : R hi = 0) (hlo' : R' lo = 0) (hhi' : R' hi = 0)
    (i r : ℕ) (xA xB : ℝ) :
    let f := (kepReferenceDensity heps hj).density
    kepLogGraphIntegral (kepLogStep f (-1)) (kepLogStep f 1) w lo hi D i r xA xB R φ'' =
      kepLogGraphIntegral (kepLogStep f (-1)) (kepLogStep f 1) w lo hi D i r xA xB
        (fun s => Real.exp (2 * s) * (2 * R s + 3 * R' s + R'' s) / D ^ 2) φ +
      kepLogGraphFluxIntegral (kepLogStep f (-1)) (kepLogStep f 1) w lo hi D i r xA xB
        (kepGraphTransferredScalar D R R') φ +
      kepLogGraphFluxIntegral (kepLogStep f (-1)) (kepLogStep f 1) w lo hi D i r xA xB R φ' := by
  exact kepLogGraphIntegral_second_transfer_with_flux
    (kepReferenceTailDynamics heps hj (Or.inr rfl))
    (kepReferenceTailDynamics heps hj (Or.inl rfl))
    hφ hφ' hφ'' hdφ hddφ hR hR' hR'' hdR hddR hw hlh hD hlo hhi hlo' hhi' i r xA xB

/-- Effective reference pins have a positive increment in the fixed numerator.
Each is transferred with only one derivative of its new fixed bridge. -/
theorem kepReference_pinned_graph_transfer {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {φ φ' R R' : ℝ → ℝ} (hφ : Continuous φ) (hφ' : Continuous φ')
    (hdφ : ∀ y, HasDerivAt φ (φ' y) y) (hR : Continuous R) (hR' : Continuous R')
    (hdR : ∀ s, HasDerivAt R (R' s) s)
    {w lo hi D : ℝ} (hw : 0 ≤ w) (hlh : lo ≤ hi) (hD : 0 < D)
    (hlo : R lo = 0) (hhi : R hi = 0) (i r l : ℕ) (xA xB x b : ℝ)
    (hpin : ∃ s, kepFixedBridge (kepLogStep (kepReferenceDensity heps hj).density σ)
      w s l x b ≠ 0) :
    let f := (kepReferenceDensity heps hj).density
    let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    let d := kepGapNumerator σ (l + 1) x b
    kepLogGraphIntegral (kepLogStep f (-1)) (kepLogStep f 1)
      w lo hi (D + d) i r xA xB (kepGraphPinScalar (kepLogStep f σ) w D d l x b R) φ' =
    kepLogGraphIntegral (kepLogStep f (-1)) (kepLogStep f 1) w lo hi (D + d) i r xA xB
      (fun s => Real.exp s * (kepGraphPinScalar (kepLogStep f σ) w D d l x b R s +
        kepGraphPinScalarFirst (kepLogStep f σ) (kepLogStepSlope f f' σ)
          w D d l x b R R' s) / (D + d)) φ +
    kepLogGraphFluxIntegral (kepLogStep f (-1)) (kepLogStep f 1) w lo hi (D + d) i r xA xB
      (kepGraphPinScalar (kepLogStep f σ) w D d l x b R) φ := by
  obtain ⟨s, hs⟩ := hpin
  have hd := kepReference_bridge_numerator_pos heps hj w σ s l x b hs
  exact kepLogPinnedGraphIntegral_derivative_transfer
    (kepReferenceTailDynamics heps hj (Or.inr rfl))
    (kepReferenceTailDynamics heps hj (Or.inl rfl))
    (kepReferenceTailDynamics heps hj hσ)
    hφ hφ' hdφ hR hR' hdR hw hlh hD hd.le hlo hhi i r l xA xB x b

end

end PGM
