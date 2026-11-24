import PLAStochastic.Index.CEPS.Scaled.CutoffPairTaylor
import PLAStochastic.Index.CEPS.Scaled.FixedCutoffApproximation

/-! # Arbitrary-order expansions of the fixed actual complete-pair integral -/

noncomputable section
open Complex Set Metric MeasureTheory Finset
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.pairTaylorApproximationCutoff {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M δ : ℝ) : ℝ :=
  min δ (min (dom.pairComparisonScaleBase (N + 1) M / 8)
    (dom.completePairScaleBase (N + 1) M / 8))

def CepsCanonDomain.pairIntegralTaylorScaleBase {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min 1 (min (dom.pairComparisonScaleBase (N + 1) M / 4)
    (dom.completePairScaleBase (N + 1) M / 4))

def CepsCanonDomain.pairIntegralTaylorDecayRate {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  min (dom.positiveBridgeDecayRate / 2) dom.positiveEntranceBridgeDecayRate

def CepsCanonDomain.actualPairIntegralTaylorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M δ : ℝ) : ℝ :=
  let δN := dom.pairTaylorApproximationCutoff N M δ
  dom.cutoffPairErrorIntegralConstant N M δN +
    dom.cutoffPairTaylorIntegralConstant (N + 1) M δN (N + 1)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem pairTaylorApproximationCutoff_properties (N : ℕ) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 < δ) :
    0 < dom.pairTaylorApproximationCutoff N M δ ∧
      dom.pairTaylorApproximationCutoff N M δ ≤ δ ∧
      dom.pairTaylorApproximationCutoff N M δ ≤ dom.pairComparisonScaleBase (N + 1) M / 4 ∧
      dom.pairTaylorApproximationCutoff N M δ ≤ dom.completePairScaleBase (N + 1) M / 4 := by
  have hB := pairComparisonScaleBase_pos dom hW hθ hD (N + 1) hM
  have hR := completePairScaleBase_pos dom hW hθ hD (N + 1) M
  unfold CepsCanonDomain.pairTaylorApproximationCutoff
  refine ⟨by positivity, min_le_left _ _, ?_, ?_⟩
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))

include hW hθ hD in
theorem pairIntegralTaylorScaleBase_pos (N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 < dom.pairIntegralTaylorScaleBase N M := by
  have hB := pairComparisonScaleBase_pos dom hW hθ hD (N + 1) hM
  have hR := completePairScaleBase_pos dom hW hθ hD (N + 1) M
  unfold CepsCanonDomain.pairIntegralTaylorScaleBase
  positivity

include hW hθ hD in
theorem pairIntegralTaylorDecayRate_pos : 0 < dom.pairIntegralTaylorDecayRate :=
  lt_min (half_pos (positiveBridgePolynomial_constants dom hW hθ hD 0 0).2)
    (positiveEntranceBridge_constants dom hW hθ hD 0 0).2

include hW hθ hD in
theorem actualPairIntegralTaylorConstant_nonneg (N : ℕ) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 < δ) : 0 ≤ dom.actualPairIntegralTaylorConstant N M δ := by
  have hcut := (pairTaylorApproximationCutoff_properties dom hW hθ hD N hM hδ).1
  have ht : 0 ≤ dom.cutoffPairTaylorIntegralConstant (N + 1) M
      (dom.pairTaylorApproximationCutoff N M δ) (N + 1) :=
    mul_nonneg (cutoffPairTaylorBudgetConstant_nonneg dom hW hθ hD (N + 1) M hcut (N + 1))
      (integral_nonneg fun _ => by positivity)
  exact add_nonneg (cutoffPairErrorIntegralConstant_nonneg dom N M hcut) ht

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_integral_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    {δ : ℝ} (hδ : 0 < δ) (hδactual : δ ≤ dom.trueDecayScaleBase M / 4)
    {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.pairIntegralTaylorScaleBase N M) :
    Integrable (cepsScaledTrueCutoffPair dom ρW b δ z) ∧
      ‖(∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam) -
        ∑ j ∈ range (N + 1), (b : ℂ) ^ j *
          cepsScaledSurrogatePairIntegralCoeff dom ρW (N + 1) j z‖ ≤
        dom.actualPairIntegralTaylorConstant N M δ * b ^ (N + 1) *
          (1 + Real.sqrt ‖z‖) ^ (N + 5) *
            Real.exp (-dom.pairIntegralTaylorDecayRate * Real.sqrt ‖z‖) := by
  let δN := dom.pairTaylorApproximationCutoff N M δ
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  obtain ⟨hcut, hle, hsmallB, hsmallR⟩ := pairTaylorApproximationCutoff_properties dom hW hθ hD N hM0 hδ
  have hbzB : b * (1 + Real.sqrt ‖z‖) < dom.pairComparisonScaleBase (N + 1) M / 4 :=
    hbz.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hbzR : b * (1 + Real.sqrt ‖z‖) < dom.completePairScaleBase (N + 1) M / 4 :=
    hbz.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hb1 : b ≤ 1 := by
    have ht := hbz.trans_le (min_le_left _ _)
    nlinarith [mul_nonneg hb.le (Real.sqrt_nonneg ‖z‖)]
  obtain ⟨hi, _, hErr⟩ := cepsScaledCutoffPair_integral_error dom hW hθ hD
    hf hη hM N hN hb hcut hle hδactual hsmallB hz hbzB
  obtain ⟨_, hTaylor⟩ := cepsScaledSurrogateCutoffPair_integral_taylor_le dom hW hθ hD
    hf hη hM (N + 1) (by omega) (by rw [hz]) hb hcut hsmallR hsmallB hbzR hbzB (N + 1)
  have hK1 := cutoffPairErrorIntegralConstant_nonneg dom N M hcut
  have hK2 : 0 ≤ dom.cutoffPairTaylorIntegralConstant (N + 1) M δN (N + 1) :=
    mul_nonneg (cutoffPairTaylorBudgetConstant_nonneg dom hW hθ hD (N + 1) M hcut (N + 1))
      (integral_nonneg fun _ => by positivity)
  have hpow : b ^ (N + 2) ≤ b ^ (N + 1) := by
    rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
    exact mul_le_of_le_one_right (by positivity) hb1
  have he1 : Real.exp (-(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖) ≤
      Real.exp (-dom.pairIntegralTaylorDecayRate * Real.sqrt ‖z‖) := by
    apply Real.exp_le_exp.mpr
    have hc := min_le_left (dom.positiveBridgeDecayRate / 2) dom.positiveEntranceBridgeDecayRate
    change dom.pairIntegralTaylorDecayRate ≤ _ at hc
    nlinarith [Real.sqrt_nonneg ‖z‖]
  have he2 : Real.exp (-dom.positiveEntranceBridgeDecayRate * Real.sqrt ‖z‖) ≤
      Real.exp (-dom.pairIntegralTaylorDecayRate * Real.sqrt ‖z‖) := by
    apply Real.exp_le_exp.mpr
    have hc := min_le_right (dom.positiveBridgeDecayRate / 2) dom.positiveEntranceBridgeDecayRate
    change dom.pairIntegralTaylorDecayRate ≤ _ at hc
    nlinarith [Real.sqrt_nonneg ‖z‖]
  refine ⟨hi, ?_⟩
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam)
    (∫ lam : ℝ, cepsScaledSurrogateCutoffPair dom ρW (N + 1) b δN z lam)
    (∑ j ∈ range (N + 1), (b : ℂ) ^ j * cepsScaledSurrogatePairIntegralCoeff dom ρW (N + 1) j z)
  apply htri.trans
  apply (add_le_add hErr hTaylor).trans
  calc
    _ ≤ dom.cutoffPairErrorIntegralConstant N M δN * b ^ (N + 1) *
        (1 + Real.sqrt ‖z‖) ^ (N + 5) * Real.exp (-dom.pairIntegralTaylorDecayRate * Real.sqrt ‖z‖) +
      dom.cutoffPairTaylorIntegralConstant (N + 1) M δN (N + 1) * b ^ (N + 1) *
        (1 + Real.sqrt ‖z‖) ^ (N + 5) * Real.exp (-dom.pairIntegralTaylorDecayRate * Real.sqrt ‖z‖) := by
      gcongr
    _ = _ := by unfold CepsCanonDomain.actualPairIntegralTaylorConstant; dsimp [δN]; ring

end PGM
