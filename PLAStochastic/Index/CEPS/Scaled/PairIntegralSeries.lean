import PLAStochastic.Index.CEPS.Scaled.ActualPairIntegralTaylor
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesBudget

/-! # Formal series and class budgets for actual fixed-cutoff pair integrals -/

noncomputable section
open Complex Set Metric MeasureTheory Finset PowerSeries
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.pairIntegralCoeffBudgetConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) (j : ℕ) : ℝ :=
  dom.pairCoeffBudgetConstant N M j *
    ∫ lam : ℝ, (1 + |lam|) ^ (j + 4) * Real.exp (-dom.positiveEntranceBridgeDecayRate * |lam|)

def cepsScaledPairIntegralSeries {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (z : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun j => cepsScaledSurrogatePairIntegralCoeff dom ρW (N + 1) j z

def CepsCanonDomain.pairIntegralSeriesBudgetConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M δ : ℝ) : ℝ :=
  dom.actualPairIntegralTaylorConstant N M δ +
    ∑ j ∈ range (N + 1), dom.pairIntegralCoeffBudgetConstant (N + 1) M j

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem pairIntegralCoeffBudgetConstant_nonneg (N : ℕ) (M : ℝ) (j : ℕ) :
    0 ≤ dom.pairIntegralCoeffBudgetConstant N M j := by
  have hR := completePairScaleBase_pos dom hW hθ hD N M
  have hK := completePairConstant_nonneg dom N M
  unfold CepsCanonDomain.pairIntegralCoeffBudgetConstant CepsCanonDomain.pairCoeffBudgetConstant
  exact mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)

include hW hθ hD in
theorem cepsScaledSurrogatePairIntegralCoeff_norm_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) (j : ℕ) :
    ‖cepsScaledSurrogatePairIntegralCoeff dom ρW N j z‖ ≤
      dom.pairIntegralCoeffBudgetConstant N M j * (1 + Real.sqrt ‖z‖) ^ (j + 4) *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * Real.sqrt ‖z‖) := by
  have hR := completePairScaleBase_pos dom hW hθ hD N M
  have hK := completePairConstant_nonneg dom N M
  exact (cepsScaled_integral_norm_le_of_envelope (j + 4)
    (positiveEntranceBridge_constants dom hW hθ hD N M).2
    (show 0 ≤ dom.pairCoeffBudgetConstant N M j by
      unfold CepsCanonDomain.pairCoeffBudgetConstant; positivity) z
    (cepsScaledSurrogatePairCoeff_aestronglyMeasurable dom hW hθ hD hf hη hM N hN hz j)
    (fun lam => cepsScaledSurrogatePairCoeff_norm_le dom hW hθ hD hf hη hM N (by omega) hz j lam)).2

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_integral_seriesApprox {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    {δ : ℝ} (hδ : 0 < δ) (hδactual : δ ≤ dom.trueDecayScaleBase M / 4)
    {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.pairIntegralTaylorScaleBase N M) :
    SeriesApprox (∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam)
      (cepsScaledPairIntegralSeries dom ρW N z) N b
      (dom.pairIntegralSeriesBudgetConstant N M δ * (1 + Real.sqrt ‖z‖) ^ (N + 5)) := by
  have hC := actualPairIntegralTaylorConstant_nonneg dom hW hθ hD N
    ((cepsSobolev_nonneg m η fW).trans hM) hδ
  have hcoef (j : ℕ) := pairIntegralCoeffBudgetConstant_nonneg dom hW hθ hD (N + 1) M j
  have hsum : 0 ≤ ∑ j ∈ range (N + 1), dom.pairIntegralCoeffBudgetConstant (N + 1) M j :=
    sum_nonneg fun j _ => hcoef j
  have hH : 1 ≤ 1 + Real.sqrt ‖z‖ := by linarith [Real.sqrt_nonneg ‖z‖]
  have he : Real.exp (-dom.positiveEntranceBridgeDecayRate * Real.sqrt ‖z‖) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (positiveEntranceBridge_constants dom hW hθ hD 0 M).2.le) (Real.sqrt_nonneg _))
  refine ⟨fun j hj => ?_, ?_⟩
  · simp only [cepsScaledPairIntegralSeries, coeff_mk]
    have ht := cepsScaledSurrogatePairIntegralCoeff_norm_le dom hW hθ hD hf hη hM
      (N + 1) (by omega) (by rw [hz]) j
    have hjC : dom.pairIntegralCoeffBudgetConstant (N + 1) M j ≤
        dom.pairIntegralSeriesBudgetConstant N M δ :=
      (single_le_sum (f := fun i => dom.pairIntegralCoeffBudgetConstant (N + 1) M i)
        (fun i _ => hcoef i) (mem_range.mpr (by omega))).trans
        (le_add_of_nonneg_left hC)
    apply ht.trans
    calc _ ≤ dom.pairIntegralCoeffBudgetConstant (N + 1) M j *
        (1 + Real.sqrt ‖z‖) ^ (N + 5) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH (by omega)) (hcoef j))
            he (Real.exp_nonneg _) (mul_nonneg (hcoef j) (by positivity))
      _ ≤ _ := by rw [mul_one]; gcongr
  · have ht := (cepsScaledTrueCutoffPair_integral_taylor_le dom hW hθ hD
      hf hη hM N hN hδ hδactual hb hz hbz).2
    have he' : Real.exp (-dom.pairIntegralTaylorDecayRate * Real.sqrt ‖z‖) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (pairIntegralTaylorDecayRate_pos dom hW hθ hD).le) (Real.sqrt_nonneg _))
    have htrunc : truncEval (cepsScaledPairIntegralSeries dom ρW N z) N b =
        ∑ j ∈ range (N + 1), (b : ℂ) ^ j * cepsScaledSurrogatePairIntegralCoeff dom ρW (N + 1) j z := by
      simp only [truncEval, cepsScaledPairIntegralSeries, coeff_mk, mul_comm]
    rw [htrunc]
    apply ht.trans
    unfold CepsCanonDomain.pairIntegralSeriesBudgetConstant
    calc _ ≤ dom.actualPairIntegralTaylorConstant N M δ * b ^ (N + 1) *
        (1 + Real.sqrt ‖z‖) ^ (N + 5) * 1 := by gcongr
      _ ≤ _ := by rw [mul_one]; nlinarith [mul_nonneg hsum (mul_nonneg (pow_nonneg hb.le (N + 1))
        (pow_nonneg (by positivity : 0 ≤ 1 + Real.sqrt ‖z‖) (N + 5)))]

end PGM
