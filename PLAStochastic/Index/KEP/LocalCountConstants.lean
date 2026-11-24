import PLAStochastic.Index.LocalCount.Propagation
import PLAStochastic.Index.KEP.ReferenceGoodEvent
import PLAStochastic.Index.Model.ExpGaps
import PLAStochastic.Index.Model.ExpSequence

/-!
# The local-bound constants of the exponential reference hierarchy

For the canonical iid `Exp(1)` sequence, the local-bound constant
`K_ℓ = refK expSeqMeasure eps expCoord ℓ = m_ℓ · sup_m P(N⁽ℓ⁾ = m)` grows at most
geometrically in `ℓ`: `K_ℓ ≤ C₃^ℓ · log(e · eps²)` for all `eps ≥ eps₁`
(`refK_expCoord_le`).  Layers `ℓ ≥ 1` are the fourth conjunct of `local_count_hierarchy`;
layer `0` has counts `≡ 1`, so `K_0 = 1 ≤ log(e · eps²)`.
-/

namespace PGM

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The `ℝ≥0∞` supremum of the point masses of the count, converted to `ℝ`, is `cntAtom`. -/
theorem toReal_iSup_count_eq_cntAtom [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ × ℕ}
    (hZ : Measurable (Z 0)) :
    (⨆ m : ℕ, P {ω | (Z 0 ω).2 = m}).toReal = cntAtom P Z := by
  rw [cntAtom_eq_iSup hZ, ENNReal.toReal_iSup fun _ => measure_ne_top P _]
  rfl

/-- **Geometric growth of the local-bound constants** of the exponential reference hierarchy:
`K_ℓ ≤ C₃^ℓ · log(e · eps²)` for every layer `ℓ` and every `eps ≥ eps₁`. -/
theorem refK_expCoord_le : ∃ C₃ ≥ 1, ∃ eps₁, ∀ eps ≥ eps₁, ∀ ℓ,
    refK expSeqMeasure eps expCoord ℓ ≤ C₃ ^ ℓ * Real.log (Real.exp 1 * eps ^ 2) := by
  refine ⟨hierConst (vIn 1 1), le_max_left _ _,
    max hierEps (max 1 (epsK (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))))),
    fun eps heps ℓ => ?_⟩
  have hepsH : hierEps ≤ eps := le_trans (le_max_left _ _) heps
  have heps1 : 1 ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) heps
  have hepsK : epsK (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))) ≤ eps :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) heps
  have H := RefHyp.of_gapLaw (gapLaw_exp iidSeq_expCoord (hasLaw_expCoord 0)) hepsK
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · -- layer `0`: `lcount = 1` and every point mass is at most `1`
    have hlc0 : lcount expSeqMeasure (epLayerSeq eps expCoord 0) = 1 := by
      simp [lcount, epLayerSeq, inputPairs]
    have hsup : (⨆ m : ℕ, expSeqMeasure {ω | (epLayerSeq eps expCoord 0 0 ω).2 = m}).toReal
        ≤ 1 := by
      refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
      rw [ENNReal.ofReal_one]
      exact iSup_le fun _ => prob_le_one
    have hL : 1 ≤ Real.log (Real.exp 1 * eps ^ 2) := by
      rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
      have : 0 ≤ Real.log (eps ^ 2) := Real.log_nonneg (by nlinarith)
      linarith
    rw [refK, hlc0, one_mul, pow_zero, one_mul]
    exact le_trans hsup hL
  · -- layers `ℓ ≥ 1`: the fourth conjunct of `local_count_hierarchy`
    have h4 := (local_count_hierarchy iidSeq_expCoord (hasLaw_expCoord 0) H hepsH).2.2.2 ℓ hℓ
    rw [refK, toReal_iSup_count_eq_cntAtom ((H.iid ℓ).measurable 0)]
    exact h4

end PGM
