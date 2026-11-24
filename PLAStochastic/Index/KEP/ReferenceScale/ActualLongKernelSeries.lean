import PLAStochastic.Index.KEP.ReferenceScale.ActualLongKernelSlope
import PLAStochastic.Index.KEP.ReferenceScale.LongKernelSummability

/-!
# Actual long-kernel series at one fixed physical output weight

The reference compression lower bound selects a single positive exponent before
epsilon and the layer. At that exponent every polynomially weighted series of
actual compact-slope second-derivative integrals is summable. This is the long
kernel series only; the full greedy output still requires graph and rare-path
identification and budgets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_second_long_slope_series :
    ∃ theta eps0 : ℝ, 0 < theta ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
        ∀ m : ℕ, ∀ x y : ℝ, (y = 0 ∨ y = 2 * eps) → ∀ p : ℕ,
        let f := (kepReferenceDensity heps hj).density
        let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let C := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
        Summable (fun k : ℕ => (k + 9 : ℝ) ^ p * Real.exp (2 * theta * (k + 8) / C) *
          (∫ a in Icc (1 / 2 : ℝ) 2,
            |truncatedConvolution 0 (2 * eps) (kepStepSpatialSecond f'' σ (σ * a))
              (fun z => krDens (Icc 0 (2 * eps)) (kepReferenceLaw eps j) f σ (σ * a)
                (m + k + 10) x z) y|)) := by
  obtain ⟨D, vlo, vhi, e0, hD, hvlo, hvhi, he0, hactual⟩ :=
    kepReference_second_long_slope_uniform
  let cb := cBr (bIn 1 1) (vIn 1 1)
  let theta := krKappa D vlo vhi / (256 * cb)
  have hcb1 : 1 ≤ cb := one_le_cBr (bAbs_le_bIn 1 1)
  have hcb : 0 < cb := by linarith
  have hκ := krKappa_pos hD hvlo hvhi
  have htheta : 0 < theta := by dsimp [theta]; positivity
  refine ⟨theta, e0, htheta, he0, ?_⟩
  intro eps he heps j hj σ hσ m x y hy p
  dsimp only
  have heps2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hepspos : 0 < eps := by linarith
  have hepssq : 0 < eps ^ 2 := by positivity
  have hw : 2 ≤ 2 * eps := by linarith
  let C := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
  have hC : eps ^ 2 / cb ≤ C :=
    (segMean_bracket gapLaw_expCoord ((le_max_right _ _).trans heps) j).1
  have hC0 : 0 < C := (div_pos hepssq hcb).trans_le hC
  let eta := 2 * theta / C
  have heta : eta < krKappa D vlo vhi / (8 * (2 * eps) ^ 2) := by
    calc
      eta ≤ 2 * theta / (eps ^ 2 / cb) :=
        div_le_div_of_nonneg_left (by positivity) (div_pos hepssq hcb) hC
      _ = krKappa D vlo vhi / (128 * eps ^ 2) := by
        dsimp [theta]
        field_simp
        ring
      _ < krKappa D vlo vhi / (8 * (2 * eps) ^ 2) := by
        apply div_lt_div_of_pos_left hκ (by positivity)
        nlinarith
  let J1 := 3 * Real.sqrt (1 + kepReferenceSecondNorm eps j)
  let J2 := kepReferenceSecondNorm eps j
  have hs := summable_polynomial_weighted_kepLongSecondSlopeBudget
    (J1 := J1) (J2 := J2) hD hvlo hvhi (by linarith : 1 ≤ 2 * eps) heta p
  have hs8 := (summable_nat_add_iff 8).2 hs
  have htarget : Summable (fun k : ℕ => (k + 9 : ℝ) ^ p *
      Real.exp (2 * theta * (k + 8) / C) *
        kepLongSecondSlopeBudget D vlo vhi (2 * eps) (k + 8) J1 J2) := by
    convert hs8 using 1 <;> first
    | rfl
    | (funext k
       simp only [Nat.cast_add, Nat.cast_ofNat]
       have heq : 2 * theta * ((k : ℝ) + 8) / C = eta * ((k : ℝ) + 8) := by
         dsimp [eta]
         ring
       rw [show (k : ℝ) + 8 + 1 = k + 9 by ring, heq])
  apply htarget.of_nonneg_of_le
  · intro k
    exact mul_nonneg (by positivity)
      (setIntegral_nonneg measurableSet_Icc (fun _ _ => abs_nonneg _))
  · intro k
    have hb := (hactual eps he heps j hj (2 * eps) σ hw hσ m (k + 8)
      (by omega) x y hy).2.2
    have hn : m + (k + 8) + 2 = m + k + 10 := by omega
    rw [hn] at hb
    exact mul_le_mul_of_nonneg_left hb (by positivity)

end

end PGM
