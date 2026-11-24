import PLAStochastic.Index.KEP.ReferenceScale.ActualLongKernelSlope
import PLAStochastic.Index.KEP.ReferenceScale.LongKernelQuantitative

/-!
# Polynomial budgets for the actual reference long-kernel series

One positive physical output exponent and one positive inheritance decay rate
are selected before epsilon, the layer, and the polynomial length weight. The
actual endpoint slope integrals have a polynomial epsilon budget; their linear
dependence on the input second-derivative norm is exponentially small after a
cutoff of order epsilon. This theorem estimates the long kernel, not the entire
greedy-output density.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- Replacing the geometric factor by a strictly positive factor handles the
case where the original factor is zero, with a class-uniform decay rate. -/
theorem kepLong_geometric_cutoff_decay {D vlo vhi : ℝ}
    (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∃ c : ℝ, 0 < c ∧ ∀ eps : ℝ, ∀ N : ℕ, eps ≤ (N / 2 : ℕ) →
      Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) ≤ Real.exp (-c * eps) := by
  let ρ := Real.sqrt (1 - killCnu D vlo vhi)
  let q := (1 + ρ) / 2
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ < 1 := kBVHighStepL2_regLaw_factor_lt_one hD hvlo hvhi
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  refine ⟨-Real.log q, by linarith, ?_⟩
  intro eps N hN
  calc
    _ ≤ q ^ (N / 2) := pow_le_pow_left₀ hρ0 (by dsimp [q]; linarith) _
    _ = Real.exp (Real.log q * (N / 2 : ℕ)) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log hq0]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonpos_left hN hlog.le
      simpa only [neg_neg] using h

theorem kepReference_second_long_slope_polynomial_budget :
    ∃ theta c eps0 : ℝ, 0 < theta ∧ 0 < c ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ p : ℕ, ∃ K : ℝ, 0 < K ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
          ∀ m N : ℕ, 8 ≤ N → eps ≤ (N / 2 : ℕ) →
          ∀ x y : ℝ, (y = 0 ∨ y = 2 * eps) →
          let f := (kepReferenceDensity heps hj).density
          let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
          let C := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
          let F := fun k : ℕ => (k + N + 1 : ℝ) ^ p *
            Real.exp (2 * theta * (k + N) / C) *
            (∫ a in Icc (1 / 2 : ℝ) 2,
              |truncatedConvolution 0 (2 * eps) (kepStepSpatialSecond f'' σ (σ * a))
                (fun z => krDens (Icc 0 (2 * eps)) (kepReferenceLaw eps j) f σ (σ * a)
                  (m + k + N + 2) x z) y|)
          Summable F ∧ (∑' k : ℕ, F k) ≤
            K * eps ^ (2 * p + 4) *
              (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
                Real.exp (-c * eps) * kepReferenceSecondNorm eps j) := by
  obtain ⟨D, vlo, vhi, e0, hD, hvlo, hvhi, he0, hactual⟩ :=
    kepReference_second_long_slope_uniform
  obtain ⟨c, hc, hdecay⟩ := kepLong_geometric_cutoff_decay hD hvlo hvhi
  let cb := cBr (bIn 1 1) (vIn 1 1)
  let theta := krKappa D vlo vhi / (256 * cb)
  have hcb1 : 1 ≤ cb := one_le_cBr (bAbs_le_bIn 1 1)
  have hcb : 0 < cb := by linarith
  have hκ := krKappa_pos hD hvlo hvhi
  have htheta : 0 < theta := by dsimp [theta]; positivity
  refine ⟨theta, c, e0, htheta, hc, he0, ?_⟩
  intro p
  obtain ⟨K, hK, hsum⟩ :=
    tsum_polynomial_weighted_kepLongSecondSlopeBudget_tail_le hD hvlo hvhi p
  refine ⟨3 * K * 2 ^ (2 * p + 4), by positivity, ?_⟩
  intro eps he heps j hj σ hσ m N hN hcut x y hy
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
  have heta : eta ≤ krKappa D vlo vhi / (16 * (2 * eps) ^ 2) := by
    calc
      eta ≤ 2 * theta / (eps ^ 2 / cb) :=
        div_le_div_of_nonneg_left (by positivity) (div_pos hepssq hcb) hC
      _ = krKappa D vlo vhi / (128 * eps ^ 2) := by
        dsimp [theta]
        field_simp
        ring
      _ ≤ krKappa D vlo vhi / (16 * (2 * eps) ^ 2) := by
        apply div_le_div_of_nonneg_left hκ.le (by positivity)
        nlinarith
  have heta' : eta < krKappa D vlo vhi / (8 * (2 * eps) ^ 2) := by
    apply heta.trans_lt
    apply div_lt_div_of_pos_left hκ (by positivity)
    nlinarith
  let J := kepReferenceSecondNorm eps j
  have hJ : 0 ≤ J := kepReferenceSecondNorm_nonneg eps j
  let G := fun k : ℕ => (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
    kepLongSecondSlopeBudget D vlo vhi (2 * eps) (k + N) (3 * Real.sqrt (1 + J)) J
  have hsG : Summable G := by
    convert (summable_nat_add_iff N).2
      (summable_polynomial_weighted_kepLongSecondSlopeBudget
        (J1 := 3 * Real.sqrt (1 + J)) (J2 := J)
        hD hvlo hvhi (by linarith : 1 ≤ 2 * eps) heta' p) using 1 <;> first
    | rfl
    | (funext k; simp only [G, Nat.cast_add])
  have hbound (k : ℕ) : (k + N + 1 : ℝ) ^ p *
      Real.exp (2 * theta * (k + N) / C) *
      (∫ a in Icc (1 / 2 : ℝ) 2,
        |truncatedConvolution 0 (2 * eps)
          (kepStepSpatialSecond
            (gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)) σ (σ * a))
          (fun z => krDens (Icc 0 (2 * eps)) (kepReferenceLaw eps j)
            (kepReferenceDensity heps hj).density σ (σ * a) (m + k + N + 2) x z) y|) ≤ G k := by
    have hb := (hactual eps he heps j hj (2 * eps) σ hw hσ m (k + N)
      (by omega) x y hy).2.2
    rw [show m + (k + N) + 2 = m + k + N + 2 by omega] at hb
    have heq : 2 * theta * ((k : ℝ) + N) / C = eta * ((k : ℝ) + N) := by
      dsimp [eta]
      ring
    dsimp [G]
    rw [heq]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hsF := hsG.of_nonneg_of_le (fun k =>
    mul_nonneg (by positivity)
      (setIntegral_nonneg measurableSet_Icc (fun _ _ => abs_nonneg _))) hbound
  refine ⟨hsF, ?_⟩
  have hb := hsum (2 * eps) eta (by linarith) heta N
    (3 * Real.sqrt (1 + J)) J (by positivity) hJ
  have hsqrt : Real.sqrt (1 + J) ≤ 1 + Real.sqrt J := by
    have h0 := Real.sqrt_nonneg J
    have h1 := Real.sqrt_nonneg (1 + J)
    have hsq0 := Real.sq_sqrt hJ
    have hsq1 := Real.sq_sqrt (by linarith : 0 ≤ 1 + J)
    nlinarith
  have hrough := hdecay eps N hcut
  calc
    _ ≤ ∑' k : ℕ, G k := hsF.tsum_le_tsum hbound hsG
    _ ≤ K * (2 * eps) ^ (2 * p + 4) *
        (3 * Real.sqrt (1 + J) +
          Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) * J) := hb
    _ ≤ K * (2 * eps) ^ (2 * p + 4) *
        (3 * (1 + Real.sqrt J) + Real.exp (-c * eps) * J) := by gcongr
    _ ≤ K * (2 * eps) ^ (2 * p + 4) *
        (3 * (1 + Real.sqrt J + Real.exp (-c * eps) * J)) := by
      gcongr
      nlinarith [mul_nonneg (Real.exp_pos (-c * eps)).le hJ]
    _ = _ := by rw [mul_pow]; ring

end

end PGM
