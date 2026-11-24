import PLAStochastic.Index.KEP.ReferenceScale.ActualMixedFirstSeries

/-!
# A genuine one-step boundary derivative times a long first derivative

The compact slope average pays the one-step endpoint factor. The long factor
uses the derivative-free regular part and retains geometric remainder decay.
This includes the zero-tail boundary factors omitted by the three-step series.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_boundary_mixed_first_series_polynomial_budget :
    ∃ theta c eps0 : ℝ, 0 < theta ∧ 0 < c ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ p : ℕ, ∃ K : ℝ, 0 < K ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ σA σB : ℝ,
          (σA = 1 ∨ σA = -1) → (σB = 1 ∨ σB = -1) →
          ∀ m N : ℕ, 8 ≤ N → eps ≤ (N / 2 : ℕ) →
          ∀ xA yA xB yB : ℝ,
          (xA = 0 ∨ xA = 2 * eps) → (yA = 0 ∨ yA = 2 * eps) →
          let C := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
          let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
          let F := fun k : ℕ => (k + N + 1 : ℝ) ^ p *
            Real.exp (2 * theta * (k + N) / C) *
            (∫ a in Icc (1 / 2 : ℝ) 2,
              |kepStepSpatialFirst f' σA (σA * a) (yA - xA) *
                kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB a|)
          Summable F ∧ (∑' k : ℕ, F k) ≤
            K * eps ^ (2 * p + 4) * (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
              Real.exp (-c * eps) * kepReferenceSecondNorm eps j) := by
  obtain ⟨D, vlo, vhi, e0, hD, hvlo, hvhi, he0, hactual⟩ :=
    kepReference_first_short_long_uniform
  obtain ⟨c, hc, hdecay⟩ := kepLong_geometric_cutoff_decay hD hvlo hvhi
  let cb := cBr (bIn 1 1) (vIn 1 1)
  let theta := krKappa D vlo vhi / (256 * cb)
  have hcb1 : 1 ≤ cb := one_le_cBr (bAbs_le_bIn 1 1)
  have hcb : 0 < cb := by linarith
  have hκ := krKappa_pos hD hvlo hvhi
  have ht : 0 < theta := by dsimp [theta]; positivity
  refine ⟨theta, c, e0, ht, hc, he0, ?_⟩
  intro p
  obtain ⟨K, hK, hsum⟩ := tsum_polynomial_weighted_kepLongFirstBudget_tail_le hD hvlo hvhi p
  refine ⟨12 * K * 2 ^ (2 * p + 4), by positivity, ?_⟩
  intro eps he heps j hj σA σB hσA hσB m N hN hcut xA yA xB yB hxA hyA
  dsimp only
  have heps2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hepspos : 0 < eps := by linarith
  let C := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
  have hC : eps ^ 2 / cb ≤ C :=
    (segMean_bracket gapLaw_expCoord ((le_max_right _ _).trans heps) j).1
  have hCpos : 0 < C := (div_pos (by positivity) hcb).trans_le hC
  let eta := 2 * theta / C
  have heta : eta ≤ krKappa D vlo vhi / (16 * (2 * eps) ^ 2) := by
    calc
      eta ≤ 2 * theta / (eps ^ 2 / cb) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hC
      _ = krKappa D vlo vhi / (128 * eps ^ 2) := by
        dsimp [theta]
        field_simp
        ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left hκ.le (by positivity)
        nlinarith
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let J := kepReferenceSecondNorm eps j
  let S := Real.sqrt (1 + J)
  have hJ : 0 ≤ J := kepReferenceSecondNorm_nonneg eps j
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  obtain ⟨hiA, hA⟩ := kepReference_endpoint_slope_budget heps hj
    (by linarith : 2 ≤ 2 * eps) hyA hxA (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 2) hσA
  have hA' : (∫ a in Icc (1 / 2 : ℝ) 2,
      |kepStepSpatialFirst f' σA (σA * a) (yA - xA)|) ≤ 3 * S :=
    hA.trans (kepReferenceFirstNorm_le_sqrt heps hj)
  have hB0 (k : ℕ) : 0 ≤ kepLongFirstBudget D vlo vhi (2 * eps) (k + N) (3 * S) := by
    have hV := kepLongUniformVariation_nonneg (w := 2 * eps) (k + N) hD hvlo hvhi
    have hR := kepLongUniformRemainder_nonneg D vlo vhi (2 * eps) (k + N)
    dsimp [kepLongFirstBudget]
    positivity
  have hprod (k : ℕ) :
      IntegrableOn (fun a => |kepStepSpatialFirst f' σA (σA * a) (yA - xA) *
        kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB a|)
        (Icc (1 / 2 : ℝ) 2) ∧
      (∫ a in Icc (1 / 2 : ℝ) 2,
        |kepStepSpatialFirst f' σA (σA * a) (yA - xA) *
          kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB a|) ≤
        3 * S * kepLongFirstBudget D vlo vhi (2 * eps) (k + N) (3 * S) := by
    let B := kepLongFirstBudget D vlo vhi (2 * eps) (k + N) (3 * S)
    have hb (a : ℝ) (ha : a ∈ Icc (1 / 2 : ℝ) 2) :
        |kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB a| ≤ B := by
      have h := (hactual eps he heps j hj (2 * eps) a σB (by linarith) ha.1 ha.2 hσB).2
        m (k + N) (by omega) xB yB
      simpa only [kepReferenceFirstKernel, Nat.add_assoc] using h
    have hm := measurable_kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB
    have hd := hiA.const_mul B
    have hi : IntegrableOn (fun a => |kepStepSpatialFirst f' σA (σA * a) (yA - xA) *
        kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB a|)
        (Icc (1 / 2 : ℝ) 2) := by
      simp only [abs_mul]
      apply hd.mono' (hiA.aestronglyMeasurable.mul hm.abs.aestronglyMeasurable)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_abs]
      exact (mul_le_mul_of_nonneg_left (hb a ha) (abs_nonneg _)).trans_eq (by ring)
    refine ⟨hi, ?_⟩
    calc
      _ ≤ ∫ a in Icc (1 / 2 : ℝ) 2, B * |kepStepSpatialFirst f' σA (σA * a) (yA - xA)| := by
        apply setIntegral_mono_on hi hd measurableSet_Icc
        intro a ha
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hb a ha) (abs_nonneg _)).trans_eq (by ring)
      _ = B * ∫ a in Icc (1 / 2 : ℝ) 2, |kepStepSpatialFirst f' σA (σA * a) (yA - xA)| :=
        integral_const_mul _ _
      _ ≤ B * (3 * S) := mul_le_mul_of_nonneg_left hA' (hB0 k)
      _ = _ := by ring
  obtain ⟨hs, hb⟩ := hsum (2 * eps) eta (by linarith) heta N (3 * S) (by positivity)
  let G := fun k : ℕ => (3 * S) * ((k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
    kepLongFirstBudget D vlo vhi (2 * eps) (k + N) (3 * S))
  have hsG : Summable G := hs.mul_left _
  have hFG (k : ℕ) : (k + N + 1 : ℝ) ^ p * Real.exp (2 * theta * (k + N) / C) *
      (∫ a in Icc (1 / 2 : ℝ) 2, |kepStepSpatialFirst f' σA (σA * a) (yA - xA) *
        kepReferenceFirstKernel heps hj (2 * eps) σB (m + k + N) xB yB a|) ≤ G k := by
    have heq : 2 * theta * (k + N : ℝ) / C = eta * (k + N : ℝ) := by dsimp [eta]; ring
    rw [heq]
    exact (mul_le_mul_of_nonneg_left (hprod k).2 (by positivity)).trans_eq (by dsimp [G]; ring)
  have hsF := hsG.of_nonneg_of_le (fun k => mul_nonneg (by positivity)
    (setIntegral_nonneg measurableSet_Icc (fun _ _ => abs_nonneg _))) hFG
  refine ⟨hsF, ?_⟩
  have hsqrt : S ≤ 1 + Real.sqrt J := by
    have hs1 := Real.sq_sqrt (by linarith : 0 ≤ 1 + J)
    have hs0 := Real.sq_sqrt hJ
    have h0 := Real.sqrt_nonneg J
    dsimp [S]
    nlinarith
  have hdec := hdecay eps N hcut
  have hdec1 : Real.exp (-c * eps) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hnorm : S * (1 + Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) * (3 * S)) ≤
      4 * (1 + Real.sqrt J + Real.exp (-c * eps) * J) := by
    have hsq : S ^ 2 = 1 + J := Real.sq_sqrt (by linarith)
    calc
      _ = S + 3 * Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) * (1 + J) := by nlinarith [hsq]
      _ ≤ 1 + Real.sqrt J + 3 * Real.exp (-c * eps) * (1 + J) := by gcongr
      _ ≤ _ := by nlinarith [Real.sqrt_nonneg J, mul_nonneg (Real.exp_pos (-c * eps)).le hJ]
  calc
    _ ≤ ∑' k : ℕ, G k := hsF.tsum_le_tsum hFG hsG
    _ = (3 * S) * ∑' k : ℕ, (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
        kepLongFirstBudget D vlo vhi (2 * eps) (k + N) (3 * S) := tsum_mul_left
    _ ≤ (3 * S) * (K * (2 * eps) ^ (2 * p + 4) *
        (1 + Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) * (3 * S))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (3 * K * (2 * eps) ^ (2 * p + 4)) *
        (S * (1 + Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) * (3 * S))) := by ring
    _ ≤ (3 * K * (2 * eps) ^ (2 * p + 4)) *
        (4 * (1 + Real.sqrt J + Real.exp (-c * eps) * J)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by rw [mul_pow]; ring

end

end PGM
