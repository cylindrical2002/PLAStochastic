import PLAStochastic.Index.KEP.ReferenceScale.ActualGraphOtherSeries

/-!
# The complete actual long-core graph series has a uniform polynomial budget

All original second graphs are summed over the two exterior lengths and the
selected long bridge. The retained input-second-norm coefficient is exponentially
small in tolerance. This theorem does not estimate the complementary rare paths.
-/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_long_core_graph_series :
    ∃ theta c K eps0 : ℝ, 0 < theta ∧ 0 < c ∧ 0 < K ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ N : ℕ,
        8 ≤ N → eps ≤ (N / 2 : ℕ) → (N : ℝ) ≤ 7 * eps →
        ∀ B : ℝ, 0 ≤ B → ∀ φ : (ℕ × ℕ × ℕ) → ℝ → ℝ, (∀ z, Continuous (φ z)) →
          (∀ z t, 0 ≤ t → |φ z t| ≤ B * Real.exp (theta * t /
            segMean expSeqMeasure eps (epLayerSeq eps expCoord j))) →
        let f := (kepReferenceDensity heps hj).density
        let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let F := fun z : ℕ × ℕ × ℕ =>
          |kepCertificateSecondGraph f f' f'' eps ((z.2.2 + N + 3 : ℕ) - 2 * eps)
            z.1 z.2.1 (z.2.2 + N + 2) (φ z)|
        Summable F ∧ (∑' z : ℕ × ℕ × ℕ, F z) ≤
          B * K * eps ^ 43 *
            (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
              Real.exp (-c * eps) * kepReferenceSecondNorm eps j) := by
  obtain ⟨C, κ, A, eG, hC, hκ, hκ1, hA, heG, hgraph⟩ :=
    kepReference_finite_second_graph_polynomial
  obtain ⟨theta, c, eH, ht, htcap, hc, heH, hhighest⟩ :=
    kepReference_graph_highest_series_polynomial hκ
  obtain ⟨KX, hKX, hX⟩ := hhighest 3
  obtain ⟨KY, hKY, hY⟩ := kepReference_graph_other_series_polynomial hκ ht.le htcap 5
  let K := 9 * C ^ 2 * (4 * A * KX + 684 * A * C ^ 3 * KY)
  have hCpos : 0 < C := by linarith
  have hApos : 0 < A := by linarith
  refine ⟨theta, c, K, max eG eH, ht, hc, by dsimp [K]; positivity,
    heG.trans (le_max_left _ _), ?_⟩
  intro eps he heps j hj N hN hcut hNup B hB φ hφ hφb
  dsimp only
  let f := (kepReferenceDensity heps hj).density
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let mean := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
  let rate := κ / (2 * (2 * eps) ^ 2)
  let J := Real.sqrt (1 + kepReferenceSecondNorm eps j)
  let R := 1 + Real.sqrt (kepReferenceSecondNorm eps j) +
    Real.exp (-c * eps) * kepReferenceSecondNorm eps j
  let X := fun z : ℕ × ℕ × ℕ =>
    (2 * eps + (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 1) ^ 3 *
      Real.exp (2 * theta * ((z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 2 * eps) / mean) *
      kepLogSlopeNorm (fun s => kepFixedBridgeRight (kepLogStep f 1)
        (kepLogStepSecond f'' 1) (2 * eps) s (z.2.2 + N + 2) 0 (2 * eps)) *
      Real.exp (-rate * (z.1 + z.2.1 : ℕ))
  let Y := fun z : ℕ × ℕ × ℕ =>
    (2 * eps + (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 1) ^ 5 *
      Real.exp (2 * theta * ((z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 2 * eps) / mean) *
      Real.exp (-rate * (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ))
  let T := (1 + C * (2 * eps)) ^ 2 * B
  let F := fun z : ℕ × ℕ × ℕ =>
    |kepCertificateSecondGraph f f' f'' eps ((z.2.2 + N + 3 : ℕ) - 2 * eps)
      z.1 z.2.1 (z.2.2 + N + 2) (φ z)|
  obtain ⟨hsX, hbX⟩ := hX eps ((le_max_right _ _).trans he) heps j hj N hN hcut hNup
  obtain ⟨hsY, hbY⟩ := hY eps heps j N hNup
  norm_num only [Nat.reduceMul, Nat.reduceAdd] at hbX hbY
  have hcmean := (kepReference_graph_exponent_rate hκ ht.le htcap heps j).1
  have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have he1 : 1 ≤ eps := by linarith
  have hepos : 0 < eps := by linarith
  have hJ0 := kepReferenceSecondNorm_nonneg eps j
  have hJ : 0 ≤ J := Real.sqrt_nonneg _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hJR : J ≤ R := by
    have h0 := Real.sqrt_nonneg (kepReferenceSecondNorm eps j)
    have h1 := Real.sqrt_nonneg (1 + kepReferenceSecondNorm eps j)
    have hsq0 := Real.sq_sqrt hJ0
    have hsq1 := Real.sq_sqrt (by linarith : 0 ≤ 1 + kepReferenceSecondNorm eps j)
    have hlin : J ≤ 1 + Real.sqrt (kepReferenceSecondNorm eps j) := by
      dsimp [J]
      nlinarith
    have hsmall : 0 ≤ Real.exp (-c * eps) * kepReferenceSecondNorm eps j := by positivity
    dsimp [R]
    linarith
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hNband : 2 * eps ≤ (N : ℝ) := by
    have hn : 2 * (N / 2) ≤ N := by omega
    have hn' : 2 * ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
    linarith
  have hb (z : ℕ × ℕ × ℕ) : F z ≤ T * (4 * A * X z + 684 * A * C ^ 3 * J * Y z) := by
    have hd : 1 ≤ ((z.2.2 + N + 2 + 1 : ℕ) : ℝ) - 2 * eps := by
      push_cast
      linarith [show (0 : ℝ) ≤ z.2.2 by positivity]
    have hh := hgraph eps ((le_max_left _ _).trans he) heps j hj z.1 z.2.1 (z.2.2 + N + 2)
      hd theta mean B ht.le hcmean hB (φ z) (hφ z) (hφb z)
    dsimp only at hh
    have hn : z.2.2 + N + 2 + 1 = z.2.2 + N + 3 := by omega
    have hk : z.1 + z.2.1 + (z.2.2 + N + 3) = z.1 + z.2.1 + z.2.2 + N + 3 := by omega
    have htlen : z.2.2 + N + 3 + z.1 + z.2.1 = z.1 + z.2.1 + z.2.2 + N + 3 := by omega
    have hsize : 2 * eps + ((z.1 + z.2.1 + z.2.2 + N + 3 + 1 : ℕ) : ℝ) =
        2 * eps + (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
      ring
    simp only [hn, hk, htlen, hsize] at hh
    convert hh using 1
    dsimp only [F, T, X, Y, J, mean, rate]
    ring
  have hsM := ((hsX.mul_left (4 * A)).add (hsY.mul_left (684 * A * C ^ 3 * J))).mul_left T
  have hsF : Summable F := hsM.of_nonneg_of_le (fun z => abs_nonneg _) hb
  refine ⟨hsF, ?_⟩
  have hsum : (∑' z : ℕ × ℕ × ℕ, F z) ≤
      T * (4 * A * (∑' z : ℕ × ℕ × ℕ, X z) +
        684 * A * C ^ 3 * J * (∑' z : ℕ × ℕ × ℕ, Y z)) := by
    apply (hsF.tsum_le_tsum hb hsM).trans_eq
    rw [tsum_mul_left, (hsX.mul_left (4 * A)).tsum_add (hsY.mul_left (684 * A * C ^ 3 * J)),
      tsum_mul_left, tsum_mul_left]
  have hpow : eps ^ 29 ≤ eps ^ 41 := pow_le_pow_right₀ he1 (by norm_num)
  have hbX' : (∑' z : ℕ × ℕ × ℕ, X z) ≤ KX * eps ^ 41 * R := by
    apply hbX.trans
    gcongr
  have hbY' : J * (∑' z : ℕ × ℕ × ℕ, Y z) ≤ KY * eps ^ 41 * R := by
    calc
      _ ≤ J * (KY * eps ^ 41) := mul_le_mul_of_nonneg_left hbY hJ
      _ ≤ R * (KY * eps ^ 41) := mul_le_mul_of_nonneg_right hJR (by positivity)
      _ = _ := by ring
  have hinside : 4 * A * (∑' z : ℕ × ℕ × ℕ, X z) +
      684 * A * C ^ 3 * J * (∑' z : ℕ × ℕ × ℕ, Y z) ≤
      (4 * A * KX + 684 * A * C ^ 3 * KY) * eps ^ 41 * R := by
    have hx := mul_le_mul_of_nonneg_left hbX' (by positivity : 0 ≤ 4 * A)
    have hy := mul_le_mul_of_nonneg_left hbY' (by positivity : 0 ≤ 684 * A * C ^ 3)
    nlinarith only [hx, hy]
  have htail : T ≤ 9 * C ^ 2 * eps ^ 2 * B := by
    have h1 : 1 ≤ C * eps := one_le_mul_of_one_le_of_one_le hC he1
    have hwidth : 1 + C * (2 * eps) ≤ 3 * C * eps := by nlinarith only [h1]
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + C * (2 * eps)) hwidth 2
    exact (mul_le_mul_of_nonneg_right hp hB).trans_eq (by ring)
  calc
    _ ≤ T * ((4 * A * KX + 684 * A * C ^ 3 * KY) * eps ^ 41 * R) :=
      hsum.trans (mul_le_mul_of_nonneg_left hinside hT)
    _ ≤ (9 * C ^ 2 * eps ^ 2 * B) *
        ((4 * A * KX + 684 * A * C ^ 3 * KY) * eps ^ 41 * R) := by gcongr
    _ = B * K * eps ^ 43 * R := by dsimp [K]; ring

end

end PGM
