import PLAStochastic.Index.KEP.ReferenceScale.ActualKilledGraphSeries

/-!
# Summing the original second spatial kernel over every exterior length

The actual long-kernel budget is combined with both exterior killed series.
The cutoff is proportional to tolerance and all constants precede the layer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_graph_highest_series_polynomial {κ : ℝ} (hκ : 0 < κ) :
    ∃ theta c eps0 : ℝ, 0 < theta ∧ theta ≤ κ / (64 * kepGraphMeanBracket) ∧
      0 < c ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ p : ℕ, ∃ K : ℝ, 0 < K ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ N : ℕ,
          8 ≤ N → eps ≤ (N / 2 : ℕ) → (N : ℝ) ≤ 7 * eps →
          let f := (kepReferenceDensity heps hj).density
          let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
          let mean := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
          let rate := κ / (2 * (2 * eps) ^ 2)
          let F := fun z : ℕ × ℕ × ℕ =>
            (2 * eps + (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 1) ^ p *
            Real.exp (2 * theta * ((z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 2 * eps) / mean) *
            kepLogSlopeNorm (fun s => kepFixedBridgeRight (kepLogStep f 1)
              (kepLogStepSecond f'' 1) (2 * eps) s (z.2.2 + N + 2) 0 (2 * eps)) *
            Real.exp (-rate * (z.1 + z.2.1 : ℕ))
          Summable F ∧ (∑' z : ℕ × ℕ × ℕ, F z) ≤
            K * eps ^ (7 * p + 8) *
              (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
                Real.exp (-c * eps) * kepReferenceSecondNorm eps j) := by
  obtain ⟨t0, c, e0, ht0, hc, he0, hlong⟩ := kepReference_second_graph_kernel_polynomial_budget
  let theta := min t0 (κ / (64 * kepGraphMeanBracket))
  have hcb : 0 < kepGraphMeanBracket := by linarith [kepGraphMeanBracket_ge_one]
  have ht : 0 < theta := lt_min ht0 (by positivity)
  have htcap : theta ≤ κ / (64 * kepGraphMeanBracket) := min_le_right _ _
  have htt0 : theta ≤ t0 := min_le_left _ _
  refine ⟨theta, c, e0, ht, htcap, hc, he0, ?_⟩
  intro p
  obtain ⟨K0, hK0, hlongp⟩ := hlong p
  let D := (p.factorial : ℝ) * Real.exp 1 * (1 + 32 / κ) ^ (p + 1)
  let K := Real.exp (50 * theta * kepGraphMeanBracket) * 11 ^ p * D ^ 2 * K0
  refine ⟨K, by dsimp [K, D]; positivity, ?_⟩
  intro eps he heps j hj N hN hcut hNup
  dsimp only
  let f := (kepReferenceDensity heps hj).density
  let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let mean := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
  let eta := 2 * theta / mean
  let rate := κ / (2 * (2 * eps) ^ 2)
  let W := 2 * eps + (N : ℝ) + 3
  let H := fun L : ℕ => kepLogSlopeNorm (fun s => kepFixedBridgeRight (kepLogStep f 1)
    (kepLogStepSecond f'' 1) (2 * eps) s (L + N + 2) 0 (2 * eps))
  let Q := fun L : ℕ => (L + 1 : ℝ) ^ p * Real.exp (eta * L) * H L
  let Q0 := fun L : ℕ => (L + N + 1 : ℝ) ^ p * Real.exp (2 * t0 * (L + N) / mean) * H L
  obtain ⟨hcmean, heta, hr, hfit, hexp⟩ := kepReference_graph_exponent_rate hκ ht.le htcap heps j
  obtain ⟨hs0, hb0⟩ := hlongp eps he heps j hj 1 (Or.inl rfl) 0 N hN hcut 0 (2 * eps)
    (Or.inl rfl) (Or.inr rfl)
  simp only [zero_add] at hs0 hb0
  have hQ (L : ℕ) : Q L ≤ Q0 L := by
    have he : eta * L ≤ 2 * t0 * (L + N) / mean := by
      dsimp [eta]
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hcmean.le
      nlinarith only [mul_le_mul_of_nonneg_right htt0 (Nat.cast_nonneg L),
        mul_nonneg ht0.le (Nat.cast_nonneg N)]
    dsimp [Q, Q0]
    gcongr
    · exact kepLogSlopeNorm_nonneg _
    · exact_mod_cast Nat.le_add_right L N
  have hsQ := hs0.of_nonneg_of_le (fun L => mul_nonneg (by positivity) (kepLogSlopeNorm_nonneg _)) hQ
  have hbQ : (∑' L : ℕ, Q L) ≤ K0 * eps ^ (2 * p + 4) *
      (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
        Real.exp (-c * eps) * kepReferenceSecondNorm eps j) :=
    (hsQ.tsum_le_tsum hQ hs0).trans hb0
  have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hepos : 0 < eps := by linarith
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hgap : 0 < rate - eta := by linarith
  obtain ⟨hsF, hbF⟩ := kep_graph_triple_series hW (by linarith : eta < rate) p
    (fun L => kepLogSlopeNorm_nonneg _) hsQ
  have hform : (fun z : ℕ × ℕ × ℕ =>
      (2 * eps + (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 1) ^ p *
      Real.exp (2 * theta * ((z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 2 * eps) / mean) *
      H z.2.2 * Real.exp (-rate * (z.1 + z.2.1 : ℕ))) =
      (fun z : ℕ × ℕ × ℕ => (W + (z.1 + z.2.1 + z.2.2 : ℕ) + 1) ^ p *
        Real.exp (eta * ((z.1 + z.2.1 + z.2.2 : ℕ) + W)) *
        H z.2.2 * Real.exp (-rate * (z.1 + z.2.1 : ℕ))) := by
    funext z
    have hlen : 2 * eps + (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 1 =
        W + (z.1 + z.2.1 + z.2.2 : ℕ) + 1 := by dsimp [W]; push_cast; ring
    have hex : 2 * theta * ((z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 2 * eps) / mean =
        eta * ((z.1 + z.2.1 + z.2.2 : ℕ) + W) := by dsimp [eta, W]; push_cast; ring
    rw [hlen, hex]
  rw [hform]
  refine ⟨hsF, hbF.trans ?_⟩
  have hwidth : W + 1 ≤ 11 * eps := by dsimp [W]; linarith
  have hW5 : W ≤ 5 * (2 * eps + 3) := by dsimp [W]; linarith
  have hexpW : Real.exp (eta * W) ≤ Real.exp (50 * theta * kepGraphMeanBracket) := by
    apply Real.exp_le_exp.mpr
    have hh := Real.exp_le_exp.mp hexp
    nlinarith only [mul_le_mul_of_nonneg_left hW5 heta, hh]
  have hinv : 1 + 2 / (rate - eta) ≤ (1 + 32 / κ) * eps ^ 2 := by
    have hfit' : rate / 2 ≤ rate - eta := by linarith
    have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : 0 < rate / 2) hfit'
    have heq : 2 / (rate / 2) = (32 / κ) * eps ^ 2 := by dsimp [rate]; field_simp; ring
    rw [heq] at hdiv
    nlinarith [sq_nonneg (eps - 1)]
  have hQ0 : 0 ≤ ∑' L : ℕ, Q L := tsum_nonneg (fun L => mul_nonneg (by positivity) (kepLogSlopeNorm_nonneg _))
  have hJ0 := kepReferenceSecondNorm_nonneg eps j
  calc
    _ ≤ (Real.exp (50 * theta * kepGraphMeanBracket) * (11 * eps) ^ p) *
        ((p.factorial : ℝ) * Real.exp 1 * (((1 + 32 / κ) * eps ^ 2) ^ (p + 1))) ^ 2 *
        (K0 * eps ^ (2 * p + 4) *
          (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
            Real.exp (-c * eps) * kepReferenceSecondNorm eps j)) := by gcongr
    _ = K * (eps ^ p * eps ^ (4 * (p + 1)) * eps ^ (2 * p + 4)) *
        (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
          Real.exp (-c * eps) * kepReferenceSecondNorm eps j) := by
      rw [mul_pow, mul_pow, ← pow_mul]
      simp only [mul_pow, ← pow_mul]
      dsimp [K, D]
      ring
    _ = _ := by
      rw [← pow_add, ← pow_add,
        show p + 4 * (p + 1) + (2 * p + 4) = 7 * p + 8 by omega]

end

end PGM
