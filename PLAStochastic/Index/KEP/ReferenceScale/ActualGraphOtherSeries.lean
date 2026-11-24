import PLAStochastic.Index.KEP.ReferenceScale.ActualGraphHighestSeries

/-!
# The remaining graph coefficients are summable with a polynomial budget

All three lengths retain their killed decay. A cutoff shift proportional to
tolerance has bounded positive weight and cannot worsen this polynomial bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_graph_shifted_coefficients {κ theta eps : ℝ} (hκ : 0 < κ)
    (ht : 0 ≤ theta) (htcap : theta ≤ κ / (64 * kepGraphMeanBracket))
    (heps : kepReferenceClassicalThreshold ≤ eps) (j N : ℕ) (hNup : (N : ℝ) ≤ 7 * eps) :
    let mean := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
    let eta := 2 * theta / mean
    let rate := κ / (2 * (2 * eps) ^ 2)
    let W := 2 * eps + (N : ℝ) + 3
    Real.exp (eta * W) ≤ Real.exp (50 * theta * kepGraphMeanBracket) ∧
      W + 1 ≤ 11 * eps ∧
      1 + 2 / (rate - eta) ≤ (1 + 32 / κ) * eps ^ 2 := by
  obtain ⟨_, heta, hr, hfit, hexp⟩ := kepReference_graph_exponent_rate hκ ht htcap heps j
  have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
  let eta := 2 * theta / segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
  let rate := κ / (2 * (2 * eps) ^ 2)
  refine ⟨?_, by linarith, ?_⟩
  · apply Real.exp_le_exp.mpr
    have hh := Real.exp_le_exp.mp hexp
    have hw : 2 * eps + (N : ℝ) + 3 ≤ 5 * (2 * eps + 3) := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left hw heta, hh]
  · have hfit' : rate / 2 ≤ rate - eta := by linarith
    have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : 0 < rate / 2) hfit'
    have hepos : 0 < eps := by linarith
    have heq : 2 / (rate / 2) = (32 / κ) * eps ^ 2 := by dsimp [rate]; field_simp; ring
    rw [heq] at hdiv
    nlinarith [sq_nonneg (eps - 1)]

theorem kepReference_graph_other_series_polynomial {κ theta : ℝ} (hκ : 0 < κ)
    (ht : 0 ≤ theta) (htcap : theta ≤ κ / (64 * kepGraphMeanBracket)) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ eps : ℝ, kepReferenceClassicalThreshold ≤ eps →
      ∀ j N : ℕ, (N : ℝ) ≤ 7 * eps →
      let mean := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
      let rate := κ / (2 * (2 * eps) ^ 2)
      let F := fun z : ℕ × ℕ × ℕ =>
        (2 * eps + (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 1) ^ p *
        Real.exp (2 * theta * ((z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 2 * eps) / mean) *
        Real.exp (-rate * (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ))
      Summable F ∧ (∑' z : ℕ × ℕ × ℕ, F z) ≤ K * eps ^ (7 * p + 6) := by
  let D := (p.factorial : ℝ) * Real.exp 1 * (1 + 32 / κ) ^ (p + 1)
  let K := Real.exp (50 * theta * kepGraphMeanBracket) * 11 ^ p * D ^ 3
  refine ⟨K, by dsimp [K, D]; positivity, ?_⟩
  intro eps heps j N hNup
  dsimp only
  let mean := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
  let eta := 2 * theta / mean
  let rate := κ / (2 * (2 * eps) ^ 2)
  let W := 2 * eps + (N : ℝ) + 3
  let H := fun L : ℕ => Real.exp (-rate * L)
  let Q := fun L : ℕ => (L + 1 : ℝ) ^ p * Real.exp (eta * L) * H L
  let E := fun L : ℕ => (L + 1 : ℝ) ^ p * Real.exp (-(rate - eta) * L)
  obtain ⟨_, heta, hr, hfit, _⟩ := kepReference_graph_exponent_rate hκ ht htcap heps j
  have hr' : 0 < rate - eta := by linarith
  have hsE : Summable E := kep_summable_polynomial_exp hr' p
  have hQE : Q = E := by
    funext L
    dsimp [Q, H, E]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hsQ : Summable Q := hQE.symm ▸ hsE
  have hbQ : (∑' L : ℕ, Q L) ≤
      (p.factorial : ℝ) * Real.exp 1 * (1 + 2 / (rate - eta)) ^ (p + 1) := by
    rw [hQE]
    exact Real.tsum_polynomial_mul_exp_neg_le hr' p
  have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hW : 0 ≤ W := by dsimp [W]; positivity
  obtain ⟨hsG, hbG⟩ := kep_graph_triple_series hW (by linarith : eta < rate) p
    (fun L => (Real.exp_pos (-rate * L)).le) hsQ
  have hb (z : ℕ × ℕ × ℕ) :
      (2 * eps + (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 1) ^ p *
        Real.exp (2 * theta * ((z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 2 * eps) / mean) *
        Real.exp (-rate * (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ)) ≤
      (W + (z.1 + z.2.1 + z.2.2 : ℕ) + 1) ^ p *
        Real.exp (eta * ((z.1 + z.2.1 + z.2.2 : ℕ) + W)) * H z.2.2 *
        Real.exp (-rate * (z.1 + z.2.1 : ℕ)) := by
    have hlen : 2 * eps + (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 1 =
        W + (z.1 + z.2.1 + z.2.2 : ℕ) + 1 := by dsimp [W]; push_cast; ring
    have hex : 2 * theta * ((z.1 + z.2.1 + z.2.2 + N + 3 : ℕ) + 2 * eps) / mean =
        eta * ((z.1 + z.2.1 + z.2.2 : ℕ) + W) := by dsimp [eta, W]; push_cast; ring
    have hdec : -(rate * (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ)) ≤
        -rate * z.2.2 + -rate * (z.1 + z.2.1 : ℕ) := by
      push_cast
      nlinarith only [mul_nonneg hr.le (by positivity : 0 ≤ (N : ℝ) + 3)]
    have hdec' : Real.exp (-rate * (z.1 + z.2.1 + z.2.2 + N + 3 : ℕ)) ≤
        Real.exp (-rate * z.2.2) * Real.exp (-rate * (z.1 + z.2.1 : ℕ)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by simpa only [neg_mul] using hdec)
    rw [hlen, hex]
    dsimp only [H]
    exact (mul_le_mul_of_nonneg_left hdec' (by positivity : 0 ≤
      (W + (z.1 + z.2.1 + z.2.2 : ℕ) + 1) ^ p *
        Real.exp (eta * ((z.1 + z.2.1 + z.2.2 : ℕ) + W)))).trans_eq (by ring)
  have hsF := hsG.of_nonneg_of_le (fun z => by positivity) hb
  refine ⟨hsF, ?_⟩
  have htop := hsF.tsum_le_tsum hb hsG
  obtain ⟨hexpW, hwidth, hinv⟩ := kepReference_graph_shifted_coefficients hκ ht htcap heps j N hNup
  have hQ0 : 0 ≤ ∑' L : ℕ, Q L := tsum_nonneg (fun L => by dsimp [Q, H]; positivity)
  calc
    _ ≤ (Real.exp (eta * W) * (W + 1) ^ p) *
        ((p.factorial : ℝ) * Real.exp 1 * (1 + 2 / (rate - eta)) ^ (p + 1)) ^ 3 := by
      apply (htop.trans hbG).trans
      have hh := mul_le_mul_of_nonneg_left hbQ (by positivity : 0 ≤
        (Real.exp (eta * W) * (W + 1) ^ p) *
          ((p.factorial : ℝ) * Real.exp 1 * (1 + 2 / (rate - eta)) ^ (p + 1)) ^ 2)
      exact hh.trans_eq (by ring)
    _ ≤ (Real.exp (50 * theta * kepGraphMeanBracket) * (11 * eps) ^ p) *
        ((p.factorial : ℝ) * Real.exp 1 * (((1 + 32 / κ) * eps ^ 2) ^ (p + 1))) ^ 3 := by gcongr
    _ = K * (eps ^ p * eps ^ (6 * (p + 1))) := by
      rw [mul_pow, mul_pow, ← pow_mul]
      simp only [mul_pow, ← pow_mul]
      dsimp [K, D]
      ring
    _ = _ := by rw [← pow_add, show p + 6 * (p + 1) = 7 * p + 6 by omega]

end

end PGM
