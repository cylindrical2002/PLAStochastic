import PLAStochastic.Index.KEP.ReferenceScale.GraphWeightedLengthSeries

/-!
# Layer-uniform polynomial budgets for the actual weighted killed lengths

A fixed positive output exponent fits inside the killed spectral rate because
the actual segment mean is bounded below by a constant times tolerance squared.
The entire length sum then has an explicit polynomial tolerance budget.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepGraphMeanBracket : ℝ := cBr (bIn 1 1) (vIn 1 1)

theorem kepGraphMeanBracket_ge_one : 1 ≤ kepGraphMeanBracket :=
  one_le_cBr (bAbs_le_bIn 1 1)

theorem kepReference_graph_exponent_rate {κ theta eps : ℝ} (hκ : 0 < κ)
    (ht : 0 ≤ theta) (htcap : theta ≤ κ / (64 * kepGraphMeanBracket))
    (heps : kepReferenceClassicalThreshold ≤ eps) (j : ℕ) :
    let c := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
    let eta := 2 * theta / c
    let rate := κ / (2 * (2 * eps) ^ 2)
    0 < c ∧ 0 ≤ eta ∧ 0 < rate ∧ eta ≤ rate / 2 ∧
      Real.exp (eta * (2 * eps + 3)) ≤ Real.exp (10 * theta * kepGraphMeanBracket) := by
  let cb := kepGraphMeanBracket
  let c := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
  have hcb1 : 1 ≤ cb := kepGraphMeanBracket_ge_one
  have hcb : 0 < cb := by linarith
  have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have he : 0 < eps := by linarith
  have he2pos : 0 < eps ^ 2 := by positivity
  have hc : eps ^ 2 / cb ≤ c :=
    (segMean_bracket gapLaw_expCoord ((le_max_right _ _).trans heps) j).1
  have hcpos : 0 < c := (div_pos he2pos hcb).trans_le hc
  have heta : 2 * theta / c ≤ 2 * theta * cb / eps ^ 2 := by
    calc
      _ ≤ 2 * theta / (eps ^ 2 / cb) :=
        div_le_div_of_nonneg_left (by positivity) (div_pos he2pos hcb) hc
      _ = _ := by field_simp
  have hcap : 2 * theta * cb ≤ κ / 32 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 64 * cb)).mp htcap
    linarith
  refine ⟨hcpos, by positivity, by positivity, ?_, ?_⟩
  · calc
      2 * theta / c ≤ (κ / 32) / eps ^ 2 :=
        heta.trans (div_le_div_of_nonneg_right hcap he2pos.le)
      _ ≤ (κ / (2 * (2 * eps) ^ 2)) / 2 := by
        have hκ0 := hκ.le
        field_simp
        nlinarith
  · apply Real.exp_le_exp.mpr
    have hsize : 2 * eps + 3 ≤ 5 * eps ^ 2 := by nlinarith [sq_nonneg (eps - 1)]
    calc
      2 * theta / c * (2 * eps + 3) ≤ (2 * theta * cb / eps ^ 2) * (5 * eps ^ 2) := by gcongr
      _ = 10 * theta * cb := by field_simp; ring

theorem kepReference_killed_length_series_polynomial {κ theta : ℝ} (hκ : 0 < κ)
    (ht : 0 ≤ theta) (htcap : theta ≤ κ / (64 * kepGraphMeanBracket)) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ eps : ℝ, kepReferenceClassicalThreshold ≤ eps →
      ∀ j : ℕ,
      let c := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
      let rate := κ / (2 * (2 * eps) ^ 2)
      let F := fun k : ℕ => (2 * eps + (k : ℝ) + 1) ^ p *
        Real.exp (2 * theta * ((k : ℝ) + 2 * eps) / c) * Real.exp (-rate * k)
      Summable F ∧ (∑' k : ℕ, F k) ≤ K * eps ^ (3 * p + 2) := by
  let cb := kepGraphMeanBracket
  let K := Real.exp (10 * theta * cb) * 3 ^ p *
    ((p.factorial : ℝ) * Real.exp 1 * (1 + 32 / κ) ^ (p + 1))
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro eps heps j
  dsimp only
  let c := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
  let eta := 2 * theta / c
  let rate := κ / (2 * (2 * eps) ^ 2)
  obtain ⟨hc, heta, hr, hfit, hexp⟩ := kepReference_graph_exponent_rate hκ ht htcap heps j
  obtain ⟨hsF, hbF⟩ := kep_graph_length_series (w := 2 * eps) (r := rate)
    (eta := eta) (by linarith [(le_max_left _ _).trans heps] : 0 ≤ 2 * eps) hr hfit p
  have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have he : 0 < eps := by linarith
  have hweight : (fun k : ℕ => (2 * eps + (k : ℝ) + 1) ^ p *
      Real.exp (2 * theta * ((k : ℝ) + 2 * eps) / c) * Real.exp (-rate * k)) =
      (fun k : ℕ => (2 * eps + (k : ℝ) + 1) ^ p *
        Real.exp (eta * ((k : ℝ) + 2 * eps)) * Real.exp (-rate * k)) := by
    funext k
    rw [show 2 * theta * ((k : ℝ) + 2 * eps) / c = eta * ((k : ℝ) + 2 * eps) by
      dsimp [eta]
      ring]
  rw [hweight]
  refine ⟨hsF, hbF.trans ?_⟩
  have hexp' : Real.exp (eta * (2 * eps)) ≤ Real.exp (10 * theta * cb) := by
    apply (Real.exp_le_exp.mpr ?_).trans hexp
    nlinarith only [heta]
  have hwidth : 2 * eps + 1 ≤ 3 * eps := by linarith
  have hinv : 1 + 4 / rate ≤ (1 + 32 / κ) * eps ^ 2 := by
    have heq : 4 / rate = (32 / κ) * eps ^ 2 := by dsimp [rate]; field_simp; ring
    rw [heq]
    nlinarith [sq_nonneg (eps - 1)]
  calc
    _ ≤ Real.exp (10 * theta * cb) * (3 * eps) ^ p *
        ((p.factorial : ℝ) * Real.exp 1 * ((1 + 32 / κ) * eps ^ 2) ^ (p + 1)) := by gcongr
    _ = K * (eps ^ p * eps ^ (2 * (p + 1))) := by
      rw [mul_pow, mul_pow, ← pow_mul]
      dsimp [K]
      ring
    _ = _ := by rw [← pow_add, show p + 2 * (p + 1) = 3 * p + 2 by omega]

end

end PGM
