import PLAStochastic.Index.CEPS.Scaled.PairCoefficients
import PLAStochastic.Index.CEPS.Scaled.CutoffTailPower

/-! # Taylor-polynomial tails outside a physical drift cutoff -/

noncomputable section
open Complex Set Metric MeasureTheory Finset
namespace PGM

theorem cepsNorm_cutoff_tail_power_le_degree {u : ℂ} {K X E b δ : ℝ}
    (hK : 0 ≤ K) (hX : 0 ≤ X) (hE : 0 ≤ E) (hδ : 0 < δ)
    (hscale : δ ≤ b * X) (q : ℕ) (hu : ‖u‖ ≤ K * X ^ q * E) (n : ℕ) :
    ‖u‖ ≤ (K / δ ^ n) * b ^ n * X ^ (n + q) * E := by
  have hp := pow_le_pow_left₀ hδ.le hscale n
  have hco : K ≤ (K / δ ^ n) * b ^ n * X ^ n := by
    calc
      _ = (K / δ ^ n) * δ ^ n := (div_mul_cancel₀ K (pow_pos hδ n).ne').symm
      _ ≤ (K / δ ^ n) * (b * X) ^ n := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by rw [mul_pow]; ring
  apply hu.trans
  calc
    _ ≤ ((K / δ ^ n) * b ^ n * X ^ n) * X ^ q * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hco (pow_nonneg hX _)) hE
    _ = _ := by rw [pow_add]; ring

theorem cepsNorm_scaled_cutoff_tail_le {u : ℂ} {K X E b δ : ℝ}
    (hK : 0 ≤ K) (hX : 0 ≤ X) (hE : 0 ≤ E) (hb : 0 ≤ b) (hδ : 0 < δ)
    (hscale : δ ≤ b * X) (n j : ℕ) (hj : j ≤ n)
    (hu : ‖u‖ ≤ K * X ^ (j + 4) * E) :
    ‖(b : ℂ) ^ j * u‖ ≤ (K / δ ^ (n - j)) * b ^ n * X ^ (n + 4) * E := by
  have ht := cepsNorm_cutoff_tail_power_le_degree hK hX hE hδ hscale (j + 4) hu (n - j)
  rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  calc b ^ j * ‖u‖ ≤ b ^ j * ((K / δ ^ (n - j)) * b ^ (n - j) * X ^ (n - j + (j + 4)) * E) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by
      rw [show n - j + (j + 4) = n + 4 by omega]
      rw [show b ^ n = b ^ j * b ^ (n - j) by rw [← pow_add, Nat.add_sub_of_le hj]]
      ring

def CepsCanonDomain.pairCoeffBudgetConstant {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * dom.completePairConstant N M /
    (dom.completePairScaleBase N M / 2) ^ n

def CepsCanonDomain.cutoffPairTaylorBudgetConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M δ : ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * dom.completePairConstant N M /
    (dom.completePairScaleBase N M / 4) ^ n +
      ∑ j ∈ range n, dom.pairCoeffBudgetConstant N M j / δ ^ (n - j)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : WienerHopf.IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cutoffPairTaylorBudgetConstant_nonneg (N : ℕ) (M : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (n : ℕ) : 0 ≤ dom.cutoffPairTaylorBudgetConstant N M δ n := by
  have hK := completePairConstant_nonneg dom N M
  have hR := completePairScaleBase_pos dom hW hθ hD N M
  unfold CepsCanonDomain.cutoffPairTaylorBudgetConstant CepsCanonDomain.pairCoeffBudgetConstant
  positivity

include hW hθ hD in
theorem cepsScaledSurrogatePair_taylor_tail_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (n : ℕ) (lam : ℝ) (htail : δ ≤ b * (1 + |lam| + Real.sqrt ‖z‖)) :
    ‖complexTaylorSum (cepsScaledSurrogateSubtractedPair dom ρW N lam z) n 0 b‖ ≤
      (∑ j ∈ range n, dom.pairCoeffBudgetConstant N M j / δ ^ (n - j)) *
        b ^ n * (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 4) *
          Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hK := completePairConstant_nonneg dom N M
  have hR := completePairScaleBase_pos dom hW hθ hD N M
  unfold complexTaylorSum
  simp only [sub_zero]
  apply (norm_sum_le _ _).trans
  rw [sum_mul, sum_mul, sum_mul]
  refine sum_le_sum fun j hj => ?_
  have hco := cepsScaledSurrogatePairCoeff_norm_le dom hW hθ hD hf hη hM N hN hz j lam
  have ht := cepsNorm_scaled_cutoff_tail_le
    (show 0 ≤ dom.pairCoeffBudgetConstant N M j by
      unfold CepsCanonDomain.pairCoeffBudgetConstant; positivity)
    (show 0 ≤ 1 + |lam| + Real.sqrt ‖z‖ by positivity)
    (Real.exp_nonneg _) hb.le hδ htail n j (mem_range.mp hj).le hco
  simpa only [cepsScaledSurrogatePairCoeff, mul_left_comm, mul_assoc] using ht

end PGM
