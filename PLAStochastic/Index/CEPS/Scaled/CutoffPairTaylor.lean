import PLAStochastic.Index.CEPS.Scaled.CutoffTaylorTail
import PLAStochastic.Index.CEPS.Scaled.PolynomialEnvelopeIntegral

/-! # Complete surrogate cutoff integrals and their genuine Taylor coefficients -/

noncomputable section
open Complex Set Metric MeasureTheory Finset
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogatePairIntegralCoeff {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N n : ℕ) (z : ℂ) : ℂ :=
  ∫ lam : ℝ, cepsScaledSurrogatePairCoeff dom ρW N n z lam

def CepsCanonDomain.cutoffPairTaylorIntegralConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M δ : ℝ) (n : ℕ) : ℝ :=
  dom.cutoffPairTaylorBudgetConstant N M δ n *
    ∫ lam : ℝ, (1 + |lam|) ^ (n + 4) *
      Real.exp (-dom.positiveEntranceBridgeDecayRate * |lam|)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateCutoffPair_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (hδR : δ ≤ dom.completePairScaleBase N M / 4)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.completePairScaleBase N M / 4)
    (n : ℕ) (lam : ℝ) :
    ‖cepsScaledSurrogateCutoffPair dom ρW N b δ z lam -
        complexTaylorSum (cepsScaledSurrogateSubtractedPair dom ρW N lam z) n 0 b‖ ≤
      dom.cutoffPairTaylorBudgetConstant N M δ n * b ^ n *
        (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 4) *
          Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hK := completePairConstant_nonneg dom N M
  have hR := completePairScaleBase_pos dom hW hθ hD N M
  have hsum : 0 ≤ ∑ j ∈ range n, dom.pairCoeffBudgetConstant N M j / δ ^ (n - j) := by
    apply sum_nonneg
    intro j _
    unfold CepsCanonDomain.pairCoeffBudgetConstant
    positivity
  unfold cepsScaledSurrogateCutoffPair
  by_cases hc : |lam| ≤ δ / b
  · rw [if_pos hc]
    have hscale : (b : ℂ) ∈ ball (0 : ℂ)
        ((dom.completePairScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)) / 2) := by
      rw [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos hb]
      have hbl : b * |lam| ≤ δ := by
        have := (le_div_iff₀ hb).mp hc
        nlinarith
      rw [div_div, lt_div_iff₀ (by positivity)]
      nlinarith
    have ht := cepsScaledSurrogateSubtractedPair_complete_taylor_le dom hW hθ hD
      hf hη hM N hN lam hz n hscale
    simp only [norm_real, Real.norm_eq_abs, abs_of_pos hb] at ht
    apply ht.trans
    unfold CepsCanonDomain.completePairTaylorBound CepsCanonDomain.cutoffPairTaylorBudgetConstant
    rw [show ((n.factorial : ℝ) * dom.completePairConstant N M /
      (dom.completePairScaleBase N M / 4) ^ n) *
      (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 4) *
      Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) * b ^ n =
      ((n.factorial : ℝ) * dom.completePairConstant N M /
      (dom.completePairScaleBase N M / 4) ^ n) * b ^ n *
      (1 + |lam| + Real.sqrt ‖z‖) ^ (n + 4) *
      Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) by ring]
    gcongr
    exact le_add_of_nonneg_right hsum
  · rw [if_neg hc, zero_sub, norm_neg]
    have htail : δ ≤ b * (1 + |lam| + Real.sqrt ‖z‖) := by
      have hl : δ < |lam| * b := (div_lt_iff₀ hb).mp (lt_of_not_ge hc)
      have hs := Real.sqrt_nonneg ‖z‖
      nlinarith
    apply (cepsScaledSurrogatePair_taylor_tail_le dom hW hθ hD hf hη hM N hN hz hb hδ n lam htail).trans
    unfold CepsCanonDomain.cutoffPairTaylorBudgetConstant
    gcongr
    exact le_add_of_nonneg_left (by positivity)

include hW hθ hD in
theorem cepsScaledSurrogatePair_taylorSum_integrable {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) (b : ℂ) :
    Integrable (fun lam : ℝ =>
      complexTaylorSum (cepsScaledSurrogateSubtractedPair dom ρW N lam z) n 0 b) := by
  have hi := integrable_finsetSum (range n) (fun j _ =>
    (cepsScaledSurrogatePairCoeff_integrable dom hW hθ hD hf hη hM N hN hz j).const_mul (b ^ j))
  have he : (fun lam : ℝ =>
      complexTaylorSum (cepsScaledSurrogateSubtractedPair dom ρW N lam z) n 0 b) =
      fun lam => ∑ j ∈ range n, b ^ j * cepsScaledSurrogatePairCoeff dom ρW N j z lam := by
    ext lam
    unfold complexTaylorSum cepsScaledSurrogatePairCoeff
    simp only [sub_zero]
    apply sum_congr rfl
    intro j _
    ring
  rw [he]
  exact hi

include hW hθ hD in
theorem cepsScaledSurrogateCutoffPair_integral_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (hδR : δ ≤ dom.completePairScaleBase N M / 4)
    (hδB : δ ≤ dom.pairComparisonScaleBase N M / 4)
    (hbzR : b * (1 + Real.sqrt ‖z‖) < dom.completePairScaleBase N M / 4)
    (hbzB : b * (1 + Real.sqrt ‖z‖) < dom.pairComparisonScaleBase N M / 4)
    (n : ℕ) :
    Integrable (cepsScaledSurrogateCutoffPair dom ρW N b δ z) ∧
      ‖(∫ lam : ℝ, cepsScaledSurrogateCutoffPair dom ρW N b δ z lam) -
        ∑ j ∈ range n, (b : ℂ) ^ j * cepsScaledSurrogatePairIntegralCoeff dom ρW N j z‖ ≤
          dom.cutoffPairTaylorIntegralConstant N M δ n * b ^ n *
            (1 + Real.sqrt ‖z‖) ^ (n + 4) *
              Real.exp (-dom.positiveEntranceBridgeDecayRate * Real.sqrt ‖z‖) := by
  let T : ℝ → ℂ := fun lam =>
    complexTaylorSum (cepsScaledSurrogateSubtractedPair dom ρW N lam z) n 0 b
  have hiT : Integrable T := cepsScaledSurrogatePair_taylorSum_integrable dom hW hθ hD
    hf hη hM N hN hz n b
  have hm := (cepsScaledSurrogateCutoffPair_aestronglyMeasurable dom hW hθ hD
    hf hη hM N hN hb hδB hz hbzB).sub hiT.aestronglyMeasurable
  have hK := cutoffPairTaylorBudgetConstant_nonneg dom hW hθ hD N M hδ n
  obtain ⟨hiE, hE⟩ := cepsScaled_integral_norm_le_of_envelope (n + 4)
    (positiveEntranceBridge_constants dom hW hθ hD N M).2
    (show 0 ≤ dom.cutoffPairTaylorBudgetConstant N M δ n * b ^ n by positivity) z hm
    (fun lam => (cepsScaledSurrogateCutoffPair_taylor_le dom hW hθ hD
      hf hη hM N (by omega) hz hb hδ hδR hbzR n lam))
  have hi : Integrable (cepsScaledSurrogateCutoffPair dom ρW N b δ z) := by
    simpa only [Pi.add_apply, Pi.sub_apply, sub_add_cancel] using! hiE.add hiT
  have hT : (∫ lam : ℝ, T lam) =
      ∑ j ∈ range n, (b : ℂ) ^ j * cepsScaledSurrogatePairIntegralCoeff dom ρW N j z := by
    have he : T = fun lam => ∑ j ∈ range n, (b : ℂ) ^ j * cepsScaledSurrogatePairCoeff dom ρW N j z lam := by
      ext lam
      unfold T complexTaylorSum cepsScaledSurrogatePairCoeff
      simp only [sub_zero]
      apply sum_congr rfl
      intro j _
      ring
    rw [he, integral_finsetSum (range n) (fun j _ =>
      (cepsScaledSurrogatePairCoeff_integrable dom hW hθ hD hf hη hM N hN hz j).const_mul ((b : ℂ) ^ j))]
    simp only [integral_const_mul, cepsScaledSurrogatePairIntegralCoeff]
  refine ⟨hi, ?_⟩
  rw [← hT, ← integral_sub hi hiT]
  exact hE.trans_eq (by unfold CepsCanonDomain.cutoffPairTaylorIntegralConstant; ring)

end PGM
