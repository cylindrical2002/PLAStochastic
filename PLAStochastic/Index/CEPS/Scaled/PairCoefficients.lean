import PLAStochastic.Index.CEPS.Scaled.CompletePairTaylor
import PLAStochastic.Index.CEPS.Scaled.SurrogateCutoffPairMeasurability
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorCoefficientLimit
import PLAStochastic.ForMathlib.Analysis.Complex.Osgood

/-! # Measurable and integrable complete-pair scale coefficients -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogatePairCoeff {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N n : ℕ) (z : ℂ) (lam : ℝ) : ℂ :=
  (n.factorial : ℂ)⁻¹ *
    iteratedDeriv n (cepsScaledSurrogateSubtractedPair dom ρW N lam z) 0

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogatePairCoeff_aestronglyMeasurable {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    AEStronglyMeasurable (cepsScaledSurrogatePairCoeff dom ρW N n z) := by
  let B := dom.pairComparisonScaleBase N M
  let r := B / (8 * (1 + Real.sqrt ‖z‖))
  let δ := B / 8
  let b : ℕ → ℝ := fun i => r / (i + 1)
  have hB : 0 < B := pairComparisonScaleBase_pos dom hW hθ hD N
    ((cepsSobolev_nonneg m η fW).trans hM)
  have hr : 0 < r := by dsimp [r]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hb (i : ℕ) : 0 < b i := by dsimp [b]; positivity
  have hbr (i : ℕ) : b i ≤ r := by
    dsimp [b]
    exact div_le_self hr.le (by have := Nat.cast_nonneg (α := ℝ) i; linarith)
  obtain ⟨hne, hlim⟩ := tendsto_ofReal_div_succ hr
  have hlimR : Tendsto b atTop (𝓝 0) := by
    simpa only [Function.comp_def, ofReal_re, zero_re, b] using
      (continuous_re.tendsto 0).comp hlim
  unfold cepsScaledSurrogatePairCoeff
  apply aestronglyMeasurable_taylorCoefficients_of_samples
    (samples := fun i => cepsScaledSurrogateCutoffPair dom ρW N (b i) δ z) hne hlim
  · intro i
    apply cepsScaledSurrogateCutoffPair_aestronglyMeasurable dom hW hθ hD hf hη hM N hN (hb i)
      (show δ ≤ B / 4 by dsimp [δ]; linarith) hz
    calc b i * (1 + Real.sqrt ‖z‖) ≤ r * (1 + Real.sqrt ‖z‖) := by gcongr; exact hbr i
      _ = B / 8 := by dsimp [r]; field_simp
      _ < B / 4 := by linarith
  · intro lam
    have ht : Tendsto (fun i => b i * |lam|) atTop (𝓝 0) := by
      simpa using hlimR.mul_const |lam|
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with i hi
    have hc : |lam| ≤ δ / b i := (le_div_iff₀ (hb i)).mpr (by nlinarith)
    simp only [cepsScaledSurrogateCutoffPair, if_pos hc, b]
  · intro lam k
    let R := (dom.completePairScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖)) / 2
    have hR : 0 < R := by
      have := completePairScaleBase_pos dom hW hθ hD N M
      dsimp [R]; positivity
    refine ⟨dom.completePairTaylorBound N M (k + 1) lam z, ?_⟩
    filter_upwards [hlim.eventually (ball_mem_nhds (0 : ℂ) hR)] with i hi
    exact cepsScaledSurrogateSubtractedPair_complete_taylor_le dom hW hθ hD
      hf hη hM N (by omega) lam hz (k + 1) hi

include hW hθ hD in
theorem cepsScaledSurrogatePairCoeff_norm_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) (lam : ℝ) :
    ‖cepsScaledSurrogatePairCoeff dom ρW N n z lam‖ ≤
      dom.completePairScaleJetBound N M n lam z := by
  have hfac : ‖(n.factorial : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos n)
  unfold cepsScaledSurrogatePairCoeff
  rw [norm_mul]
  calc _ ≤ 1 * ‖iteratedDeriv n (cepsScaledSurrogateSubtractedPair dom ρW N lam z) 0‖ := by gcongr
    _ ≤ _ := by
      rw [one_mul]
      exact cepsScaledSurrogateSubtractedPair_complete_scale_jet_le dom hW hθ hD
        hf hη hM N hN lam hz n

include hW hθ hD in
theorem cepsScaledSurrogatePairCoeff_integrable {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    Integrable (cepsScaledSurrogatePairCoeff dom ρW N n z) := by
  have he : Integrable (fun lam : ℝ => dom.completePairScaleJetBound N M n lam z) :=
    cepsBridge_polynomialEnvelope_integrable (n + 4)
      (positiveEntranceBridge_constants dom hW hθ hD N M).2
      ((n.factorial : ℝ) * dom.completePairConstant N M /
        (dom.completePairScaleBase N M / 2) ^ n) z
  exact he.mono'
    (cepsScaledSurrogatePairCoeff_aestronglyMeasurable dom hW hθ hD hf hη hM N hN hz n)
    (ae_of_all _ fun lam => cepsScaledSurrogatePairCoeff_norm_le dom hW hθ hD
      hf hη hM N (by omega) hz n lam)

end PGM
