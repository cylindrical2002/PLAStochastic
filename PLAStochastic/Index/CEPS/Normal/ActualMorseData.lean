import PLAStochastic.Index.CEPS.Normal.ActualQuotientDisc
import PLAStochastic.Index.CEPS.Normal.ActualBudget
import PLAStochastic.Index.CEPS.Normal.Symmetry

/-! # Actual normal data in the signed Morse coordinate -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

/-- The discount corresponding to the signed Morse coordinate. -/
def cepsMorseDiscount (D θ : ℝ) (ρW : Measure ℝ) (μ r : ℂ) : ℂ :=
  cepsMorseMin D θ ρW μ + r ^ 2

/-- Canonical normal data retaining the globally defined removed quotient. -/
def cepsWHNormalData (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : CepsNormalData where
  βp := cepsRootPlus D θ ρW μ q
  βm := cepsRootMinus D θ ρW μ q
  d := cepsD ρW μ q
  Q := cepsQ D θ ρW μ q
  ψp := deriv (cepsCgfShift ρW μ) (cepsRootPlus D θ ρW μ q)
  ψm := deriv (cepsCgfShift ρW μ) (cepsRootMinus D θ ρW μ q)

/-- The signed chart version of the same data, before choosing a square root. -/
def cepsMorseNormalData (D θ : ℝ) (ρW : Measure ℝ) (μ r : ℂ) : CepsNormalData where
  βp := cepsMorseRoot D θ ρW μ r
  βm := cepsMorseRoot D θ ρW μ (-r)
  d := cepsD ρW μ (cepsMorseDiscount D θ ρW μ r)
  Q := cepsQ D θ ρW μ (cepsMorseDiscount D θ ρW μ r)
  ψp := deriv (cepsCgfShift ρW μ) (cepsMorseRoot D θ ρW μ r)
  ψm := deriv (cepsCgfShift ρW μ) (cepsMorseRoot D θ ρW μ (-r))

theorem cepsMorseDiscount_neg (D θ : ℝ) (ρW : Measure ℝ) (μ r : ℂ) :
    cepsMorseDiscount D θ ρW μ (-r) = cepsMorseDiscount D θ ρW μ r := by
  unfold cepsMorseDiscount; rw [neg_sq]

theorem cepsMorseNormalData_neg (D θ : ℝ) (ρW : Measure ℝ) (μ r : ℂ) :
    cepsMorseNormalData D θ ρW μ (-r) = (cepsMorseNormalData D θ ρW μ r).swapRoots := by
  simp only [cepsMorseNormalData, CepsNormalData.swapRoots, neg_neg, cepsMorseDiscount_neg]

theorem cepsMorseNormalData_sqrt_eq (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) :
    cepsMorseNormalData D θ ρW μ (Complex.sqrt (q - cepsMorseMin D θ ρW μ)) =
      cepsWHNormalData D θ ρW μ q := by
  have hq : cepsMorseDiscount D θ ρW μ (Complex.sqrt (q - cepsMorseMin D θ ρW μ)) = q := by
    unfold cepsMorseDiscount; rw [sqrt_sq_eq]; ring
  simp only [cepsMorseNormalData, cepsWHNormalData, hq,
    cepsRootPlus, cepsRootMinus, cepsRootR]

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMorseMin_norm_le_class {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) :
    ‖cepsMorseMin D θ ρW μ‖ ≤ dom.rmax ^ 2 / 4 := by
  have hμc := dom.μ_lt_chart hμ
  have hm := norm_cepsMorseMin_le hW hθ hD hμc
  have hb := norm_cepsMorseCenter_le hW hθ hD hμc
  have hvW := cepsVarLo_le hW hθ hD
  have hvl := cepsVarLo_pos hD
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hb' : ‖cepsMorseCenter D θ ρW μ‖ ≤ dom.rmax / (2 * (v + 1)) := by
    calc
      _ ≤ 2 * ‖μ‖ / cepsStepVar ρW := hb
      _ ≤ 2 * dom.μ₀ / cepsVarLo D :=
        div_le_div₀ (by linarith [dom.μ₀_pos]) (by linarith) hvl hvW
      _ ≤ dom.rmax / (2 * (v + 1)) := by
        rw [div_le_div_iff₀ hvl (by positivity)]; nlinarith [dom.μ₀_r]
  calc
    _ ≤ v * (dom.rmax / (2 * (v + 1))) ^ 2 :=
      hm.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb' 2) hv.le)
    _ ≤ dom.rmax ^ 2 / 4 := by
      rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [sq_nonneg dom.rmax, sq_nonneg v]

include hW hθ hD in
theorem cepsMorseDiscount_norm_lt {μ r : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hr : ‖r‖ < dom.rmax / 4) : ‖cepsMorseDiscount D θ ρW μ r‖ < dom.q₀ := by
  have hm := cepsMorseMin_norm_le_class dom hW hθ hD hμ
  have hsq : ‖r‖ ^ 2 < (dom.rmax / 4) ^ 2 :=
    pow_lt_pow_left₀ hr (norm_nonneg _) (by norm_num)
  have hn := norm_add_le (cepsMorseMin D θ ρW μ) (r ^ 2)
  rw [norm_pow] at hn
  unfold cepsMorseDiscount
  rw [dom.q₀_def]
  nlinarith [sq_pos_of_pos dom.rmax_pos]

end PGM
