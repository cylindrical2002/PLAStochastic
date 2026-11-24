import PLAStochastic.Index.CEPS.Scaled.PositivePairErrorConstants

/-! # Entrance profiles for the positive-tail complete-pair Taylor error -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledPositive_error_decay_le (M lam : ℝ) (z : ℂ) :
    Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) ≤
      Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2) := by
  have hc := (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
  have hr : dom.negativeBridgeDecayRate = 2 * dom.positiveBridgeDecayRate := by
    unfold CepsCanonDomain.negativeBridgeDecayRate CepsCanonDomain.positiveBridgeDecayRate
    ring
  apply Real.exp_le_exp.mpr
  rw [hr]
  nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]

include hW hθ hD in
theorem cepsScaledPositivePair_entrance_norm_profile {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z)) :
    let L := dom.positivePairComparisonConstant (N + 1) M
    let X := 1 + |lam| + Real.sqrt ‖z‖
    let E := Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)
    let H := cepsScaledTrueEntrance dom ρW lam z b
    let h := cepsScaledSurrogateEntrance dom ρW (N + 1) lam z b
    let Hh := cepsScaledTrueHalfEntrance dom ρW lam z b
    let hh := cepsScaledSurrogateHalfEntrance dom ρW (N + 1) lam z b
    ‖H‖ ≤ L * X ∧ ‖h‖ ≤ L * X ∧ ‖H + Hh‖ ≤ L * X ∧ ‖h + hh‖ ≤ L * X ∧
    ‖h - hh‖ ≤ L * X * E := by
  let L := dom.positivePairComparisonConstant (N + 1) M
  let K := dom.positiveEntranceErrorConstant (N + 1) M
  let KE := dom.entranceComparisonConstant (N + 1) M
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let E := Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)
  let e := Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖))
  let mu := |b * lam| ^ (N + 2)
  let H := cepsScaledTrueEntrance dom ρW lam z b
  let h := cepsScaledSurrogateEntrance dom ρW (N + 1) lam z b
  let Hh := cepsScaledTrueHalfEntrance dom ρW lam z b
  let hh := cepsScaledSurrogateHalfEntrance dom ρW (N + 1) lam z b
  have hK : 0 ≤ K := (positiveEntranceErrorConstant_pos dom (N + 1) M).le
  have hKE : 0 ≤ KE := by dsimp [KE, CepsCanonDomain.entranceComparisonConstant]; positivity
  have hX1 : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hX : 0 ≤ X := zero_le_one.trans hX1
  have hbound : ∀ c ∈ dom.positivePairErrorConstants (N + 1) M, c ≤ L :=
    fun _ hc => positivePairComparisonConstant_le dom (N + 1) M hc
  have hEL : e ≤ E := cepsScaledPositive_error_decay_le dom hW hθ hD M lam z
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have hmu : mu ≤ 1 := pow_le_one₀ (abs_nonneg _)
    (cepsScaledTrueScale_drift_le_one dom hW hθ hD M lam hz.symm.le hbD)
  obtain ⟨hH, hh0, _⟩ := cepsScaledEntrance_imaginary_comparison_profile dom hW hθ hD hf hη hM
    (N + 1) (by omega) lam hz hb hbs hbN
  obtain ⟨hHh, hhh, _⟩ := cepsScaledHalfEntrance_positive_comparison_profile dom hW hθ hD hf hη hM
    (N + 1) (by omega) lam hlam hz.symm.le hb hbs hbN
  have hHnorm : ‖H‖ ≤ L * X := hH.trans (mul_le_mul_of_nonneg_right
    (hbound _ (by simp [CepsCanonDomain.positivePairErrorConstants])) hX)
  have hhnorm : ‖h‖ ≤ L * X := hh0.trans (mul_le_mul_of_nonneg_right
    (hbound _ (by simp [CepsCanonDomain.positivePairErrorConstants])) hX)
  have hplusT : ‖H + Hh‖ ≤ (KE + 2 * K) * X :=
    (norm_add_le _ _).trans ((add_le_add hH hHh).trans (by nlinarith))
  have hplusS : ‖h + hh‖ ≤ (KE + 2 * K) * X :=
    (norm_add_le _ _).trans ((add_le_add hh0 hhh).trans (by nlinarith))
  have hplusT' := hplusT.trans (mul_le_mul_of_nonneg_right
    (hbound _ (by dsimp only [K, KE]; simp [CepsCanonDomain.positivePairErrorConstants])) hX)
  have hplusS' := hplusS.trans (mul_le_mul_of_nonneg_right
    (hbound _ (by dsimp only [K, KE]; simp [CepsCanonDomain.positivePairErrorConstants])) hX)
  have hCorrT := cepsScaledTrueEntranceCorrection_positive_imaginary_budget dom hW hθ hD hf hη hM
    (by omega) lam hlam hz hb hbs
  have hCorr : ‖H - Hh‖ ≤ 2 * K * X * e := hCorrT.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (positiveEntranceErrorConstant_le dom (N + 1) M (by simp [CepsCanonDomain.positiveEntranceErrorConstants])) (by norm_num)) hX)
        (Real.exp_pos _).le)
  have hCorrErr := cepsScaledTrueEntranceCorrection_imaginary_error_budget dom hW hθ hD hf hη hM
    (N + 1) (by omega) lam hlam hz hb hbs hbN
  have hCE : ‖(H - Hh) - (h - hh)‖ ≤ 14 * K ^ 3 * X * e * mu := hCorrErr
  have hCE1 : ‖(H - Hh) - (h - hh)‖ ≤ 14 * K ^ 3 * X * e :=
    hCE.trans (mul_le_of_le_one_right (by positivity) hmu)
  have hCS : ‖h - hh‖ ≤ (2 * K + 14 * K ^ 3) * X * e := by
    have hn := norm_sub_le (H - Hh) ((H - Hh) - (h - hh))
    rw [sub_sub_cancel] at hn
    exact hn.trans ((add_le_add hCorr hCE1).trans_eq (by ring))
  have hCS' : ‖h - hh‖ ≤ L * X * E := hCS.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (hbound _ (by dsimp only [K, KE]; simp [CepsCanonDomain.positivePairErrorConstants])) hX)
      hEL (Real.exp_pos _).le (by have := positivePairComparisonConstant_pos dom (N + 1) M; positivity))
  exact ⟨hHnorm, hhnorm, hplusT', hplusS', hCS'⟩

include hW hθ hD in
theorem cepsScaledPositivePair_entrance_taylor_profile {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z)) :
    let L := dom.positivePairComparisonConstant (N + 1) M
    let X := 1 + |lam| + Real.sqrt ‖z‖
    let beta := b ^ (N + 2)
    let E := Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)
    let H := cepsScaledTrueEntrance dom ρW lam z b
    let h := cepsScaledSurrogateEntrance dom ρW (N + 1) lam z b
    let Hh := cepsScaledTrueHalfEntrance dom ρW lam z b
    let hh := cepsScaledSurrogateHalfEntrance dom ρW (N + 1) lam z b
    ‖H - h‖ ≤ L * beta * X ^ (N + 3) ∧
    ‖(H + Hh) - (h + hh)‖ ≤ L * beta * X ^ (N + 3) ∧
    ‖(H - Hh) - (h - hh)‖ ≤ L * beta * X ^ (N + 3) * E := by
  let L := dom.positivePairComparisonConstant (N + 1) M
  let K := dom.positiveEntranceErrorConstant (N + 1) M
  let KE := dom.entranceComparisonConstant (N + 1) M
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let beta := b ^ (N + 2)
  let E := Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)
  let e := Real.exp (-dom.negativeBridgeDecayRate * (|lam| + Real.sqrt ‖z‖))
  let mu := |b * lam| ^ (N + 2)
  let H := cepsScaledTrueEntrance dom ρW lam z b
  let h := cepsScaledSurrogateEntrance dom ρW (N + 1) lam z b
  let Hh := cepsScaledTrueHalfEntrance dom ρW lam z b
  let hh := cepsScaledSurrogateHalfEntrance dom ρW (N + 1) lam z b
  have hK : 0 ≤ K := (positiveEntranceErrorConstant_pos dom (N + 1) M).le
  have hKE : 0 ≤ KE := by dsimp [KE, CepsCanonDomain.entranceComparisonConstant]; positivity
  have hX1 : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hX : 0 ≤ X := zero_le_one.trans hX1
  have hbe : 0 ≤ beta := pow_nonneg hb.le _
  have hbound : ∀ c ∈ dom.positivePairErrorConstants (N + 1) M, c ≤ L :=
    fun _ hc => positivePairComparisonConstant_le dom (N + 1) M hc
  have hEL : e ≤ E := cepsScaledPositive_error_decay_le dom hW hθ hD M lam z
  obtain ⟨_, _, hHerr⟩ := cepsScaledEntrance_imaginary_comparison_profile dom hW hθ hD hf hη hM
    (N + 1) (by omega) lam hz hb hbs hbN
  obtain ⟨_, _, hHherr⟩ := cepsScaledHalfEntrance_positive_comparison_profile dom hW hθ hD hf hη hM
    (N + 1) (by omega) lam hlam hz.symm.le hb hbs hbN
  have hHT := cepsDrift_taylor_value_budget (lam := lam) (X := X) (N + 2) hb.le hKE
    (by norm_num : (0 : ℝ) ≤ 1) (by dsimp [X]; linarith [Real.sqrt_nonneg ‖z‖])
      (by simpa only [mul_one] using hHerr)
  simp only [mul_one] at hHT
  have hHalfRaw : ‖Hh - hh‖ ≤ K * X * mu := hHherr.trans
    (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK hX1) (pow_nonneg (abs_nonneg _) _))
  have hHalfT := cepsDrift_taylor_value_budget (lam := lam) (X := X) (N + 2) hb.le hK
    (by norm_num : (0 : ℝ) ≤ 1) (by dsimp [X]; linarith [Real.sqrt_nonneg ‖z‖])
      (by simpa only [mul_one] using hHalfRaw)
  simp only [mul_one] at hHalfT
  have hHT' := hHT.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (hbound _ (by dsimp only [K, KE]; simp [CepsCanonDomain.positivePairErrorConstants])) hbe) (pow_nonneg hX _))
  have hplusErr : ‖(H + Hh) - (h + hh)‖ ≤ L * beta * X ^ (N + 3) := by
    rw [show (H + Hh) - (h + hh) = (H - h) + (Hh - hh) by ring]
    apply (norm_add_le _ _).trans ((add_le_add hHT hHalfT).trans _)
    have hcoef : KE + K ≤ L := (by linarith : KE + K ≤ KE + 2 * K).trans
      (hbound _ (by dsimp only [K, KE]; simp [CepsCanonDomain.positivePairErrorConstants]))
    calc
      _ = (KE + K) * beta * X ^ (N + 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hbe) (pow_nonneg hX _)
  have hCorrErr := cepsScaledTrueEntranceCorrection_imaginary_error_budget dom hW hθ hD hf hη hM
    (N + 1) (by omega) lam hlam hz hb hbs hbN
  have hCE : ‖(H - Hh) - (h - hh)‖ ≤ 14 * K ^ 3 * X * e * mu := hCorrErr
  have hCET := cepsDrift_taylor_value_budget (lam := lam) (X := X) (N + 2) hb.le (by positivity)
    (Real.exp_pos _).le (by dsimp [X]; linarith [Real.sqrt_nonneg ‖z‖]) hCE
  have hCET' : ‖(H - Hh) - (h - hh)‖ ≤ L * beta * X ^ (N + 3) * E := hCET.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (hbound _ (by dsimp only [K, KE]; simp [CepsCanonDomain.positivePairErrorConstants])) hbe) (pow_nonneg hX _))
      hEL (Real.exp_pos _).le (by have := positivePairComparisonConstant_pos dom (N + 1) M; positivity))
  exact ⟨hHT', hplusErr, hCET'⟩

include hW hθ hD in
theorem cepsScaledPositivePair_entrance_error_profile {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : z.re = 0) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z)) :
    let L := dom.positivePairComparisonConstant (N + 1) M
    let X := 1 + |lam| + Real.sqrt ‖z‖
    let beta := b ^ (N + 2)
    let E := Real.exp (-(dom.positiveBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) / 2)
    let H := cepsScaledTrueEntrance dom ρW lam z b
    let h := cepsScaledSurrogateEntrance dom ρW (N + 1) lam z b
    let Hh := cepsScaledTrueHalfEntrance dom ρW lam z b
    let hh := cepsScaledSurrogateHalfEntrance dom ρW (N + 1) lam z b
    ‖H‖ ≤ L * X ∧ ‖h‖ ≤ L * X ∧ ‖H + Hh‖ ≤ L * X ∧ ‖h + hh‖ ≤ L * X ∧
    ‖h - hh‖ ≤ L * X * E ∧ ‖H - h‖ ≤ L * beta * X ^ (N + 3) ∧
    ‖(H + Hh) - (h + hh)‖ ≤ L * beta * X ^ (N + 3) ∧
    ‖(H - Hh) - (h - hh)‖ ≤ L * beta * X ^ (N + 3) * E := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cepsScaledPositivePair_entrance_norm_profile
    dom hW hθ hD hf hη hM N hN lam hlam hz hb hbs hbN
  obtain ⟨h6, h7, h8⟩ := cepsScaledPositivePair_entrance_taylor_profile
    dom hW hθ hD hf hη hM N hN lam hlam hz hb hbs hbN
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

end PGM
