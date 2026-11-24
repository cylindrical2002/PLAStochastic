import PLAStochastic.Swing.FrozenCarry.Path.LengthLimit
import PLAStochastic.Swing.FirstSegment.LowerRejectionReflection

/-! An actual Gaussian exponential-series envelope for negative frozen carries. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The full exponential series of the original Gaussian partial sums. -/
def gaussianNegativeCarryEnvelope (X : ℕ → Ω → ℝ) (c : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(c/2)*cumulativeSamples X n ω-c^2*(n : ℝ)/4))

theorem gaussianNegativeCarryEnvelope_measurable
    (hX : ∀ n, Measurable (X n)) (c : ℝ) : Measurable (gaussianNegativeCarryEnvelope X c) := by
  apply Measurable.tsum
  intro n
  have hm : Measurable (cumulativeSamples X n) := Finset.measurable_sum _ (fun k _ => hX k)
  exact ((hm.const_mul (-(c/2))).sub_const (c^2*(n : ℝ)/4)).exp.ennreal_ofReal

/-- The actual fixed-time Gaussian MGF controls each term of the envelope. -/
theorem gaussianNegativeCarryEnvelope_term_integral
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (c : ℝ) (n : ℕ) :
    Integrable (fun ω => Real.exp (-(c/2)*cumulativeSamples X n ω-c^2*(n : ℝ)/4)) μ ∧
    (∫ ω, Real.exp (-(c/2)*cumulativeSamples X n ω-c^2*(n : ℝ)/4) ∂μ) =
      Real.exp (-(c^2)/8)^n := by
  have hl : HasLaw (cumulativeSamples X n) (gaussianReal 0 (n : ℝ≥0)) μ := by
    simpa [cumulativeSamples] using! gaussian_weighted_sum_hasLaw hX hi hG (Finset.range n) (fun _ => 1)
  have hI : Integrable (fun ω => Real.exp (-(c/2)*cumulativeSamples X n ω)) μ := by
    apply (integrable_map_measure (g := fun z : ℝ => Real.exp (-(c/2)*z))
      (by fun_prop) hl.aemeasurable).mp
    rw [hl.map_eq]
    exact integrable_exp_mul_gaussianReal _
  have he : (∫ ω, Real.exp (-(c/2)*cumulativeSamples X n ω) ∂μ) = Real.exp ((n : ℝ)*(c/2)^2/2) := by
    have h := hl.integral_comp (show AEStronglyMeasurable (fun z : ℝ => Real.exp (-(c/2)*z))
      (gaussianReal 0 (n : ℝ≥0)) by fun_prop)
    dsimp only [Function.comp_def] at h
    rw [h]
    simpa only [mgf, id_eq, zero_mul, NNReal.coe_natCast, zero_add, neg_sq] using
      congrFun (mgf_id_gaussianReal (μ := 0) (v := (n : ℝ≥0))) (-(c/2))
  have heq (ω : Ω) : Real.exp (-(c/2)*cumulativeSamples X n ω-c^2*(n : ℝ)/4) =
      Real.exp (-(c^2*(n : ℝ)/4))*Real.exp (-(c/2)*cumulativeSamples X n ω) := by
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · apply (hI.const_mul _).congr
    exact ae_of_all _ (fun ω => (heq ω).symm)
  · simp_rw [heq]
    rw [integral_const_mul, he, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring

/-- Tonelli and the geometric Gaussian MGF sum prove finiteness without a pathwise envelope hypothesis. -/
theorem gaussianNegativeCarryEnvelope_lintegral_ne_top
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {c : ℝ} (hc : 0 < c) :
    (∫⁻ ω, gaussianNegativeCarryEnvelope X c ω ∂μ) ≠ ∞ := by
  have hq : Real.exp (-(c^2)/8) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hc])
  have hsum := (summable_geometric_of_lt_one (Real.exp_pos _).le hq).tsum_ofReal_lt_top
  have hm (n : ℕ) : AEMeasurable
      (fun ω => ENNReal.ofReal (Real.exp (-(c/2)*cumulativeSamples X n ω-c^2*(n : ℝ)/4))) μ :=
    (gaussianNegativeCarryEnvelope_term_integral hX hi hG c n).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  unfold gaussianNegativeCarryEnvelope
  rw [lintegral_tsum hm]
  simp_rw [← ofReal_integral_eq_lintegral_ofReal
    (gaussianNegativeCarryEnvelope_term_integral hX hi hG c _).1
    (ae_of_all _ (fun _ => (Real.exp_pos _).le)),
    (gaussianNegativeCarryEnvelope_term_integral hX hi hG c _).2]
  exact hsum.ne

theorem gaussianNegativeCarryEnvelope_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {c : ℝ} (hc : 0 < c) :
    Integrable (fun ω => (gaussianNegativeCarryEnvelope X c ω).toReal) μ :=
  integrable_toReal_of_lintegral_ne_top (gaussianNegativeCarryEnvelope_measurable hX c).aemeasurable
    (gaussianNegativeCarryEnvelope_lintegral_ne_top hX hi hG hc)

theorem gaussianNegativeCarryEnvelope_finite_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ ω ∂μ, gaussianNegativeCarryEnvelope X c ω ≠ ∞ :=
  (ae_lt_top (gaussianNegativeCarryEnvelope_measurable hX c)
    (gaussianNegativeCarryEnvelope_lintegral_ne_top hX hi hG hc)).mono (fun _ h => h.ne)

omit mΩ in
theorem gaussianNegativeCarryEnvelope_bounds {c : ℝ} {ω : Ω}
    (hH : gaussianNegativeCarryEnvelope X c ω ≠ ∞) (n : ℕ) :
    -(c/2)*cumulativeSamples X n ω-c^2*(n : ℝ)/4 ≤
      (gaussianNegativeCarryEnvelope X c ω).toReal := by
  have he : Real.exp (-(c/2)*cumulativeSamples X n ω-c^2*(n : ℝ)/4) ≤
      (gaussianNegativeCarryEnvelope X c ω).toReal := by
    have h := ENNReal.toReal_mono hH (ENNReal.le_tsum (f := fun k : ℕ =>
      ENNReal.ofReal (Real.exp (-(c/2)*cumulativeSamples X k ω-c^2*(k : ℝ)/4))) n)
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  linarith [Real.add_one_le_exp (-(c/2)*cumulativeSamples X n ω-c^2*(n : ℝ)/4)]

/-! A two-sided version obtained by applying the same exponential-series
certificate to `X` and to its reflected sequence.  The resulting slope is
`c/2`, while the random intercept is explicit and finite whenever both
series are finite. -/

def gaussianNegativeCarryAffineIntercept (X : ℕ → Ω → ℝ) (c : ℝ) (ω : Ω) : ℝ :=
  max ((2 / c) * (gaussianNegativeCarryEnvelope X c ω).toReal)
    ((2 / c) * (gaussianNegativeCarryEnvelope (negIncrements X) c ω).toReal)

omit mΩ in
theorem gaussianNegativeCarryAffineEnvelope_bounds
    {c : ℝ} {ω : Ω} (hc : 0 < c)
    (hH : gaussianNegativeCarryEnvelope X c ω ≠ ∞)
    (hHneg : gaussianNegativeCarryEnvelope (negIncrements X) c ω ≠ ∞) :
    ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤
        gaussianNegativeCarryAffineIntercept X c ω + (c / 2) * (n : ℝ) := by
  intro n
  let Hp : ℝ := (gaussianNegativeCarryEnvelope X c ω).toReal
  let Hm : ℝ := (gaussianNegativeCarryEnvelope (negIncrements X) c ω).toReal
  let A : ℝ := max ((2 / c) * Hp) ((2 / c) * Hm)
  have hHp : 0 ≤ Hp := by
    dsimp [Hp]
    exact ENNReal.toReal_nonneg
  have hHm : 0 ≤ Hm := by
    dsimp [Hm]
    exact ENNReal.toReal_nonneg
  have hc2 : 0 < c / 2 := by positivity
  have hplus := gaussianNegativeCarryEnvelope_bounds
    (X := X) (c := c) (ω := ω) hH n
  have hminus := gaussianNegativeCarryEnvelope_bounds
    (X := negIncrements X) (c := c) (ω := ω) hHneg n
  have hminus' :
      (c / 2) * cumulativeSamples X n ω - c^2 * (n : ℝ) / 4 ≤ Hm := by
    rw [cumulativeSamples_neg] at hminus
    dsimp [Hm] at hminus ⊢
    linarith
  have hplus' :
      -(c / 2) * cumulativeSamples X n ω - c^2 * (n : ℝ) / 4 ≤ Hp := by
    simpa only [Hp] using hplus
  have hlow_mul :
      (c / 2) * (-(2 / c) * Hp - (c / 2) * (n : ℝ)) ≤
        (c / 2) * cumulativeSamples X n ω := by
    have hEq :
        (c / 2) * (-(2 / c) * Hp - (c / 2) * (n : ℝ)) =
          -Hp - c^2 * (n : ℝ) / 4 := by
      field_simp
      ring
    rw [hEq]
    linarith
  have hlow :
      -(2 / c) * Hp - (c / 2) * (n : ℝ) ≤ cumulativeSamples X n ω := by
    exact le_of_mul_le_mul_left hlow_mul hc2
  have hupp_mul :
      (c / 2) * cumulativeSamples X n ω ≤
        (c / 2) * ((2 / c) * Hm + (c / 2) * (n : ℝ)) := by
    have hEq :
        (c / 2) * ((2 / c) * Hm + (c / 2) * (n : ℝ)) =
          Hm + c^2 * (n : ℝ) / 4 := by
      field_simp
      ring
    rw [hEq]
    linarith
  have hupp :
      cumulativeSamples X n ω ≤
        (2 / c) * Hm + (c / 2) * (n : ℝ) := by
    exact le_of_mul_le_mul_left hupp_mul hc2
  have hAplus : (2 / c) * Hp ≤ A := by
    exact le_max_left _ _
  have hAminus : (2 / c) * Hm ≤ A := by
    exact le_max_right _ _
  have hlowA :
      -(A + (c / 2) * (n : ℝ)) ≤ cumulativeSamples X n ω := by
    linarith
  have huppA :
      cumulativeSamples X n ω ≤ A + (c / 2) * (n : ℝ) := by
    linarith
  have habs := (abs_le).2 ⟨hlowA, huppA⟩
  simpa only [gaussianNegativeCarryAffineIntercept, Hp, Hm, A] using habs

theorem gaussianNegativeCarryAffineIntercept_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {c : ℝ} (hc : 0 < c) :
    Integrable (gaussianNegativeCarryAffineIntercept X c) μ := by
  have hnegX : ∀ n, Measurable (negIncrements X n) := fun n => (hX n).neg
  have hineg : iIndepFun (negIncrements X) μ := by
    have hfun : negIncrements X = (fun n ω => -X n ω) := by
      funext n ω
      rfl
    rw [hfun]
    exact hi.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hGneg : ∀ n, μ.map (negIncrements X n) = gaussianReal 0 1 := by
    intro n
    calc
      μ.map (negIncrements X n) = Measure.map ((fun x : ℝ => -x) ∘ X n) μ := by rfl
      _ = Measure.map (fun x : ℝ => -x) (μ.map (X n)) :=
        (Measure.map_map measurable_neg (hX n)).symm
      _ = Measure.map (fun x : ℝ => -x) (gaussianReal 0 1) := by rw [hG n]
      _ = gaussianReal 0 1 := by rw [gaussianReal_map_neg]; simp
  have hIp := gaussianNegativeCarryEnvelope_integrable hX hi hG hc
  have hIm := gaussianNegativeCarryEnvelope_integrable hnegX hineg hGneg hc
  have hcp : Integrable (fun ω => (2 / c) *
      (gaussianNegativeCarryEnvelope X c ω).toReal) μ := hIp.const_mul (2 / c)
  have hcm : Integrable (fun ω => (2 / c) *
      (gaussianNegativeCarryEnvelope (negIncrements X) c ω).toReal) μ :=
    hIm.const_mul (2 / c)
  have hs := hcp.sup hcm
  change Integrable (fun ω => max
    ((2 / c) * (gaussianNegativeCarryEnvelope X c ω).toReal)
    ((2 / c) * (gaussianNegativeCarryEnvelope (negIncrements X) c ω).toReal)) μ
  exact hs

theorem gaussianNegativeCarryAffineEnvelope_bounds_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤
        gaussianNegativeCarryAffineIntercept X c ω + (c / 2) * (n : ℝ) := by
  have hnegX : ∀ n, Measurable (negIncrements X n) := fun n => (hX n).neg
  have hineg : iIndepFun (negIncrements X) μ := by
    have hfun : negIncrements X = (fun n ω => -X n ω) := by
      funext n ω
      rfl
    rw [hfun]
    exact hi.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hGneg : ∀ n, μ.map (negIncrements X n) = gaussianReal 0 1 := by
    intro n
    calc
      μ.map (negIncrements X n) = Measure.map ((fun x : ℝ => -x) ∘ X n) μ := by rfl
      _ = Measure.map (fun x : ℝ => -x) (μ.map (X n)) :=
        (Measure.map_map measurable_neg (hX n)).symm
      _ = Measure.map (fun x : ℝ => -x) (gaussianReal 0 1) := by rw [hG n]
      _ = gaussianReal 0 1 := by rw [gaussianReal_map_neg]; simp
  filter_upwards [gaussianNegativeCarryEnvelope_finite_ae hX hi hG hc,
    gaussianNegativeCarryEnvelope_finite_ae hnegX hineg hGneg hc] with ω hH hHneg
  exact gaussianNegativeCarryAffineEnvelope_bounds hc hH hHneg

end SwingRepair
