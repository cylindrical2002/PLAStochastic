import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Holomorphic

/-!
# The discount variable `s = e^{-q}` and drifted steps

Statement shapes of the CEPS blueprint (W-1–W-3): steps `Y = W + μ`, discount `e^{-q}` with
`Re q ≥ 0`, `d(ζ; μ, q) = 1 - e^{-q} e^{μ ζ} M₀(ζ)`.

* `stepTransform_driftStep`: `E e^{ζ (W + μ)} = e^{μ ζ} E e^{ζ W}`.
* `norm_entryTransform_le`: `‖E[s^τ e^{z S_τ}; τ < ∞]‖ ≤ ‖s‖` when `‖s‖ ≤ 1` and `Re z · x ≤ 0` on
  the entrance set; in particular `‖A_±‖ < 1` for `Re q > 0`.
* `continuousOn_entryTransform_disk`, `differentiableOn_entryTransform_disk`: under absolute
  convergence of the ladder series, the transform is continuous on `‖s‖ ≤ 1` and holomorphic on
  `‖s‖ < 1`; `continuousOn_entryTransform_exp`, `differentiableOn_entryTransform_exp` give the same
  in `q` on `Re q ≥ 0`, resp. `Re q > 0`.
* `tsum_resolvent_mul`: the argmax (first ascending ladder) decomposition of the resolvent,
  `(∑ sⁿ φ(z)ⁿ)(1 - χ₊(s, z)) = ∑ sⁿ E[e^{z S_n}; S_1, …, S_n ≤ 0]`.
* `wienerHopf_drift_strip`: `(1 - A₊(ζ))(1 - A₋(ζ)) = 1 - e^{-q} e^{μ ζ} M₀(ζ)` for `Re q ≥ 0`,
  `|Re ζ| ≤ a`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Finset
open scoped ENNReal

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {A : Set ℝ}

/-! ### Drifted steps -/

/-- The law of `W + μ` for `W ∼ ρW`. -/
def driftStep (ρW : Measure ℝ) (μ : ℝ) : Measure ℝ := ρW.map fun w => w + μ

instance (ρW : Measure ℝ) [IsProbabilityMeasure ρW] (μ : ℝ) :
    IsProbabilityMeasure (driftStep ρW μ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- `E e^{ζ (W + μ)} = e^{μ ζ} E e^{ζ W}`. -/
theorem stepTransform_driftStep (ρW : Measure ℝ) (μ : ℝ) (ζ : ℂ) :
    stepTransform (driftStep ρW μ) ζ = cexp (μ * ζ) * stepTransform ρW ζ := by
  unfold stepTransform driftStep
  rw [integral_map (by fun_prop) (by fun_prop), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [Complex.ofReal_add, ← Complex.exp_add]
  ring_nf

theorem norm_cexp_neg_le_one {q : ℂ} (hq : 0 ≤ q.re) : ‖cexp (-q)‖ ≤ 1 := by
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff]
  linarith

theorem norm_cexp_neg_lt_one {q : ℂ} (hq : 0 < q.re) : ‖cexp (-q)‖ < 1 := by
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_lt_one_iff]
  linarith

/-! ### `‖A_±‖ ≤ ‖s‖` -/

/-- `‖E[s^τ e^{z S_τ}; τ < ∞]‖ ≤ ‖s‖` for `‖s‖ ≤ 1` and `Re z · x ≤ 0` on `A`. -/
theorem norm_entryTransform_le {s z : ℂ} (hs : ‖s‖ ≤ 1)
    (hzA : ∀ x ∈ A, z.re * x ≤ 0) : ‖entryTransform ρ A s z‖ ≤ ‖s‖ := by
  have hpt : ∀ ω ∈ {ω | firstEntry A ω < ⊤},
      ‖s ^ (firstEntry A ω).toNat * cexp (z * entryValue A ω)‖ ≤ ‖s‖ := by
    intro ω hω
    obtain ⟨n, hn⟩ := firstEntry_lt_top_iff.mp hω
    have hn1 : 1 ≤ n := (firstEntry_eq_coe_iff.mp hn).1
    rw [norm_mul, norm_pow, norm_cexp_mul_ofReal, hn, ENat.toNat_natCast]
    have he : Real.exp (z.re * entryValue A ω) ≤ 1 :=
      Real.exp_le_one_iff.mpr (hzA _ (entryValue_mem hω))
    calc ‖s‖ ^ n * Real.exp (z.re * entryValue A ω) ≤ ‖s‖ ^ 1 * 1 :=
          mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hs hn1) he (Real.exp_pos _).le
            (pow_nonneg (norm_nonneg _) _)
      _ = ‖s‖ := by ring
  calc ‖entryTransform ρ A s z‖
      ≤ ‖s‖ * (pathLaw ρ).real {ω | firstEntry A ω < ⊤} :=
        norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hpt
    _ ≤ ‖s‖ * 1 := mul_le_mul_of_nonneg_left measureReal_le_one (norm_nonneg _)
    _ = ‖s‖ := mul_one _

/-- `‖A₊(ζ)‖ < 1` for `Re q > 0` and `Re ζ ≤ 0`. -/
theorem norm_ascTransform_exp_lt_one {q ζ : ℂ} (hq : 0 < q.re) (hζ : ζ.re ≤ 0) :
    ‖ascTransform ρ (cexp (-q)) ζ‖ < 1 :=
  lt_of_le_of_lt (norm_entryTransform_le (norm_cexp_neg_lt_one hq).le
    fun x hx => mul_nonpos_of_nonpos_of_nonneg hζ (le_of_lt (show (0 : ℝ) < x from hx)))
    (norm_cexp_neg_lt_one hq)

/-- `‖A₋(ζ)‖ < 1` for `Re q > 0` and `Re ζ ≥ 0`. -/
theorem norm_descTransform_exp_lt_one {q ζ : ℂ} (hq : 0 < q.re) (hζ : 0 ≤ ζ.re) :
    ‖descTransform ρ (cexp (-q)) ζ‖ < 1 :=
  lt_of_le_of_lt (norm_entryTransform_le (norm_cexp_neg_lt_one hq).le
    fun _ hx => mul_nonpos_of_nonneg_of_nonpos hζ hx) (norm_cexp_neg_lt_one hq)

/-! ### Regularity in the discount -/

omit [IsProbabilityMeasure ρ] in
theorem continuousOn_entryTransform_disk (hAm : MeasurableSet A) {z : ℂ}
    (hint : ∀ n : ℕ, IntegrableOn (fun ω => cexp (z * partialSum n ω))
      {ω | firstEntry A ω = n} (pathLaw ρ))
    (hsum : Summable fun n : ℕ =>
      ∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ) :
    ContinuousOn (fun s => entryTransform ρ A s z) (Metric.closedBall 0 1) := by
  have hbound : ∀ (n : ℕ), ∀ s ∈ Metric.closedBall (0 : ℂ) 1, ‖s ^ n * entryCoeff ρ A z n‖ ≤
      ∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ := by
    intro n s hs
    rw [mem_closedBall_zero_iff] at hs
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hs)).trans
      (norm_integral_le_integral_norm _)
  have hc := continuousOn_tsum (fun n => (continuous_pow n |>.mul continuous_const).continuousOn)
    hsum hbound
  refine hc.congr fun s hs => ?_
  rw [mem_closedBall_zero_iff] at hs
  refine entryTransform_eq_tsum hAm hint ?_
  exact hsum.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun _ => norm_nonneg _))
    fun n => mul_le_of_le_one_left (integral_nonneg fun _ => norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) hs)

omit [IsProbabilityMeasure ρ] in
theorem differentiableOn_entryTransform_disk (hAm : MeasurableSet A) {z : ℂ}
    (hint : ∀ n : ℕ, IntegrableOn (fun ω => cexp (z * partialSum n ω))
      {ω | firstEntry A ω = n} (pathLaw ρ))
    (hsum : Summable fun n : ℕ =>
      ∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ) :
    DifferentiableOn ℂ (fun s => entryTransform ρ A s z) (Metric.ball 0 1) := by
  have hbound : ∀ (n : ℕ), ∀ s ∈ Metric.ball (0 : ℂ) 1, ‖s ^ n * entryCoeff ρ A z n‖ ≤
      ∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ := by
    intro n s hs
    rw [mem_ball_zero_iff] at hs
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hs.le)).trans
      (norm_integral_le_integral_norm _)
  have hd := differentiableOn_tsum_of_summable_norm hsum
    (fun n => ((differentiable_pow n).mul (differentiable_const _)).differentiableOn)
    Metric.isOpen_ball hbound
  refine hd.congr fun s hs => ?_
  rw [mem_ball_zero_iff] at hs
  refine entryTransform_eq_tsum hAm hint ?_
  exact hsum.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun _ => norm_nonneg _))
    fun n => mul_le_of_le_one_left (integral_nonneg fun _ => norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) hs.le)

omit [IsProbabilityMeasure ρ] in
/-- In the variable `q` (`s = e^{-q}`): continuous on `Re q ≥ 0`. -/
theorem continuousOn_entryTransform_exp (hAm : MeasurableSet A) {z : ℂ}
    (hint : ∀ n : ℕ, IntegrableOn (fun ω => cexp (z * partialSum n ω))
      {ω | firstEntry A ω = n} (pathLaw ρ))
    (hsum : Summable fun n : ℕ =>
      ∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ) :
    ContinuousOn (fun q => entryTransform ρ A (cexp (-q)) z) {q | 0 ≤ q.re} :=
  (continuousOn_entryTransform_disk hAm hint hsum).comp
    (Complex.continuous_exp.comp continuous_neg).continuousOn
    fun _ hq => mem_closedBall_zero_iff.mpr (norm_cexp_neg_le_one hq)

omit [IsProbabilityMeasure ρ] in
/-- In the variable `q` (`s = e^{-q}`): holomorphic on `Re q > 0`. -/
theorem differentiableOn_entryTransform_exp (hAm : MeasurableSet A) {z : ℂ}
    (hint : ∀ n : ℕ, IntegrableOn (fun ω => cexp (z * partialSum n ω))
      {ω | firstEntry A ω = n} (pathLaw ρ))
    (hsum : Summable fun n : ℕ =>
      ∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ) :
    DifferentiableOn ℂ (fun q => entryTransform ρ A (cexp (-q)) z) {q | 0 < q.re} :=
  (differentiableOn_entryTransform_disk hAm hint hsum).comp
    (Complex.differentiable_exp.comp differentiable_neg).differentiableOn
    fun _ hq => mem_ball_zero_iff.mpr (norm_cexp_neg_lt_one hq)

/-! ### The argmax decomposition of the resolvent -/

/-- The first-ascending-ladder (argmax) decomposition of the resolvent:
`(∑ sⁿ φ(z)ⁿ) (1 - E[s^{τ_{Aᶜ}} e^{z S}; τ_{Aᶜ} < ∞]) = ∑ sⁿ E[e^{z S_n}; n < τ_{Aᶜ}]`
whenever `‖s‖ ∫ e^{Re z · y} dρ < 1`. For `A = Iic 0` the right side is
`∑ sⁿ E[e^{z S_n}; S_1, …, S_n ≤ 0]`. -/
theorem tsum_resolvent_mul (hAm : MeasurableSet A) {s z : ℂ}
    (hz : Integrable (fun y : ℝ => cexp (z * y)) ρ)
    (hs : ‖s‖ * ∫ y, Real.exp (z.re * y) ∂ρ < 1) :
    (∑' n, s ^ n * stepTransform ρ z ^ n) * (1 - entryTransform ρ Aᶜ s z) =
      ∑' n, s ^ n * survivalCoeff ρ Aᶜ z n := by
  set M := ∫ y, Real.exp (z.re * y) ∂ρ
  have hM := integral_exp_re_nonneg (ρ := ρ) z
  have hφ : ‖stepTransform ρ z‖ ≤ M := by
    have := norm_setIntegral_cexp_partialSum_le hz (ρ := ρ) univ 1
    simpa [Measure.restrict_univ, integral_cexp_partialSum hz] using this
  have ha : ∀ n, ‖stepTransform ρ z ^ n‖ ≤ M ^ n := fun n => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hφ n
  have hf : ∀ n, ‖entryCoeff ρ Aᶜ z n‖ ≤ M ^ n := fun n =>
    norm_setIntegral_cexp_partialSum_le hz _ n
  have hg : ∀ n, ‖survivalCoeff ρ Aᶜ z n‖ ≤ M ^ n := fun n =>
    norm_setIntegral_cexp_partialSum_le hz _ n
  have hX := tsum_pow_mul_eq_add_mul (summable_norm_pow_mul_of_le hM hs hf)
    (summable_norm_pow_mul_of_le hM hs ha) (summable_norm_pow_mul_of_le hM hs hg).of_norm
    (stepTransform_pow_eq_survival_add hAm.compl hz)
  rw [← entryTransform_eq_tsum_of_lt_one hAm.compl hz hs] at hX
  linear_combination hX

/-- The resolvent decomposition for `‖s‖ < 1` and `Re z = 0`, strict ascending ladder:
`(∑ sⁿ φ(z)ⁿ)(1 - χ₊(s, z)) = ∑ sⁿ E[e^{z S_n}; n < τ₊]`. -/
theorem tsum_resolvent_mul_asc (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {s z : ℂ}
    (hs : ‖s‖ < 1) (hz : z.re = 0) :
    (∑' n, s ^ n * stepTransform ρ z ^ n) * (1 - ascTransform ρ s z) =
      ∑' n, s ^ n * survivalCoeff ρ (Ioi 0) z n := by
  have h := tsum_resolvent_mul (ρ := ρ) (A := Iic 0) measurableSet_Iic (s := s)
    (integrable_cexp_of_re_eq_zero hz)
    (by rw [integral_exp_re_of_re_eq_zero hz, mul_one]; exact hs)
  rwa [compl_Iic] at h

/-! ### The factorization in the blueprint's shape -/

/-- **Wiener–Hopf for drifted steps**: for `Y = W + μ` with `∫ e^{± a y} d Law(Y) < ∞` charging
both half-lines, `Re q ≥ 0` and `|Re ζ| ≤ a`,
`(1 - A₊(ζ)) (1 - A₋(ζ)) = 1 - e^{-q} e^{μ ζ} M₀(ζ)` with `M₀(ζ) = E e^{ζ W}`. -/
theorem wienerHopf_drift_strip (ρW : Measure ℝ) [IsProbabilityMeasure ρW] (μ : ℝ) {a : ℝ}
    (ha : 0 < a)
    (hpos : Integrable (fun y : ℝ => Real.exp (a * y)) (driftStep ρW μ))
    (hneg : Integrable (fun y : ℝ => Real.exp (-a * y)) (driftStep ρW μ))
    (hl : 0 < driftStep ρW μ (Iio 0)) (hr : 0 < driftStep ρW μ (Ioi 0)) {q ζ : ℂ}
    (hq : 0 ≤ q.re) (hζ : |ζ.re| ≤ a) :
    (1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ) *
        (1 - descTransform (driftStep ρW μ) (cexp (-q)) ζ) =
      1 - cexp (-q) * cexp (μ * ζ) * stepTransform ρW ζ := by
  rw [← wienerHopf_strip_of_pos ha hpos hneg hl hr (norm_cexp_neg_le_one hq) hζ,
    stepTransform_driftStep, mul_assoc]

end PGM.WienerHopf
