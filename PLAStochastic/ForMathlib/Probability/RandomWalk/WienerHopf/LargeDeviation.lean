import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.StepClass

/-!
# Fixed-drift large deviations (blueprint W-7)

* `measureReal_partialSum_le_neg_le`, `measureReal_partialSum_ge_le`: Chernoff bounds
  `P(S_m ≤ -x) ≤ e^{-λ x} (E e^{-λ Y})^m`, `P(S_m ≥ x) ≤ e^{-λ x} (E e^{λ Y})^m`.
* `measureReal_increment_le`: increments have the law of the walk,
  `P(S_j - S_i ≤ -x) = P(S_{j-i} ≤ -x)`.
* `IsStepLaw.integral_sq_mul_exp_le`: `E[W² e^{θ|W|/2}] ≤ 256 D / θ³`;
  `IsStepLaw.integral_exp_le`: `E e^{t W} ≤ 1 + t² · 256 D / θ³` for `|t| ≤ θ/2`.
* For the step class and `Y = W + μ` with `μ ≥ δ > 0`, with the rate
  `c = driftRate D θ δ = min (θ/4) (δ θ³ / (1024 D))`:
  `measureReal_increment_le_of_stepLaw`: `P(Z_j - Z_i ≤ -x) ≤ e^{-c (x + δ (j - i))}`;
  `measureReal_exists_increment_le_of_stepLaw`: `P(∃ i ≤ j ≤ k, Z_j - Z_i ≤ -x) ≤ (k+1)² e^{-c x}`;
  `measureReal_exists_partialSum_le_of_stepLaw`: `P(∃ m, Z_m ≤ -x) ≤ e^{-c x} / (1 - e^{-c δ})`.
  For `μ ≤ -δ` the reflected statements (`…_ge_of_stepLaw`) hold with the same rate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ]

/-! ### Chernoff bounds -/

/-- `P(S_m ≤ -x) ≤ e^{-λ x} (E e^{-λ Y})^m` for `λ ≥ 0`. -/
theorem measureReal_partialSum_le_neg_le {l : ℝ} (hl : 0 ≤ l)
    (hint : Integrable (fun y : ℝ => Real.exp (-l * y)) ρ) (m : ℕ) (x : ℝ) :
    (pathLaw ρ).real {ω | partialSum m ω ≤ -x} ≤
      Real.exp (-l * x) * (∫ y, Real.exp (-l * y) ∂ρ) ^ m := by
  obtain ⟨hfi, hfe⟩ := integrable_exp_partialSum hint m
  have hsub : {ω | partialSum m ω ≤ -x} ⊆
      {ω | Real.exp (l * x) ≤ Real.exp (-l * partialSum m ω)} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [Real.exp_le_exp]; nlinarith
  have hM := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos (-l * partialSum m ω)).le) hfi
    (Real.exp (l * x))
  rw [hfe] at hM
  have hpos := Real.exp_pos (l * x)
  calc (pathLaw ρ).real {ω | partialSum m ω ≤ -x}
      ≤ (pathLaw ρ).real {ω | Real.exp (l * x) ≤ Real.exp (-l * partialSum m ω)} :=
        measureReal_mono hsub
    _ ≤ Real.exp (-l * x) * (∫ y, Real.exp (-l * y) ∂ρ) ^ m := by
        rw [show -l * x = -(l * x) by ring, Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ hpos]
        linarith [hM]

/-- `P(S_m ≥ x) ≤ e^{-λ x} (E e^{λ Y})^m` for `λ ≥ 0`. -/
theorem measureReal_partialSum_ge_le {l : ℝ} (hl : 0 ≤ l)
    (hint : Integrable (fun y : ℝ => Real.exp (l * y)) ρ) (m : ℕ) (x : ℝ) :
    (pathLaw ρ).real {ω | x ≤ partialSum m ω} ≤
      Real.exp (-l * x) * (∫ y, Real.exp (l * y) ∂ρ) ^ m := by
  obtain ⟨hfi, hfe⟩ := integrable_exp_partialSum hint m
  have hsub : {ω | x ≤ partialSum m ω} ⊆
      {ω | Real.exp (l * x) ≤ Real.exp (l * partialSum m ω)} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [Real.exp_le_exp]; nlinarith
  have hM := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos (l * partialSum m ω)).le) hfi
    (Real.exp (l * x))
  rw [hfe] at hM
  have hpos := Real.exp_pos (l * x)
  calc (pathLaw ρ).real {ω | x ≤ partialSum m ω}
      ≤ (pathLaw ρ).real {ω | Real.exp (l * x) ≤ Real.exp (l * partialSum m ω)} :=
        measureReal_mono hsub
    _ ≤ Real.exp (-l * x) * (∫ y, Real.exp (l * y) ∂ρ) ^ m := by
        rw [show -l * x = -(l * x) by ring, Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ hpos]
        linarith [hM]

/-- Increments have the law of the walk: `P(S_j - S_i ∈ E) = P(S_{j-i} ∈ E)`. -/
theorem measureReal_increment_eq {i j : ℕ} (hij : i ≤ j) {E : Set ℝ} (hE : MeasurableSet E) :
    (pathLaw ρ).real {ω | partialSum j ω - partialSum i ω ∈ E} =
      (pathLaw ρ).real {ω | partialSum (j - i) ω ∈ E} := by
  have hset : {ω | partialSum j ω - partialSum i ω ∈ E} =
      shift i ⁻¹' {ω | partialSum (j - i) ω ∈ E} := by
    ext ω
    simp only [mem_ofPred_eq, Set.mem_preimage]
    rw [partialSum_shift, Nat.add_sub_cancel' hij]
  have hmeas : MeasurableSet {ω : ℕ → ℝ | partialSum (j - i) ω ∈ E} :=
    hE.preimage (measurable_partialSum (j - i))
  rw [hset, measureReal_def, measureReal_def,
    (measurePreserving_shift (ρ := ρ) i).measure_preimage hmeas.nullMeasurableSet]

/-! ### Moment generating functions of the step class -/

/-- `e^t ≤ 1 + t + t² e^{|t|}`. -/
theorem exp_le_one_add_add_sq_mul_exp_abs (t : ℝ) :
    Real.exp t ≤ 1 + t + t ^ 2 * Real.exp |t| := by
  rcases le_or_gt |t| 1 with h | h
  · have h1 := Real.abs_exp_sub_one_sub_id_le h
    have h2 : t ^ 2 ≤ t ^ 2 * Real.exp |t| :=
      le_mul_of_one_le_right (sq_nonneg t) (Real.one_le_exp (abs_nonneg t))
    linarith [le_abs_self (Real.exp t - 1 - t)]
  · have hexp : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.mpr (le_abs_self t)
    have hsq : 1 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
    rcases le_or_gt 0 t with ht | ht
    · nlinarith [Real.exp_pos |t|]
    · -- `t < -1`: the right side is at least `1`
      have habs : |t| = -t := abs_of_neg ht
      have hq := Real.quadratic_le_exp_of_nonneg (abs_nonneg t)
      rw [habs] at hq hexp ⊢
      have he1 : 1 ≤ Real.exp (-t) := Real.one_le_exp (by linarith)
      have : Real.exp t ≤ 1 := Real.exp_le_one_iff.mpr ht.le
      nlinarith [sq_nonneg t]

namespace IsStepLaw

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

theorem lintegral_exp_neg_abs (a : ℝ) (ha : 0 < a) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (-a * |w|)) = ENNReal.ofReal (2 / a) := by
  have hR : (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0 := by ext; simp
  rw [← setLIntegral_univ, hR, lintegral_union measurableSet_Ioi
    (Set.disjoint_left.mpr fun x h1 h2 => by simp only [mem_Iic, mem_Ioi] at h1 h2; linarith)]
  have h1 : ∫⁻ w in Iic (0 : ℝ), ENNReal.ofReal (Real.exp (-a * |w|)) =
      ENNReal.ofReal (1 / a) := by
    rw [setLIntegral_congr_fun measurableSet_Iic (g := fun w => ENNReal.ofReal (Real.exp (a * w)))
      (fun w hw => by
        simp only [mem_Iic] at hw
        rw [abs_of_nonpos hw, show -a * -w = a * w by ring])]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic ha 0)
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le), integral_exp_mul_Iic ha 0]
    simp
  have h2 : ∫⁻ w in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-a * |w|)) =
      ENNReal.ofReal (1 / a) := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun w => ENNReal.ofReal (Real.exp (-a * w)))
      (fun w hw => by
        simp only [mem_Ioi] at hw
        rw [abs_of_pos hw])]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi (by linarith) 0)
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le),
      integral_exp_mul_Ioi (by linarith) 0]
    congr 1; simp
  rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

/-- `E[W² e^{θ|W|/2}] ≤ 256 D / θ³` (and the integrand is integrable). -/
theorem integral_sq_mul_exp_le (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 ≤ D) :
    Integrable (fun w => w ^ 2 * Real.exp (θ / 2 * |w|)) ρW ∧
      ∫ w, w ^ 2 * Real.exp (θ / 2 * |w|) ∂ρW ≤ 256 * D / θ ^ 3 := by
  have hm : Measurable fun w : ℝ => w ^ 2 * Real.exp (θ / 2 * |w|) := by fun_prop
  have hpt : ∀ w : ℝ, fW w * (w ^ 2 * Real.exp (θ / 2 * |w|)) ≤
      32 * D / θ ^ 2 * Real.exp (-(θ / 4) * |w|) := by
    intro w
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ θ / 4 * |w| by positivity)
    have hsq : w ^ 2 ≤ 32 / θ ^ 2 * Real.exp (θ / 4 * |w|) := by
      have : w ^ 2 = 32 / θ ^ 2 * ((θ / 4 * |w|) ^ 2 / 2) := by
        rw [mul_pow, sq_abs]; field_simp; ring
      rw [this]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith [abs_nonneg w]
    calc fW w * (w ^ 2 * Real.exp (θ / 2 * |w|))
        ≤ D * Real.exp (-θ * |w|) * (32 / θ ^ 2 * Real.exp (θ / 4 * |w|) *
            Real.exp (θ / 2 * |w|)) :=
          mul_le_mul (hW.le_exp w) (mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le)
            (by positivity) (by positivity)
      _ = 32 * D / θ ^ 2 * Real.exp (-(θ / 4) * |w|) := by
          rw [show D * Real.exp (-θ * |w|) * (32 / θ ^ 2 * Real.exp (θ / 4 * |w|) *
            Real.exp (θ / 2 * |w|)) = 32 * D / θ ^ 2 * (Real.exp (-θ * |w|) *
              Real.exp (θ / 4 * |w|) * Real.exp (θ / 2 * |w|)) by ring,
            ← Real.exp_add, ← Real.exp_add]
          congr 2; ring
  have hlin : ∫⁻ w, ENNReal.ofReal (w ^ 2 * Real.exp (θ / 2 * |w|)) ∂ρW ≤
      ENNReal.ofReal (256 * D / θ ^ 3) := by
    have hfE : Measurable fun x => ENNReal.ofReal (fW x) :=
      ENNReal.measurable_ofReal.comp hW.measurable
    have hmE : Measurable fun w => ENNReal.ofReal (w ^ 2 * Real.exp (θ / 2 * |w|)) :=
      ENNReal.measurable_ofReal.comp hm
    rw [hW.eq_withDensity, lintegral_withDensity_eq_lintegral_mul _ hfE hmE]
    calc ∫⁻ w, ((fun x => ENNReal.ofReal (fW x)) * fun w =>
          ENNReal.ofReal (w ^ 2 * Real.exp (θ / 2 * |w|))) w
        ≤ ∫⁻ w, ENNReal.ofReal (32 * D / θ ^ 2) *
            ENNReal.ofReal (Real.exp (-(θ / 4) * |w|)) := by
          refine lintegral_mono fun w => ?_
          simp only [Pi.mul_apply]
          rw [← ENNReal.ofReal_mul (hW.nonneg w), ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hpt w)
      _ = ENNReal.ofReal (32 * D / θ ^ 2) * ENNReal.ofReal (2 / (θ / 4)) := by
          rw [lintegral_const_mul _ (by fun_prop), lintegral_exp_neg_abs _ (by positivity)]
      _ = ENNReal.ofReal (256 * D / θ ^ 3) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp; ring
  have hint : Integrable (fun w => w ^ 2 * Real.exp (θ / 2 * |w|)) ρW := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun w => by positivity)]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => by positivity)
    hm.aestronglyMeasurable]
  calc _ ≤ (ENNReal.ofReal (256 * D / θ ^ 3)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    _ = _ := ENNReal.toReal_ofReal (by positivity)

/-- `E e^{t W} ≤ 1 + t² · 256 D / θ³` for `|t| ≤ θ/2`. -/
theorem integral_exp_le (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 ≤ D) {t : ℝ}
    (ht : |t| ≤ θ / 2) :
    Integrable (fun w => Real.exp (t * w)) ρW ∧
      ∫ w, Real.exp (t * w) ∂ρW ≤ 1 + t ^ 2 * (256 * D / θ ^ 3) := by
  have := hW.isProbabilityMeasure
  obtain ⟨hKi, hK⟩ := hW.integral_sq_mul_exp_le hθ hD
  have hpt : ∀ w : ℝ, Real.exp (t * w) ≤
      1 + t * w + t ^ 2 * (w ^ 2 * Real.exp (θ / 2 * |w|)) := by
    intro w
    have h := exp_le_one_add_add_sq_mul_exp_abs (t * w)
    have habs : |t * w| ≤ θ / 2 * |w| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right ht (abs_nonneg w)
    calc Real.exp (t * w) ≤ 1 + t * w + (t * w) ^ 2 * Real.exp |t * w| := h
      _ ≤ 1 + t * w + (t * w) ^ 2 * Real.exp (θ / 2 * |w|) := by
          gcongr
      _ = _ := by ring
  have hA1 : Integrable (fun w : ℝ => 1 + t * w) ρW :=
    (integrable_const 1).add (hW.integrable_id.const_mul t)
  have hA2 : Integrable (fun w : ℝ => t ^ 2 * (w ^ 2 * Real.exp (θ / 2 * |w|))) ρW :=
    hKi.const_mul _
  have hA3 : Integrable (fun w : ℝ => t * w) ρW := hW.integrable_id.const_mul t
  have hR : Integrable (fun w => 1 + t * w + t ^ 2 * (w ^ 2 * Real.exp (θ / 2 * |w|))) ρW :=
    hA1.add hA2
  have hexpi : Integrable (fun w => Real.exp (t * w)) ρW :=
    hR.mono' (by fun_prop) (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hpt w)
  refine ⟨hexpi, (integral_mono hexpi hR hpt).trans ?_⟩
  rw [integral_add hA1 hA2, integral_add (integrable_const 1) hA3, integral_const,
    integral_const_mul, integral_const_mul, hW.integral_id]
  simp only [probReal_univ, smul_eq_mul, mul_one, mul_zero, add_zero]
  gcongr

end IsStepLaw

/-! ### Large deviations against a fixed drift -/

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

/-- The large-deviation rate `c = min (θ/4) (δ θ³ / (1024 D))`. -/
def driftRate (D θ δ : ℝ) : ℝ := min (θ / 4) (δ * θ ^ 3 / (1024 * D))

theorem driftRate_pos (hθ : 0 < θ) (hD : 0 < D) {δ : ℝ} (hδ : 0 < δ) : 0 < driftRate D θ δ :=
  lt_min (by positivity) (by positivity)

/-- The mgf of `±(W + μ)` against the drift: with `λ = 2 c`, `E e^{-λ (W + μ)} ≤ e^{-c δ}` for
`μ ≥ δ`. -/
theorem integral_exp_drift_le (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
    {δ μ : ℝ} (hδ : 0 < δ) (hμ : δ ≤ μ) {t : ℝ} (ht : |t| = 2 * driftRate D θ δ) :
    Integrable (fun w => Real.exp (t * w)) ρW ∧
      Real.exp (-(2 * driftRate D θ δ) * μ) * ∫ w, Real.exp (t * w) ∂ρW ≤
        Real.exp (-(driftRate D θ δ * δ)) := by
  set c := driftRate D θ δ
  have hc : 0 < c := driftRate_pos hθ hD hδ
  have hc1 : c ≤ θ / 4 := min_le_left _ _
  have hc2 : c ≤ δ * θ ^ 3 / (1024 * D) := min_le_right _ _
  obtain ⟨hi, hle⟩ := hW.integral_exp_le hθ hD.le (t := t) (by rw [ht]; linarith)
  refine ⟨hi, ?_⟩
  have hK : t ^ 2 * (256 * D / θ ^ 3) ≤ c * δ := by
    rw [← sq_abs, ht]
    have : 4 * c * (256 * D / θ ^ 3) ≤ δ := by
      rw [show 4 * c * (256 * D / θ ^ 3) = c * (1024 * D) / θ ^ 3 by ring,
        div_le_iff₀ (by positivity)]
      rw [le_div_iff₀ (by positivity)] at hc2
      linarith
    nlinarith
  calc Real.exp (-(2 * c) * μ) * ∫ w, Real.exp (t * w) ∂ρW
      ≤ Real.exp (-(2 * c) * μ) * (1 + t ^ 2 * (256 * D / θ ^ 3)) :=
        mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    _ ≤ Real.exp (-(2 * c) * μ) * Real.exp (c * δ) := by
        gcongr
        linarith [Real.add_one_le_exp (c * δ)]
    _ = Real.exp (-(2 * c) * μ + c * δ) := by rw [Real.exp_add]
    _ ≤ Real.exp (-(c * δ)) := by
        rw [Real.exp_le_exp]; nlinarith

theorem integral_exp_driftStep (ρW : Measure ℝ) (μ t : ℝ) :
    ∫ y, Real.exp (t * y) ∂(driftStep ρW μ) = Real.exp (t * μ) * ∫ w, Real.exp (t * w) ∂ρW := by
  unfold driftStep
  rw [integral_map (by fun_prop) (by fun_prop), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [mul_add, Real.exp_add]; ring

theorem integrable_exp_driftStep (ρW : Measure ℝ) (μ t : ℝ)
    (h : Integrable (fun w => Real.exp (t * w)) ρW) :
    Integrable (fun y => Real.exp (t * y)) (driftStep ρW μ) := by
  unfold driftStep
  refine (integrable_map_measure (by fun_prop) (by fun_prop)).mpr ?_
  refine (h.const_mul (Real.exp (t * μ))).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Function.comp_apply, mul_add, Real.exp_add]; ring

/-- **W-7, positive drift**: for `Y = W + μ`, `μ ≥ δ > 0`,
`P(S_m ≤ -x) ≤ e^{-c (x + δ m)}` with `c = driftRate D θ δ`. -/
theorem measureReal_partialSum_le_neg_of_stepLaw (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) {δ μ : ℝ} (hδ : 0 < δ) (hμ : δ ≤ μ) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    haveI := hW.isProbabilityMeasure
    (pathLaw (driftStep ρW μ)).real {ω | partialSum m ω ≤ -x} ≤
      Real.exp (-(driftRate D θ δ * (x + δ * m))) := by
  have := hW.isProbabilityMeasure
  set c := driftRate D θ δ
  have hc : 0 < c := driftRate_pos hθ hD hδ
  obtain ⟨hi, hle⟩ := integral_exp_drift_le hW hθ hD hδ hμ (t := -(2 * c))
    (by rw [abs_neg, abs_of_pos (by linarith)])
  have hint := integrable_exp_driftStep ρW μ _ hi
  have hch := measureReal_partialSum_le_neg_le (ρ := driftStep ρW μ) (l := 2 * c) (by linarith)
    (by simpa using hint) m x
  rw [show -(2 * c) = -(2 * c) from rfl] at hch
  have hM : ∫ y, Real.exp (-(2 * c) * y) ∂(driftStep ρW μ) ≤ Real.exp (-(c * δ)) := by
    rw [integral_exp_driftStep]; exact hle
  have hM0 : 0 ≤ ∫ y, Real.exp (-(2 * c) * y) ∂(driftStep ρW μ) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  calc _ ≤ Real.exp (-(2 * c) * x) * (∫ y, Real.exp (-(2 * c) * y) ∂(driftStep ρW μ)) ^ m := hch
    _ ≤ Real.exp (-(2 * c) * x) * Real.exp (-(c * δ)) ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hM m) (Real.exp_pos _).le
    _ = Real.exp (-(2 * c) * x - c * δ * m) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(c * (x + δ * m))) := by
        rw [Real.exp_le_exp]; nlinarith

/-- **W-7, negative drift**: for `Y = W + μ`, `μ ≤ -δ < 0`,
`P(S_m ≥ x) ≤ e^{-c (x + δ m)}`. -/
theorem measureReal_partialSum_ge_of_stepLaw (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) {δ μ : ℝ} (hδ : 0 < δ) (hμ : μ ≤ -δ) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    haveI := hW.isProbabilityMeasure
    (pathLaw (driftStep ρW μ)).real {ω | x ≤ partialSum m ω} ≤
      Real.exp (-(driftRate D θ δ * (x + δ * m))) := by
  have := hW.isProbabilityMeasure
  set c := driftRate D θ δ
  have hc : 0 < c := driftRate_pos hθ hD hδ
  -- reflect: `E e^{2c (W + μ)} = e^{-2c (-μ)} E e^{2c W}` and `-μ ≥ δ`
  obtain ⟨hi, hle⟩ := integral_exp_drift_le hW hθ hD hδ (μ := -μ) (by linarith) (t := 2 * c)
    (by rw [abs_of_pos (by linarith)])
  have hint := integrable_exp_driftStep ρW μ _ hi
  have hch := measureReal_partialSum_ge_le (ρ := driftStep ρW μ) (l := 2 * c) (by linarith)
    hint m x
  have hM : ∫ y, Real.exp (2 * c * y) ∂(driftStep ρW μ) ≤ Real.exp (-(c * δ)) := by
    rw [integral_exp_driftStep]
    calc Real.exp (2 * c * μ) * ∫ w, Real.exp (2 * c * w) ∂ρW
        = Real.exp (-(2 * c) * -μ) * ∫ w, Real.exp (2 * c * w) ∂ρW := by ring_nf
      _ ≤ _ := hle
  have hM0 : 0 ≤ ∫ y, Real.exp (2 * c * y) ∂(driftStep ρW μ) :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  calc _ ≤ Real.exp (-(2 * c) * x) * (∫ y, Real.exp (2 * c * y) ∂(driftStep ρW μ)) ^ m := hch
    _ ≤ Real.exp (-(2 * c) * x) * Real.exp (-(c * δ)) ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hM m) (Real.exp_pos _).le
    _ = Real.exp (-(2 * c) * x - c * δ * m) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(c * (x + δ * m))) := by
        rw [Real.exp_le_exp]; nlinarith

/-- **W-7 for increments**: `P(Z_j - Z_i ≤ -x) ≤ e^{-c (x + δ (j - i))}` for `μ ≥ δ > 0`. -/
theorem measureReal_increment_le_of_stepLaw (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) {δ μ : ℝ} (hδ : 0 < δ) (hμ : δ ≤ μ) {i j : ℕ} (hij : i ≤ j) {x : ℝ}
    (hx : 0 ≤ x) :
    haveI := hW.isProbabilityMeasure
    (pathLaw (driftStep ρW μ)).real {ω | partialSum j ω - partialSum i ω ≤ -x} ≤
      Real.exp (-(driftRate D θ δ * (x + δ * (j - i : ℕ)))) := by
  have := hW.isProbabilityMeasure
  have h := measureReal_increment_eq (ρ := driftStep ρW μ) hij (E := Iic (-x)) measurableSet_Iic
  simp only [mem_Iic] at h
  rw [h]
  exact measureReal_partialSum_le_neg_of_stepLaw hW hθ hD hδ hμ (j - i) hx

/-- **W-7, union over pairs**: `P(∃ i ≤ j ≤ k, Z_j - Z_i ≤ -x) ≤ (k + 1)² e^{-c x}` for
`μ ≥ δ > 0` and `x ≥ 0`. -/
theorem measureReal_exists_increment_le_of_stepLaw (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) {δ μ : ℝ} (hδ : 0 < δ) (hμ : δ ≤ μ) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    haveI := hW.isProbabilityMeasure
    (pathLaw (driftStep ρW μ)).real
        {ω | ∃ i ≤ k, ∃ j ≤ k, i ≤ j ∧ partialSum j ω - partialSum i ω ≤ -x} ≤
      ((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(driftRate D θ δ * x)) := by
  have := hW.isProbabilityMeasure
  set c := driftRate D θ δ
  have hc : 0 < c := driftRate_pos hθ hD hδ
  have hset : {ω | ∃ i ≤ k, ∃ j ≤ k, i ≤ j ∧ partialSum j ω - partialSum i ω ≤ -x} ⊆
      ⋃ p ∈ (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter (fun p : ℕ × ℕ => p.1 ≤ p.2),
        {ω | partialSum p.2 ω - partialSum p.1 ω ≤ -x} := by
    rintro ω ⟨i, hi, j, hj, hij, h⟩
    simp only [mem_iUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨(i, j), ⟨⟨by omega, by omega⟩, hij⟩, h⟩
  refine (measureReal_mono hset (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  calc ∑ p ∈ (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter (fun p : ℕ × ℕ => p.1 ≤ p.2),
        (pathLaw (driftStep ρW μ)).real {ω | partialSum p.2 ω - partialSum p.1 ω ≤ -x}
      ≤ ∑ p ∈ (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter (fun p : ℕ × ℕ => p.1 ≤ p.2),
          Real.exp (-(c * x)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        simp only [Finset.mem_filter] at hp
        refine (measureReal_increment_le_of_stepLaw hW hθ hD hδ hμ hp.2 hx).trans ?_
        rw [Real.exp_le_exp]
        have : 0 ≤ δ * ((p.2 - p.1 : ℕ) : ℝ) := by positivity
        nlinarith
    _ ≤ ∑ p ∈ Finset.range (k + 1) ×ˢ Finset.range (k + 1), Real.exp (-(c * x)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => (Real.exp_pos _).le
    _ = ((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(c * x)) := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, nsmul_eq_mul]
        push_cast; ring

/-- **W-7, all times**: `P(∃ m, Z_m ≤ -x) ≤ e^{-c x} / (1 - e^{-c δ})` for `μ ≥ δ > 0`,
`x > 0`; in particular `-min_m Z_m` has an exponential tail uniformly over the class. -/
theorem measureReal_exists_partialSum_le_of_stepLaw (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) {δ μ : ℝ} (hδ : 0 < δ) (hμ : δ ≤ μ) {x : ℝ} (hx : 0 < x) :
    haveI := hW.isProbabilityMeasure
    (pathLaw (driftStep ρW μ)).real {ω | ∃ m, partialSum m ω ≤ -x} ≤
      Real.exp (-(driftRate D θ δ * x)) / (1 - Real.exp (-(driftRate D θ δ * δ))) := by
  have := hW.isProbabilityMeasure
  set c := driftRate D θ δ
  have hc : 0 < c := driftRate_pos hθ hD hδ
  set r := Real.exp (-(c * δ))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hterm : ∀ m : ℕ, (pathLaw (driftStep ρW μ)).real {ω | partialSum m ω ≤ -x} ≤
      Real.exp (-(c * x)) * r ^ m := by
    intro m
    refine (measureReal_partialSum_le_neg_of_stepLaw hW hθ hD hδ hμ m hx.le).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hsum : Summable fun m : ℕ => Real.exp (-(c * x)) * r ^ m :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hset : {ω | ∃ m, partialSum m ω ≤ -x} = ⋃ m : ℕ, {ω | partialSum m ω ≤ -x} := by
    ext ω; simp
  rw [hset]
  have hle : (pathLaw (driftStep ρW μ)) (⋃ m : ℕ, {ω | partialSum m ω ≤ -x}) ≤
      ENNReal.ofReal (∑' m : ℕ, Real.exp (-(c * x)) * r ^ m) := by
    refine (measure_iUnion_le _).trans ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum]
    refine ENNReal.tsum_le_tsum fun m => ?_
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hterm m)
  calc (pathLaw (driftStep ρW μ)).real (⋃ m : ℕ, {ω | partialSum m ω ≤ -x})
      ≤ (ENNReal.ofReal (∑' m : ℕ, Real.exp (-(c * x)) * r ^ m)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = ∑' m : ℕ, Real.exp (-(c * x)) * r ^ m :=
        ENNReal.toReal_ofReal (tsum_nonneg fun m => by positivity)
    _ = Real.exp (-(c * x)) / (1 - r) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

end PGM.WienerHopf
