import PLAStochastic.Index.GEP.StrongApprox.LocalCLT.SmoothedDensity
import PLAStochastic.Index.GEP.StrongApprox.Saddle.GlobalRate

/-! # WP5: exact exponential tilting of Gaussian-smoothed sums -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set
open scoped Real ENNReal NNReal

/-- Completing the square in the smoothing kernel. -/
theorem sa_gaussianPDFReal_tilt {v : ℝ≥0} (hv : v ≠ 0) (lam x y : ℝ) :
    Real.exp (lam * y) * gaussianPDFReal (x - v * lam) v y =
      Real.exp (lam * x - v * lam ^ 2 / 2) * gaussianPDFReal x v y := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  unfold gaussianPDFReal
  rw [mul_left_comm, mul_left_comm (Real.exp (lam * x - v * lam ^ 2 / 2)),
    ← Real.exp_add, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- The density identity uses the actual tilted measure, including its exact
normalizing constant. -/
theorem saGaussianDensity_tilt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ≥0} (hv : v ≠ 0) {lam : ℝ}
    (hM : Integrable (fun y : ℝ => Real.exp (lam * y)) μ) (x : ℝ) :
    saGaussianDensity μ v x =
      Real.exp (cgf id μ lam + v * lam ^ 2 / 2 - lam * x) *
        saGaussianDensity (μ.tilted (fun y => lam * y)) v (x - v * lam) := by
  have hpt (y : ℝ) :
      Real.exp (lam * y - cgf id μ lam) * gaussianPDFReal (x - v * lam) v y =
        Real.exp (lam * x - v * lam ^ 2 / 2 - cgf id μ lam) * gaussianPDFReal x v y := by
    rw [Real.exp_sub (lam * y), Real.exp_sub (lam * x - v * lam ^ 2 / 2),
      div_mul_eq_mul_div, sa_gaussianPDFReal_tilt hv, div_mul_eq_mul_div]
  have hi : saGaussianDensity (μ.tilted (fun y => lam * y)) v (x - v * lam) =
      Real.exp (lam * x - v * lam ^ 2 / 2 - cgf id μ lam) *
        saGaussianDensity μ v x := by
    unfold saGaussianDensity
    have ht := integral_tilted_mul_eq_cgf (X := id) (μ := μ)
      (gaussianPDFReal (x - v * lam) v) hM
    simp only [id_eq] at ht
    rw [ht]
    simp only [smul_eq_mul, hpt]
    rw [integral_const_mul]
  rw [hi, ← mul_assoc, ← Real.exp_add]
  have : cgf id μ lam + v * lam ^ 2 / 2 - lam * x +
      (lam * x - v * lam ^ 2 / 2 - cgf id μ lam) = 0 := by ring
  rw [this, Real.exp_zero, one_mul]

/-- Moment generating functions multiply under convolution, without auxiliary
random variables or an independence certificate. -/
theorem sa_mgf_conv (μ ρ : Measure ℝ) [SFinite μ] [SFinite ρ] (lam : ℝ) :
    mgf id (μ ∗ ρ) lam = mgf id μ lam * mgf id ρ lam := by
  unfold mgf Measure.conv
  rw [integral_map (by fun_prop)
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Real.exp (lam * id x))
      ((μ.prod ρ).map (fun p : ℝ × ℝ => p.1 + p.2)))]
  simp only [id_eq, mul_add, Real.exp_add]
  convert integral_prod_mul (μ := μ) (ν := ρ) (L := ℝ)
    (fun x => Real.exp (lam * x)) (fun x => Real.exp (lam * x)) using 1

theorem sa_integrable_exp_conv {μ ρ : Measure ℝ} [SFinite μ] [SFinite ρ] {lam : ℝ}
    (hμ : Integrable (fun x : ℝ => Real.exp (lam * x)) μ)
    (hρ : Integrable (fun x : ℝ => Real.exp (lam * x)) ρ) :
    Integrable (fun x : ℝ => Real.exp (lam * x)) (μ ∗ ρ) := by
  rw [Measure.conv, integrable_map_measure (by fun_prop) (by fun_prop)]
  simpa only [Function.comp_def, mul_add, Real.exp_add] using hμ.mul_prod hρ

theorem sa_mgf_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] (lam : ℝ) (l : ℕ) :
    mgf id (convPow μ l) lam = mgf id μ lam ^ l := by
  induction l with
  | zero => simp [convPow, mgf]
  | succ l ih => rw [convPow, sa_mgf_conv, ih, pow_succ]

theorem sa_integrable_exp_convPow {μ : Measure ℝ} [IsProbabilityMeasure μ] {lam : ℝ}
    (hμ : Integrable (fun x : ℝ => Real.exp (lam * x)) μ) (l : ℕ) :
    Integrable (fun x : ℝ => Real.exp (lam * x)) (convPow μ l) := by
  induction l with
  | zero => exact integrable_dirac (by simp)
  | succ l ih => exact sa_integrable_exp_conv ih hμ

theorem sa_cgf_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] (lam : ℝ) (l : ℕ) :
    cgf id (convPow μ l) lam = (l : ℝ) * cgf id μ lam := by
  simp only [cgf, sa_mgf_convPow, Real.log_pow]

/-- Exponential tilting commutes with measurable images. -/
theorem sa_tilted_map {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (hf : Measurable f) (lam : ℝ) :
    (μ.map f).tilted (fun x => lam * x) =
      (μ.tilted (fun x => lam * f x)).map f := by
  have hi : (∫ x : ℝ, Real.exp (lam * x) ∂μ.map f) =
      ∫ x, Real.exp (lam * f x) ∂μ := integral_map hf.aemeasurable (by fun_prop)
  refine ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_tilted, lintegral_map (by fun_prop) hf,
    lintegral_map hg hf, lintegral_tilted, hi]

/-- The tilt of a convolution is the convolution of the tilted factors. -/
theorem sa_tilted_conv (μ ρ : Measure ℝ) [SFinite μ] [SFinite ρ] (lam : ℝ) :
    (μ ∗ ρ).tilted (fun x => lam * x) =
      μ.tilted (fun x => lam * x) ∗ ρ.tilted (fun x => lam * x) := by
  have hm : (∫ x, Real.exp (lam * x) ∂(μ ∗ ρ)) =
      (∫ x, Real.exp (lam * x) ∂μ) * ∫ x, Real.exp (lam * x) ∂ρ :=
    sa_mgf_conv μ ρ lam
  refine ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_tilted]
  conv_lhs => rw [Measure.conv, lintegral_map (by fun_prop) (by fun_prop)]
  conv_rhs => rw [Measure.conv, lintegral_map hg (by fun_prop)]
  rw [Measure.tilted, Measure.tilted, prod_withDensity (by fun_prop) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  apply lintegral_congr
  intro z
  change (∫ x, Real.exp (lam * x) ∂(μ.prod ρ).map (fun z : ℝ × ℝ => z.1 + z.2)) = _ at hm
  rw [hm, mul_add, Real.exp_add, mul_div_mul_comm,
    ENNReal.ofReal_mul (by positivity)]
  rfl

theorem sa_tilted_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] (lam : ℝ) (l : ℕ) :
    (convPow μ l).tilted (fun x => lam * x) =
      convPow (μ.tilted (fun x => lam * x)) l := by
  induction l with
  | zero => simp [convPow, Measure.tilted, dirac_withDensity]
  | succ l ih => rw [convPow, sa_tilted_conv, ih, convPow]

/-- Translating the summands translates the convolution by the sum of the shifts. -/
theorem sa_conv_map_sub (μ ρ : Measure ℝ) [SFinite μ] [SFinite ρ] (a b : ℝ) :
    μ.map (fun x => x - a) ∗ ρ.map (fun x => x - b) =
      (μ ∗ ρ).map (fun x => x - (a + b)) := by
  unfold Measure.conv
  rw [map_prod_map _ _ (by fun_prop) (by fun_prop),
    map_map (by fun_prop) (by fun_prop), map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
  ring

theorem sa_convPow_map_sub (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) (l : ℕ) :
    convPow (μ.map (fun x => x - a)) l = (convPow μ l).map (fun x => x - l * a) := by
  let : IsProbabilityMeasure (μ.map (fun x => x - a)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  induction l with
  | zero => simp [convPow]
  | succ l ih =>
    rw [convPow, ih, sa_conv_map_sub, ← convPow]
    congr 1
    funext x
    push_cast
    ring

/-- Translation of a measure gives an exact translation of its smoothing density. -/
theorem saGaussianDensity_map_sub (μ : Measure ℝ) (a x : ℝ) (v : ℝ≥0) :
    saGaussianDensity (μ.map (fun y => y - a)) v x = saGaussianDensity μ v (x + a) := by
  unfold saGaussianDensity
  rw [integral_map (by fun_prop) (measurable_gaussianPDFReal _ _).aestronglyMeasurable]
  simp only [gaussianPDFReal_sub]

/-- Rescaling a measure and its Gaussian kernel rescales the actual density. -/
theorem saGaussianDensity_map_inv_mul (μ : Measure ℝ) {a : ℝ} (ha : 0 < a)
    (x : ℝ) (v : ℝ≥0) :
    saGaussianDensity (μ.map (a⁻¹ * ·)) v x =
      a * saGaussianDensity μ (⟨a ^ 2, sq_nonneg a⟩ * v) (a * x) := by
  unfold saGaussianDensity
  rw [integral_map (by fun_prop) (measurable_gaussianPDFReal _ _).aestronglyMeasurable]
  simp only [gaussianPDFReal_inv_mul ha.ne', abs_of_pos ha, integral_const_mul]
  rfl

/-- Exact saddle identity for any probability law with a finite exponential
moment. The right side is the normalized, recentered tilted sum at zero. -/
theorem saGaussianDensity_convPow_tilt_at_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {lam : ℝ} (hM : Integrable (fun y : ℝ => Real.exp (lam * y)) μ)
    {v : ℝ≥0} (hv : v ≠ 0) {l : ℕ} (hl : 0 < l) (m : ℝ) :
    saGaussianDensity (convPow μ l) ((l : ℝ≥0) * v) (l * (m + v * lam)) =
      Real.exp ((l : ℝ) * (cgf id μ lam + v * lam ^ 2 / 2 - lam * (m + v * lam))) /
        Real.sqrt l *
        saGaussianDensity ((convPow ((μ.tilted (fun y => lam * y)).map (fun y => y - m)) l).map
          ((Real.sqrt l)⁻¹ * ·)) v 0 := by
  let ρ := μ.tilted (fun y => lam * y)
  let : IsProbabilityMeasure ρ := isProbabilityMeasure_tilted hM
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl
  have hls : 0 < Real.sqrt l := Real.sqrt_pos.mpr hlr
  have hlv : (l : ℝ≥0) * v ≠ 0 := mul_ne_zero (by exact_mod_cast hl.ne') hv
  have ht := saGaussianDensity_tilt (convPow μ l) hlv (sa_integrable_exp_convPow hM l)
    ((l : ℝ) * (m + v * lam))
  rw [sa_cgf_convPow, sa_tilted_convPow] at ht
  have hx : (l : ℝ) * (m + v * lam) - ↑((l : ℝ≥0) * v) * lam = l * m := by
    push_cast
    ring
  have he : (l : ℝ) * cgf id μ lam + ↑((l : ℝ≥0) * v) * lam ^ 2 / 2 -
      lam * ((l : ℝ) * (m + v * lam)) =
      (l : ℝ) * (cgf id μ lam + v * lam ^ 2 / 2 - lam * (m + v * lam)) := by
    push_cast
    ring
  rw [hx, he] at ht
  have hscale := saGaussianDensity_map_inv_mul
    (convPow (ρ.map (fun y => y - m)) l) hls 0 v
  have hsq : (⟨Real.sqrt l ^ 2, sq_nonneg (Real.sqrt l)⟩ : ℝ≥0) = (l : ℝ≥0) := by
    ext
    change Real.sqrt (l : ℝ) ^ 2 = (l : ℝ)
    exact Real.sq_sqrt (Nat.cast_nonneg l)
  rw [hsq, mul_zero] at hscale
  conv_rhs at hscale => rw [sa_convPow_map_sub, saGaussianDensity_map_sub, zero_add]
  change _ = Real.sqrt l * saGaussianDensity (convPow ρ l) ((l : ℝ≥0) * v) (l * m) at hscale
  rw [ht]
  change _ = _ * saGaussianDensity ((convPow (ρ.map (fun y => y - m)) l).map _) v 0
  rw [hscale]
  field_simp
  rfl

end

end PGM
