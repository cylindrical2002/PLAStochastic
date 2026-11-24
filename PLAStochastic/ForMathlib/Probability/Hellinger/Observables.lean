import PLAStochastic.ForMathlib.Probability.Hellinger.Restriction

/-!
# Moment-controlled observables under Hellinger comparison

The observable need not be bounded. Two finite second moments give a quantitative
expectation bound, which applies to segment lengths and physical spans of stopped
paths. No independence between the stopping time and the increments is used.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem inner_toLp_eq_integral_mul {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial]
  ring

theorem norm_toLp_sq {f : α → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp_eq_integral_mul hf hf]
  simp only [pow_two]

theorem integrable_mul_of_memLp_two {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => f x * g x) μ := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial]
  ring

theorem observable_memLp (p : HellingerDensity μ) {φ : α → ℝ}
    (hφ : Measurable φ) (hp : Integrable (fun x => φ x ^ 2 * p.density x) μ) :
    MemLp (fun x => φ x * Real.sqrt (p.density x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (hφ.mul p.measurable.sqrt).aestronglyMeasurable).2
  convert hp using 1
  funext x
  change (φ x * Real.sqrt (p.density x)) ^ 2 = φ x ^ 2 * p.density x
  rw [mul_pow, Real.sq_sqrt (p.nonneg x)]

theorem integrable_observable (p : HellingerDensity μ) {φ : α → ℝ}
    (hφ : Measurable φ) (hp : Integrable (fun x => φ x ^ 2 * p.density x) μ) :
    Integrable (fun x => φ x * p.density x) μ := by
  have h := integrable_mul_of_memLp_two (p.observable_memLp hφ hp) p.sqrt_memLp
  convert h using 1
  funext x
  rw [mul_assoc, Real.mul_self_sqrt (p.nonneg x)]

/-- A shared observable has an expectation error controlled by its two second moments. -/
theorem abs_integral_observable_sub_le (p q : HellingerDensity μ) {φ : α → ℝ}
    (hφ : Measurable φ)
    (hp : Integrable (fun x => φ x ^ 2 * p.density x) μ)
    (hq : Integrable (fun x => φ x ^ 2 * q.density x) μ) :
    |(∫ x, φ x * p.density x ∂μ) - (∫ x, φ x * q.density x ∂μ)| ≤
      p.hellinger q * Real.sqrt
        (2 * ((∫ x, φ x ^ 2 * p.density x ∂μ) +
          (∫ x, φ x ^ 2 * q.density x ∂μ))) := by
  let up := (p.observable_memLp hφ hp).toLp
    (fun x => φ x * Real.sqrt (p.density x))
  let uq := (q.observable_memLp hφ hq).toLp
    (fun x => φ x * Real.sqrt (q.density x))
  have hip : ‖up‖ ^ 2 = ∫ x, φ x ^ 2 * p.density x ∂μ := by
    rw [norm_toLp_sq]
    congr 1
    funext x
    rw [mul_pow, Real.sq_sqrt (p.nonneg x)]
  have hiq : ‖uq‖ ^ 2 = ∫ x, φ x ^ 2 * q.density x ∂μ := by
    rw [norm_toLp_sq]
    congr 1
    funext x
    rw [mul_pow, Real.sq_sqrt (q.nonneg x)]
  have hnorm : ‖up + uq‖ ≤ Real.sqrt
      (2 * ((∫ x, φ x ^ 2 * p.density x ∂μ) +
        (∫ x, φ x ^ 2 * q.density x ∂μ))) := by
    rw [← hip, ← hiq]
    have hsum := norm_add_le up uq
    have hsquare : ‖up + uq‖ ^ 2 ≤ 2 * (‖up‖ ^ 2 + ‖uq‖ ^ 2) := by
      nlinarith [norm_nonneg up, norm_nonneg uq, norm_nonneg (up + uq),
        sq_nonneg (‖up‖ - ‖uq‖)]
    have hnon : 0 ≤ 2 * (‖up‖ ^ 2 + ‖uq‖ ^ 2) := by positivity
    nlinarith [Real.sq_sqrt hnon, Real.sqrt_nonneg (2 * (‖up‖ ^ 2 + ‖uq‖ ^ 2)),
      norm_nonneg (up + uq)]
  have hi : inner ℝ (p.root - q.root) (up + uq) =
      (∫ x, φ x * p.density x ∂μ) - (∫ x, φ x * q.density x ∂μ) := by
    rw [← integral_sub (p.integrable_observable hφ hp) (q.integrable_observable hφ hq),
      L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub p.root q.root, Lp.coeFn_add up uq, p.root_ae, q.root_ae,
      (p.observable_memLp hφ hp).coeFn_toLp,
      (q.observable_memLp hφ hq).coeFn_toLp] with x hsub hadd hpr hqr hup huq
    simp only [hsub, hadd, Pi.sub_apply, Pi.add_apply, hpr, hqr,
      show up x = φ x * Real.sqrt (p.density x) from hup,
      show uq x = φ x * Real.sqrt (q.density x) from huq,
      RCLike.inner_apply, conj_trivial]
    calc
      _ = φ x * ((Real.sqrt (p.density x)) ^ 2 -
          (Real.sqrt (q.density x)) ^ 2) := by ring
      _ = _ := by rw [Real.sq_sqrt (p.nonneg x), Real.sq_sqrt (q.nonneg x)]; ring
  rw [← hi]
  calc
    |inner ℝ (p.root - q.root) (up + uq)| ≤ ‖p.root - q.root‖ * ‖up + uq‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖p.root - q.root‖ * Real.sqrt
        (2 * ((∫ x, φ x ^ 2 * p.density x ∂μ) +
          (∫ x, φ x ^ 2 * q.density x ∂μ))) :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = _ := by rw [hellinger, dist_eq_norm]

end

end ProbabilityTheory.HellingerDensity
