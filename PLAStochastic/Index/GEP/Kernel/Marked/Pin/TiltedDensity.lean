import PLAStochastic.Index.GEP.Kernel.Tilt.EndpointBounds
import PLAStochastic.Index.GEP.Kernel.Row.ChapmanKolmogorov
import PLAStochastic.Index.GEP.Kernel.Marked.Density

/-! # Pointwise exponential conjugacy of actual killed density representatives -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- The fixed pointwise representative of the exponentially tilted density. -/
def kernelTiltDensity (ν : ProbabilityMeasure ℝ) (lam : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (lam * x - cgf id (ν : Measure ℝ) lam) * f x

/-- The real and complex actual killed iterates agree under the canonical embedding. -/
theorem kernel_killed_ofReal (J : Set ℝ) (μ : Measure ℝ) (β a : ℝ)
    (u : ℝ → ℝ) (n : ℕ) :
    (kStep J μ β a)^[n] (fun x => (u x : ℂ)) =
      fun y => (((krStep J μ β a)^[n] u) y : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext y
    exact kStep_ofReal μ _ y

/-- The real conjugacy is inherited from the proved complex operator identity. -/
theorem kernel_krKilled_eq_tilt (J : Set ℝ) (ν : ProbabilityMeasure ℝ)
    (β : ℝ) {a lam : ℝ} (ha : a ≠ 0)
    (hM : Integrable (fun x : ℝ => Real.exp (lam * x)) (ν : Measure ℝ))
    (u : ℝ → ℝ) (n : ℕ) (y : ℝ) :
    ((krStep J (ν : Measure ℝ) β a)^[n] u) y =
      Real.exp ((n : ℝ) * cgf id (ν : Measure ℝ) lam - lam * (y + n * β) / a) *
        ((krStep J ((ν : Measure ℝ).tilted (fun x => lam * x)) β a)^[n]
          (fun z => Real.exp (lam * z / a) * u z)) y := by
  have hh := kernel_killed_eq_tilt J (ν : Measure ℝ) β ha hM (fun z => (u z : ℂ)) n y
  have he : (fun z => Real.exp (lam * z / a) • (u z : ℂ)) =
      fun z => ((Real.exp (lam * z / a) * u z : ℝ) : ℂ) := by
    funext z
    simp
  rw [he, kernel_killed_ofReal, kernel_killed_ofReal] at hh
  simp only [Complex.real_smul] at hh
  exact_mod_cast hh

/-- The path-defined density is exactly the row of the last one-step density. -/
theorem kernel_krDens_eq_row {J : Set ℝ} (hJ : MeasurableSet J)
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (β a : ℝ) (n : ℕ) (y z : ℝ) :
    krDens J ν f β a n y z =
      krRow J (ν : Measure ℝ) β a (n - 1) (fun u => krKer J f β a u z) y := by
  have hm : Measurable (fun u => krKer J f β a u z) :=
    (measurable_krKer_prod hJ hf β a).comp (measurable_id.prodMk measurable_const)
  rw [krRow_eq_integral hJ ν β a (n - 1) hm (fun u => abs_krKer_le hf0 hfD u z)]
  rfl

/-- The density is a genuine iterate; its terminal kernel already contains the final projection. -/
theorem kernel_krDens_eq_iterate {J : Set ℝ} (hJ : MeasurableSet J)
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (β a : ℝ) (n : ℕ) (y z : ℝ) :
    krDens J ν f β a n y z =
      ((krStep J (ν : Measure ℝ) β a)^[n - 1] (fun u => krKer J f β a u z)) y := by
  rw [kernel_krDens_eq_row hJ ν hf hf0 hfD, krRow]
  have he : J.indicator (fun u => krKer J f β a u z) = fun u => krKer J f β a u z := by
    funext u
    by_cases hu : u ∈ J
    · simp only [indicator_of_mem hu]
    · simp only [indicator_of_notMem hu, krKer_eq_zero_of_left_notMem hu]
  rw [he]

/-- One-step density conjugacy holds at every pair of endpoints for the fixed representative. -/
theorem kernel_krKer_tilt (J : Set ℝ) (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ) (β a lam y z : ℝ) :
    krKer J (kernelTiltDensity ν lam f) β a y z =
      Real.exp (lam * β / a - cgf id (ν : Measure ℝ) lam + lam * (y - z) / a) *
        krKer J f β a y z := by
  unfold krKer kernelTiltDensity
  have he : lam * ((y + β - z) / a) - cgf id (ν : Measure ℝ) lam =
      lam * β / a - cgf id (ν : Measure ℝ) lam + lam * (y - z) / a := by ring
  rw [he]
  ring

/-- Pointwise density conjugacy, including both interval projections and every endpoint. -/
theorem kernel_krDens_tilt {J : Set ℝ} (hJ : MeasurableSet J)
    (ν τ : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D E : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    {lam : ℝ} (hM : Integrable (fun x : ℝ => Real.exp (lam * x)) (ν : Measure ℝ))
    (hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x))
    (hftD : ∀ x, kernelTiltDensity ν lam f x ≤ E)
    (β : ℝ) {a : ℝ} (ha : a ≠ 0) {n : ℕ} (hn : 1 ≤ n) (y z : ℝ) :
    krDens J ν f β a n y z =
      Real.exp (-(n : ℝ) * (lam * β / a - cgf id (ν : Measure ℝ) lam) + lam * (z - y) / a) *
        krDens J τ (kernelTiltDensity ν lam f) β a n y z := by
  have hft : Measurable (kernelTiltDensity ν lam f) := by unfold kernelTiltDensity; fun_prop
  have hft0 (x : ℝ) : 0 ≤ kernelTiltDensity ν lam f x :=
    mul_nonneg (Real.exp_nonneg _) (hf0 x)
  rw [kernel_krDens_eq_iterate hJ ν hf hf0 hfD,
    kernel_krKilled_eq_tilt J ν β ha hM,
    kernel_krDens_eq_iterate hJ τ hft hft0 hftD, hτ]
  have he : (fun u => Real.exp (lam * u / a) * krKer J f β a u z) =
      fun u => Real.exp (cgf id (ν : Measure ℝ) lam - lam * β / a + lam * z / a) *
        krKer J (kernelTiltDensity ν lam f) β a u z := by
    funext u
    rw [kernel_krKer_tilt, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he]
  have hconst (c : ℝ) (u : ℝ → ℝ) (m : ℕ) :
      (krStep J ((ν : Measure ℝ).tilted (fun x => lam * x)) β a)^[m] (fun x => c * u x) =
      fun x => c * ((krStep J ((ν : Measure ℝ).tilted (fun x => lam * x)) β a)^[m] u) x := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      funext x
      by_cases hx : x ∈ J
      · simp only [krStep, indicator_of_mem hx]
        exact integral_const_mul c _
      · simp only [krStep, indicator_of_notMem hx, mul_zero]
  rw [hconst, ← mul_assoc, ← Real.exp_add]
  congr 2
  rw [Nat.cast_sub hn]
  push_cast
  ring


/-- The selected tilted density represents the actual tilted measure. -/
theorem kernel_tilt_density_measure (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hνf : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {lam : ℝ} (hM : Integrable (fun x : ℝ => Real.exp (lam * x)) (ν : Measure ℝ)) :
    (ν : Measure ℝ).tilted (fun x => lam * x) =
      volume.withDensity (fun x => ENNReal.ofReal (kernelTiltDensity ν lam f x)) := by
  have ht : (ν : Measure ℝ).tilted (fun x => lam * x) =
      (ν : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (Real.exp (lam * x - cgf id (ν : Measure ℝ) lam))) := by
    ext s hs
    rw [withDensity_apply _ hs]
    simpa only [id_eq] using
      (tilted_mul_apply_cgf' (X := id) (μ := (ν : Measure ℝ)) hs hM)
  rw [ht]
  nth_rw 1 [hνf]
  rw [← withDensity_mul volume hf.ennreal_ofReal (by fun_prop)]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (hf0 x)]
  congr 1
  unfold kernelTiltDensity
  ring

/-- The explicit representative, not merely an a.e. version, has a uniform tilted bound. -/
theorem RegLaw.kernelTiltDensity_le {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    {f : ℝ → ℝ} (hfz : ∀ x ≤ 0, f x = 0)
    (hfD : ∀ x, f x ≤ D * Real.exp (-θ * x))
    {lam : ℝ} (hlam : |lam| ≤ θ / 2) (x : ℝ) :
    kernelTiltDensity ν lam f x ≤ D * Real.exp θ := by
  have hU := hν.univClass hθ hvlo
  have hmgf : 1 ≤ mgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam :=
    hU.one_le_integral_exp_centered hlam
  have hcgf : 0 ≤ cgf (fun x : ℝ => x - 1) (ν : Measure ℝ) lam := Real.log_nonneg hmgf
  have hraw : lam ≤ cgf id (ν : Measure ℝ) lam := by
    rw [hU.kernel_raw_cgf_eq hlam]
    linarith
  by_cases hx : 0 < x
  · have he : -θ * x + (lam * x - cgf id (ν : Measure ℝ) lam) ≤ θ := by
      have hh := mul_le_mul_of_nonneg_right (abs_le.mp hlam).2 hx.le
      have hn := (abs_le.mp hlam).1
      nlinarith
    calc
      kernelTiltDensity ν lam f x ≤
          Real.exp (lam * x - cgf id (ν : Measure ℝ) lam) * (D * Real.exp (-θ * x)) :=
        mul_le_mul_of_nonneg_left (hfD x) (Real.exp_nonneg _)
      _ = D * Real.exp (-θ * x + (lam * x - cgf id (ν : Measure ℝ) lam)) := by
        rw [Real.exp_add]
        ring
      _ ≤ D * Real.exp θ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hν.D_nonneg
  · simp only [kernelTiltDensity, hfz x (not_lt.mp hx), mul_zero]
    exact mul_nonneg hν.D_nonneg (Real.exp_nonneg _)

/-- Actual tilted probability and density data, with pointwise representatives chosen once. -/
theorem RegLaw.kernel_tilt_density_data {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
      (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ∀ lam : ℝ, |lam| ≤ θ / 2 →
        ∃ τ : ProbabilityMeasure ℝ,
          (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x) ∧
          (τ : Measure ℝ) = volume.withDensity
            (fun x => ENNReal.ofReal (kernelTiltDensity ν lam f x)) ∧
          (∀ x, kernelTiltDensity ν lam f x ≤ D * Real.exp θ) := by
  obtain ⟨f, hf, hf0, hfz, hfe, hνf⟩ := hν.density
  have hfD (x : ℝ) : f x ≤ D := by
    by_cases hx : 0 < x
    · exact (hfe x).trans (mul_le_of_le_one_right hν.D_nonneg
        (Real.exp_le_one_iff.mpr (by nlinarith)))
    · rw [hfz x (not_lt.mp hx)]
      exact hν.D_nonneg
  refine ⟨f, hf, hf0, hfD, hνf, ?_⟩
  intro lam hlam
  have hU := hν.univClass hθ hvlo
  let := hU.isProbabilityMeasure_centeredTilt hlam
  have hp : IsProbabilityMeasure ((ν : Measure ℝ).tilted (fun x => lam * x)) := by
    rw [← kernel_centeredTilt_eq_raw]
    infer_instance
  let τ : ProbabilityMeasure ℝ := ⟨(ν : Measure ℝ).tilted (fun x => lam * x), hp⟩
  exact ⟨τ, rfl, kernel_tilt_density_measure ν hf hf0 hνf (hU.kernel_integrable_exp_raw hlam),
    hν.kernelTiltDensity_le hθ hvlo hfz hfe hlam⟩

/-- Pointwise conjugacy on the original regular class, with no extra tilted-law input. -/
theorem RegLaw.kernel_krDens_tilt {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
      (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      ∀ lam : ℝ, |lam| ≤ θ / 2 →
        ∃ τ : ProbabilityMeasure ℝ,
          (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x) ∧
          (τ : Measure ℝ) = volume.withDensity
            (fun x => ENNReal.ofReal (kernelTiltDensity ν lam f x)) ∧
          ∀ J : Set ℝ, MeasurableSet J → ∀ β a : ℝ, a ≠ 0 →
          ∀ n : ℕ, 1 ≤ n → ∀ y z : ℝ,
            krDens J ν f β a n y z =
              Real.exp (-(n : ℝ) * (lam * β / a - cgf id (ν : Measure ℝ) lam) +
                lam * (z - y) / a) * krDens J τ (kernelTiltDensity ν lam f) β a n y z := by
  obtain ⟨f, hf, hf0, hfD, hνf, hdata⟩ := hν.kernel_tilt_density_data hθ hvlo
  refine ⟨f, hf, hf0, hfD, hνf, ?_⟩
  intro lam hlam
  obtain ⟨τ, hτ, hτf, hftD⟩ := hdata lam hlam
  refine ⟨τ, hτ, hτf, ?_⟩
  intro J hJ β a ha n hn y z
  exact PGM.kernel_krDens_tilt hJ ν τ hf hf0 hfD
    ((hν.univClass hθ hvlo).kernel_integrable_exp_raw hlam) hτ hftD β ha hn y z


/-- Two forward pins with exchanged endpoints cancel the endpoint tilt exactly. -/
theorem kernel_krDens_pin_tilt {J : Set ℝ} (hJ : MeasurableSet J)
    (ν τ : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D E : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    {lam : ℝ} (hM : Integrable (fun x : ℝ => Real.exp (lam * x)) (ν : Measure ℝ))
    (hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x))
    (hftD : ∀ x, kernelTiltDensity ν lam f x ≤ E)
    (β : ℝ) {a : ℝ} (ha : a ≠ 0) {L M : ℕ} (hL : 1 ≤ L) (hN : 1 ≤ M) (y z : ℝ) :
    krDens J ν f β a L y z * krDens J ν f β a M z y =
      Real.exp (-((L : ℝ) + M) * (lam * β / a - cgf id (ν : Measure ℝ) lam)) *
        (krDens J τ (kernelTiltDensity ν lam f) β a L y z *
          krDens J τ (kernelTiltDensity ν lam f) β a M z y) := by
  rw [kernel_krDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD β ha hL y z,
    kernel_krDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD β ha hN z y]
  rw [mul_mul_mul_comm, ← Real.exp_add]
  congr 2
  ring

/-- Equivalently, forward and reverse pins with the same ordered endpoints cancel exactly. -/
theorem kernel_krDens_reverse_pin_tilt {J : Set ℝ} (hJ : MeasurableSet J)
    (ν τ : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D E : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    {lam : ℝ} (hM : Integrable (fun x : ℝ => Real.exp (lam * x)) (ν : Measure ℝ))
    (hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x))
    (hftD : ∀ x, kernelTiltDensity ν lam f x ≤ E)
    (β : ℝ) {a : ℝ} (ha : a ≠ 0) {L M : ℕ} (hL : 1 ≤ L) (hN : 1 ≤ M) (y z : ℝ) :
    krDens J ν f β a L y z * krDens J ν f (-β) (-a) M y z =
      Real.exp (-((L : ℝ) + M) * (lam * β / a - cgf id (ν : Measure ℝ) lam)) *
        (krDens J τ (kernelTiltDensity ν lam f) β a L y z *
          krDens J τ (kernelTiltDensity ν lam f) (-β) (-a) M y z) := by
  rw [kernel_krDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD β ha hL y z,
    kernel_krDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD (-β) (neg_ne_zero.mpr ha) hN y z]
  rw [mul_mul_mul_comm, ← Real.exp_add]
  congr 2
  simp only [mul_neg, div_neg]
  ring

/-- Internal endpoint exponents cancel pointwise in the actual marked density integral. -/
theorem kernel_markedDens_tilt {J : Set ℝ} (hJ : MeasurableSet J)
    (ν τ : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D E : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    {lam : ℝ} (hM : Integrable (fun x : ℝ => Real.exp (lam * x)) (ν : Measure ℝ))
    (hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x))
    (hftD : ∀ x, kernelTiltDensity ν lam f x ≤ E)
    (β t : ℝ) {a : ℝ} (ha : a ≠ 0) {l r : ℕ} (hl : 1 ≤ l) (hr : 1 ≤ r) (y z : ℝ) :
    kernelMarkedDens J ν f β a t l r y z =
      Real.exp (-((l : ℝ) + r) * (lam * β / a - cgf id (ν : Measure ℝ) lam) +
        lam * (z - y) / a + lam * t - lam * β / a) *
        kernelMarkedDens J τ (kernelTiltDensity ν lam f) β a t l r y z := by
  unfold kernelMarkedDens
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [kernel_krDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD β ha hl y u,
    kernel_krDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD β ha hr (u + β - a * t) z]
  rw [mul_mul_mul_comm, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- A marked pin and an oppositely ordered forward pin lose every endpoint exponent.
The remaining deterministic insertion factor is exactly `lam*t-lam*β/a`. -/
theorem kernel_marked_pin_tilt {J : Set ℝ} (hJ : MeasurableSet J)
    (ν τ : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D E : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    {lam : ℝ} (hM : Integrable (fun x : ℝ => Real.exp (lam * x)) (ν : Measure ℝ))
    (hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x))
    (hftD : ∀ x, kernelTiltDensity ν lam f x ≤ E)
    (β t : ℝ) {a : ℝ} (ha : a ≠ 0) {l r M : ℕ}
    (hl : 1 ≤ l) (hr : 1 ≤ r) (hN : 1 ≤ M) (y z : ℝ) :
    kernelMarkedDens J ν f β a t l r y z * krDens J ν f β a M z y =
      Real.exp (-((l : ℝ) + r + M) * (lam * β / a - cgf id (ν : Measure ℝ) lam) +
        lam * t - lam * β / a) *
        (kernelMarkedDens J τ (kernelTiltDensity ν lam f) β a t l r y z *
          krDens J τ (kernelTiltDensity ν lam f) β a M z y) := by
  rw [kernel_markedDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD β t ha hl hr y z,
    kernel_krDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD β ha hN z y]
  rw [mul_mul_mul_comm, ← Real.exp_add]
  congr 2
  ring

end
end PGM
