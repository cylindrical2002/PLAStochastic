import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.DiracBridge
import PLAStochastic.Index.GEP.Kernel.Marked.Pin.AllSlopes

/-!
# Estimates for the actual short downward bridge weight

The deterministic downward bridge forces `a=(w+1)/x`. Its slope Jacobian
multiplies the genuine opposite upward pin, rather than an unspecified bounded
weight. The latter pin supplies the cancelling `1/a` factor. Outer Green and
length rewards can subsequently multiply this density.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 800000

/-- The genuine opposite pin evaluated at the deterministic bridge's slope,
including the actual `1/x` coarea Jacobian. -/
def kernelDiracPin (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w : ℝ) (M : ℕ) (x : ℝ) : ℝ :=
  krDens (Icc 0 w) ν f 1 ((w + 1) / x) M 0 w / x

theorem kernelDiracPin_nonneg (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) (w : ℝ) (M : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ kernelDiracPin ν f w M x :=
  div_nonneg (krDens_nonneg ν hf0 _ _ _) hx

theorem measurable_kernelDiracPin (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (w : ℝ) (M : ℕ) : Measurable (kernelDiracPin ν f w M) := by
  exact (measurable_krDens_param ν measurableSet_Icc hf measurable_const
    (measurable_const.div measurable_id) measurable_const measurable_const M).div measurable_id

/-- The explicit Dirac mixture density, now with its genuine other-pin weight,
equals the actual coarea evaluation. -/
theorem kernel_dirac_density_actual_pin (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (_hf0 : ∀ t, 0 ≤ f t) {w x : ℝ} (hw : 0 < w) (hx : 0 < x) (M : ℕ) :
    kernelDiracShortDensity x
      (fun a => ENNReal.ofReal (a * krDens (Icc 0 w) ν f 1 a M 0 w)) (-w) =
        ENNReal.ofReal (kernelDiracPin ν f w M x) := by
  rw [kernel_dirac_short_density_at_lower hw]
  rw [← ENNReal.ofReal_div_of_pos (by linarith : 0 < w + 1)]
  congr 1
  unfold kernelDiracPin
  field_simp

/-- The other pin's true inverse-slope scale cancels the Dirac Jacobian at its
root, uniformly as the designated gap tends to zero. -/
theorem kernelDiracPin_le_of_pin_bound (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    {w x B : ℝ} (hw : 0 < w) (hx : 0 < x) (M : ℕ)
    (hb : krDens (Icc 0 w) ν f 1 ((w + 1) / x) M 0 w ≤ B / ((w + 1) / x)) :
    kernelDiracPin ν f w M x ≤ B / (w + 1) := by
  unfold kernelDiracPin
  apply (div_le_div_of_nonneg_right hb hx.le).trans_eq
  field_simp

/-- The actual short bridge has a spectral bound whenever its root slope is
above a fixed floor. No input-tail exponent is needed in this range. -/
theorem kernel_regLaw_dirac_pin_spectral (D θ vlo vhi a₀ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (ha₀ : 0 < a₀) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
      ∀ w x : ℝ, 1 ≤ w → 0 < x → a₀ ≤ (w + 1) / x →
      ∀ M : ℕ, 1 ≤ M →
        kernelDiracPin ν f w M x ≤
          (D / (w + 1)) * (1 + 3 * Real.sqrt (D * w / a₀)) *
            Real.exp (-(c * ((M : ℝ) - 2) / (2 * w ^ 2))) := by
  obtain ⟨c, hc, hb⟩ := kernel_regLaw_density_spectral_slope D θ vlo vhi a₀ hD hθ hvlo hv ha₀
  refine ⟨c, hc, ?_⟩
  intro ν hν f hf hf0 hfD w x hw hx ha M hM
  have hw0 : 0 < w := by linarith
  have ha0 : 0 < (w + 1) / x := div_pos (by linarith) hx
  have hh := hb ν hν f hf hf0 hfD 0 w 1 ((w + 1) / x) hw
    (by rwa [abs_of_pos ha0]) M hM 0 w
  rw [zero_add, abs_of_pos ha0] at hh
  have hh' := div_le_div_of_nonneg_right hh hx.le
  change kernelDiracPin ν f w M x ≤ _ at hh'
  apply hh'.trans_eq
  field_simp

/-- At the exact Dirac root the unmarked pin's endpoint tilt becomes the same
input factor `lam*x-lam/a` as for non-Dirac marked pairs. -/
theorem kernel_dirac_pin_tilt (ν τ : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D E : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    {lam : ℝ} (hM : Integrable (fun x : ℝ => Real.exp (lam * x)) (ν : Measure ℝ))
    (hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x))
    (hftD : ∀ x, kernelTiltDensity ν lam f x ≤ E)
    {w x : ℝ} (hw : 0 < w) (hx : 0 < x) {M : ℕ} (hN : 1 ≤ M) :
    kernelDiracPin ν f w M x =
      Real.exp (-(M : ℝ) * kernelTiltRate ν ((w + 1) / x) lam +
        lam * x - lam / ((w + 1) / x)) *
        kernelDiracPin τ (kernelTiltDensity ν lam f) w M x := by
  have ha : (w + 1) / x ≠ 0 := ne_of_gt (div_pos (by linarith) hx)
  unfold kernelDiracPin
  rw [kernel_krDens_tilt measurableSet_Icc ν τ hf hf0 hfD hM hτ hftD 1 ha hN 0 w]
  have he : -(M : ℝ) * (lam * 1 / ((w + 1) / x) - cgf id (ν : Measure ℝ) lam) +
      lam * (w - 0) / ((w + 1) / x) =
      -(M : ℝ) * kernelTiltRate ν ((w + 1) / x) lam + lam * x - lam / ((w + 1) / x) := by
    unfold kernelTiltRate
    field_simp
    ring
  rw [he]
  ring

/-- Arbitrary positive input weights control the genuine short Dirac pin when
its forced slope is small. The denominator is `w+1`, with no `1/x` loss. -/
theorem kernel_regLaw_dirac_pin_small_slope (D θ vlo vhi ζ : ℝ)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (hζ : 0 < ζ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ w x : ℝ, 0 < w → 0 < x → (w + 1) / x ≤ 1 / 2 →
        ∀ M : ℕ, 1 ≤ M →
          kernelDiracPin ν f w M x ≤
            (D * Real.exp θ / (w + 1)) *
              Real.exp (ζ * x - c * M / ((w + 1) / x)) := by
  obtain ⟨lam, hlam, hlζ, hlθ, _, hrate⟩ :=
    kernel_regLaw_arbitrary_small_tilt D θ vlo vhi ζ hθ hvlo hv hζ
  refine ⟨lam / 4, by positivity, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hfD, hνf, hdata⟩ := hν.kernel_tilt_density_data hθ hvlo
  refine ⟨f, hf, hf0, hfD, hνf, ?_⟩
  intro w x hw hx halo M hM
  have hlabs : |lam| ≤ θ / 2 := by rwa [abs_of_pos hlam]
  obtain ⟨τ, hτ, hτf, hftD⟩ := hdata lam hlabs
  have hft0 (t : ℝ) : 0 ≤ kernelTiltDensity ν lam f t :=
    mul_nonneg (Real.exp_nonneg _) (hf0 t)
  let a := (w + 1) / x
  have ha : 0 < a := div_pos (by linarith) hx
  have htbound : kernelDiracPin τ (kernelTiltDensity ν lam f) w M x ≤ D * Real.exp θ / (w + 1) :=
    kernelDiracPin_le_of_pin_bound τ _ hw hx M (by
      simpa only [abs_of_pos ha] using krDens_le_div (J := Icc 0 w) (β := 1) (a := a) τ hft0 hftD M 0 w)
  rw [kernel_dirac_pin_tilt ν τ hf hf0 hfD
    ((hν.univClass hθ hvlo).kernel_integrable_exp_raw hlabs) hτ hftD hw hx hM]
  have he : -(M : ℝ) * kernelTiltRate ν a lam + lam * x - lam / a ≤
      ζ * x - lam / 4 * M / a := by
    have hh := mul_le_mul_of_nonneg_left (hrate ν hν a ha halo) (Nat.cast_nonneg (α := ℝ) M)
    have hh' := mul_le_mul_of_nonneg_right hlζ hx.le
    have he' : (M : ℝ) * (lam / (4 * a)) = lam / 4 * M / a := by ring
    rw [he'] at hh
    linarith [div_pos hlam ha]
  calc
    _ ≤ Real.exp (ζ * x - lam / 4 * M / a) * (D * Real.exp θ / (w + 1)) :=
      mul_le_mul (Real.exp_le_exp.mpr he) htbound (kernelDiracPin_nonneg τ hft0 w M hx.le)
        (Real.exp_nonneg _)
    _ = _ := mul_comm _ _

/-- Arbitrary positive input weights control the genuine short Dirac pin when
its forced slope is small. The denominator is `w+1`, with no `1/x` loss. -/
theorem kernel_regLaw_dirac_pin_small_slope_of_density (D θ vlo vhi ζ : ℝ)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (hζ : 0 < ζ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        ∀ w x : ℝ, 0 < w → 0 < x → (w + 1) / x ≤ 1 / 2 →
        ∀ M : ℕ, 1 ≤ M →
          kernelDiracPin ν f w M x ≤
            (D * Real.exp θ / (w + 1)) *
              Real.exp (ζ * x - c * M / ((w + 1) / x)) := by
  obtain ⟨lam, hlam, hlζ, hlθ, _, hrate⟩ :=
    kernel_regLaw_arbitrary_small_tilt D θ vlo vhi ζ hθ hvlo hv hζ
  refine ⟨lam / 4, by positivity, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe w x hw hx halo M hM
  have hlabs : |lam| ≤ θ / 2 := by rwa [abs_of_pos hlam]
  have hU := hν.univClass hθ hvlo
  let := hU.isProbabilityMeasure_centeredTilt hlabs
  have hp : IsProbabilityMeasure ((ν : Measure ℝ).tilted (fun t => lam * t)) := by
    rw [← kernel_centeredTilt_eq_raw]
    infer_instance
  let τ : ProbabilityMeasure ℝ := ⟨(ν : Measure ℝ).tilted (fun t => lam * t), hp⟩
  have hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun t => lam * t) := rfl
  have hftD := hν.kernelTiltDensity_le hθ hvlo hfz hfe hlabs
  have hft0 (t : ℝ) : 0 ≤ kernelTiltDensity ν lam f t :=
    mul_nonneg (Real.exp_nonneg _) (hf0 t)
  let a := (w + 1) / x
  have ha : 0 < a := div_pos (by linarith) hx
  have htbound : kernelDiracPin τ (kernelTiltDensity ν lam f) w M x ≤ D * Real.exp θ / (w + 1) :=
    kernelDiracPin_le_of_pin_bound τ _ hw hx M (by
      simpa only [abs_of_pos ha] using krDens_le_div (J := Icc 0 w) (β := 1) (a := a) τ hft0 hftD M 0 w)
  rw [kernel_dirac_pin_tilt ν τ hf hf0 hfD
    ((hν.univClass hθ hvlo).kernel_integrable_exp_raw hlabs) hτ hftD hw hx hM]
  have he : -(M : ℝ) * kernelTiltRate ν a lam + lam * x - lam / a ≤
      ζ * x - lam / 4 * M / a := by
    have hh := mul_le_mul_of_nonneg_left (hrate ν hν a ha halo) (Nat.cast_nonneg (α := ℝ) M)
    have hh' := mul_le_mul_of_nonneg_right hlζ hx.le
    have he' : (M : ℝ) * (lam / (4 * a)) = lam / 4 * M / a := by ring
    rw [he'] at hh
    linarith [div_pos hlam ha]
  calc
    _ ≤ Real.exp (ζ * x - lam / 4 * M / a) * (D * Real.exp θ / (w + 1)) :=
      mul_le_mul (Real.exp_le_exp.mpr he) htbound (kernelDiracPin_nonneg τ hft0 w M hx.le)
        (Real.exp_nonneg _)
    _ = _ := mul_comm _ _

end
end PGM
