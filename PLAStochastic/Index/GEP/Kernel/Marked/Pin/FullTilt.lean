import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FullDensity

/-! # Exact exponential conjugacy for every non-Dirac marked pin -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 800000

/-- All non-Dirac insertion positions have the same exact missing-step tilt
factor, including a deterministic first or final step. -/
theorem kernel_fullDens_tilt {J : Set ℝ} (hJ : MeasurableSet J)
    (ν τ : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D E : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    {lam : ℝ} (hM : Integrable (fun x : ℝ => Real.exp (lam * x)) (ν : Measure ℝ))
    (hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x))
    (hftD : ∀ x, kernelTiltDensity ν lam f x ≤ E)
    (β t : ℝ) {a : ℝ} (ha : a ≠ 0) (l r : ℕ) (y z : ℝ) :
    kernelMarkedFullDens J ν f β a t l r y z =
      Real.exp (-((l : ℝ) + r) * (lam * β / a - cgf id (ν : Measure ℝ) lam) +
        lam * (z - y) / a + lam * t - lam * β / a) *
        kernelMarkedFullDens J τ (kernelTiltDensity ν lam f) β a t l r y z := by
  cases l with
  | zero =>
    cases r with
    | zero => simp [kernelMarkedFullDens]
    | succ r =>
      simp only [kernelMarkedFullDens]
      rw [kernel_krDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD β ha (by omega : 1 ≤ r + 1)]
      have he : -((r + 1 : ℕ) : ℝ) * (lam * β / a - cgf id (ν : Measure ℝ) lam) +
          lam * (z - (y + β - a * t)) / a =
          -((0 : ℝ) + (r + 1 : ℕ)) * (lam * β / a - cgf id (ν : Measure ℝ) lam) +
          lam * (z - y) / a + lam * t - lam * β / a := by
        field_simp [ha]
        push_cast
        ring
      rw [he]
      ring
  | succ l =>
    cases r with
    | zero =>
      simp only [kernelMarkedFullDens]
      rw [kernel_krDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD β ha (by omega : 1 ≤ l + 1)]
      have he : -((l + 1 : ℕ) : ℝ) * (lam * β / a - cgf id (ν : Measure ℝ) lam) +
          lam * (z - β + a * t - y) / a =
          -(((l + 1 : ℕ) : ℝ) + 0) * (lam * β / a - cgf id (ν : Measure ℝ) lam) +
          lam * (z - y) / a + lam * t - lam * β / a := by
        field_simp [ha]
        push_cast
        ring
      rw [he]
      ring
    | succ r =>
      exact kernel_markedDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD β t ha
        (by omega) (by omega) y z

/-- The exchanged other pin cancels the endpoint factors for every insertion
position, with precisely `l+r+M` random cumulant normalizers. -/
theorem kernel_full_marked_pin_tilt {J : Set ℝ} (hJ : MeasurableSet J)
    (ν τ : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D E : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    {lam : ℝ} (hM : Integrable (fun x : ℝ => Real.exp (lam * x)) (ν : Measure ℝ))
    (hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x))
    (hftD : ∀ x, kernelTiltDensity ν lam f x ≤ E)
    (β t : ℝ) {a : ℝ} (ha : a ≠ 0) (l r : ℕ) {M : ℕ} (hN : 1 ≤ M) (y z : ℝ) :
    kernelMarkedFullDens J ν f β a t l r y z * krDens J ν f β a M z y =
      Real.exp (-((l : ℝ) + r + M) * (lam * β / a - cgf id (ν : Measure ℝ) lam) +
        lam * t - lam * β / a) *
        (kernelMarkedFullDens J τ (kernelTiltDensity ν lam f) β a t l r y z *
          krDens J τ (kernelTiltDensity ν lam f) β a M z y) := by
  rw [kernel_fullDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD β t ha l r y z,
    kernel_krDens_tilt hJ ν τ hf hf0 hfD hM hτ hftD β ha hN z y]
  rw [mul_mul_mul_comm, ← Real.exp_add]
  congr 2
  ring

/-- A single remaining genuine random step supplies the density scale. No
positive lower bound for either individual insertion side is needed. -/
theorem kernelFar_fullDens_le_div {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D β a t : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (ha : a ≠ 0) (l r : ℕ) (y z : ℝ) :
    kernelMarkedFullDens J ν f β a t l r y z ≤ D / |a| := by
  have hD : 0 ≤ D := (hf0 0).trans (hfD 0)
  exact kernelFar_fullDens_le_longer hJ hJfin ν hf hf0 hfD hν ha (by positivity)
    l r (fun u v => krDens_le_div ν hf0 hfD _ u v) y z

/-- A pointwise Chernoff majorant valid at every positive slope and every
non-Dirac marked length, with the original density representative chosen once.
Both genuine random pins retain their scale factors. -/
theorem kernel_regLaw_full_marked_pair_tilt (D θ vlo vhi : ℝ)
    (hθ : 0 < θ) (hvlo : 0 < vlo) :
    ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (∀ x ≤ 0, f x = 0) ∧ (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ lam : ℝ, |lam| ≤ θ / 2 →
        ∀ J : Set ℝ, MeasurableSet J → volume J ≠ ⊤ →
        ∀ a : ℝ, 0 < a → ∀ t y z : ℝ, ∀ l r M : ℕ, 1 ≤ M →
          kernelMarkedFullDens J ν f 1 a t l r y z * krDens J ν f 1 a M z y ≤
            (D * Real.exp θ / a) ^ 2 *
              Real.exp (-((l : ℝ) + r + M) * kernelTiltRate ν a lam + lam * t - lam / a) := by
  intro ν hν
  obtain ⟨f, hf, hf0, hfz, hfe, hνf⟩ := hν.density
  have hfD (x : ℝ) : f x ≤ D := by
    by_cases hx : x ≤ 0
    · rw [hfz x hx]
      exact hν.D_nonneg
    · exact (hfe x).trans (mul_le_of_le_one_right hν.D_nonneg
        (Real.exp_le_one_iff.mpr (by nlinarith)))
  refine ⟨f, hf, hf0, hfD, hfz, hfe, hνf, ?_⟩
  intro lam hlam J hJ hJfin a ha t y z l r M hM
  have hU := hν.univClass hθ hvlo
  let := hU.isProbabilityMeasure_centeredTilt hlam
  have hprob : IsProbabilityMeasure ((ν : Measure ℝ).tilted (fun x => lam * x)) := by
    rw [← kernel_centeredTilt_eq_raw]
    infer_instance
  let τ : ProbabilityMeasure ℝ := ⟨(ν : Measure ℝ).tilted (fun x => lam * x), hprob⟩
  have hτ : (τ : Measure ℝ) = (ν : Measure ℝ).tilted (fun x => lam * x) := rfl
  have hτf : (τ : Measure ℝ) = volume.withDensity
      (fun x => ENNReal.ofReal (kernelTiltDensity ν lam f x)) :=
    hτ.trans (kernel_tilt_density_measure ν hf hf0 hνf (hU.kernel_integrable_exp_raw hlam))
  have hftD := hν.kernelTiltDensity_le hθ hvlo hfz hfe hlam
  have hft : Measurable (kernelTiltDensity ν lam f) := by unfold kernelTiltDensity; fun_prop
  have hft0 (x : ℝ) : 0 ≤ kernelTiltDensity ν lam f x := by
    exact mul_nonneg (Real.exp_nonneg _) (hf0 x)
  have hh := kernel_full_marked_pin_tilt hJ ν τ hf hf0 hfD
    ((hν.univClass hθ hvlo).kernel_integrable_exp_raw hlam) hτ hftD 1 t ha.ne' l r hM y z
  simp only [mul_one] at hh
  rw [hh]
  have hb₁ := kernelFar_fullDens_le_div (β := 1) (t := t) hJ hJfin τ hft hft0 hftD hτf ha.ne' l r y z
  have hb₂ := krDens_le_div (J := J) (β := 1) (a := a) τ hft0 hftD M z y
  rw [abs_of_pos ha] at hb₁ hb₂
  have hp := mul_le_mul hb₁ hb₂ (krDens_nonneg τ hft0 _ _ _)
    (show 0 ≤ D * Real.exp θ / a from div_nonneg
      (mul_nonneg hν.D_nonneg (Real.exp_nonneg _)) ha.le)
  have hh' := mul_le_mul_of_nonneg_left hp
    (Real.exp_nonneg (-((l : ℝ) + r + M) * kernelTiltRate ν a lam + lam * t - lam / a))
  simpa only [kernelTiltRate, pow_two, mul_comm (Real.exp _) _] using hh'

end
end PGM
