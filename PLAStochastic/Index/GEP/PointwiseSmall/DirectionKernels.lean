import PLAStochastic.Index.GEP.PointwiseSmall.LengthKernelBound
import PLAStochastic.Index.GEP.DirectTerm.SlopeCalibration
import PLAStochastic.Index.GEP.RawDisc.MixtureLaws

/-!
# WP4 leaves `PointwiseSmall`, `QuadResponse`: kernels against direction laws

Bookkeeping shared by the rows of (P) and by `QuadResponse`:

* an output test at the fixed base scale, `y ↦ φ_ψ(y/C)`, is bounded by
  `(M/η) e^{2ηy/C}` (`pw_testFn_div_le`), so after normalisation it is an admissible test of
  `RawDiscId` and of the coarse kernel bound;
* the insertion kernels of such tests are measurable, `O(ε⁴ e^{κx})`, hence integrable against
  every law on `(0,∞)` with the exponential moment `e^{κx}` (`pw_kernel_facts`); so is `J_C`,
  which is bounded (`pw_lawJC_integrable`);
* `∫ J_φ d(σ - ν) = ∫ I_φ d(σ - ν) - (κ_φ/C) ∫ J_C d(σ - ν)` (`pw_integral_outJ_sub`), and the
  analogous identity for `J_A` (`pw_integral_lawJA_sub`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

variable {D θ vlo vhi : ℝ}

theorem OutTest.nonneg' {η M : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) : 0 ≤ M := by
  have h := hψ.2 0 le_rfl
  rw [mul_zero, Real.exp_zero, mul_one] at h
  exact (abs_nonneg _).trans h

theorem OutTest.mono_eta {η η' M : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (h : η ≤ η') :
    OutTest η' M ψ :=
  ⟨hψ.1, fun x hx => (hψ.2 x hx).trans (by
    have := hψ.nonneg'
    gcongr)⟩

/-- An output test at the base scale `C` is `O(e^{2ηy/C})`. -/
theorem pw_testFn_div_le {η M : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) {C y : ℝ}
    (hC : 0 < C) (hy : 0 ≤ y) :
    |testFn ψ (y / C)| ≤ M / η * Real.exp (2 * η * y / C) := by
  have hu : 0 ≤ y / C := by positivity
  have hM := hψ.nonneg'
  have h1 := hψ.abs_testFn_le hη.le hu
  have h2 : y / C ≤ Real.exp (η * (y / C)) / η := le_exp_div hη
  calc |testFn ψ (y / C)| ≤ M * Real.exp (η * (y / C)) * (y / C) := h1
    _ ≤ M * Real.exp (η * (y / C)) * (Real.exp (η * (y / C)) / η) := by gcongr
    _ = M / η * Real.exp (2 * η * y / C) := by
        have e : Real.exp (2 * η * y / C) = Real.exp (η * (y / C)) * Real.exp (η * (y / C)) := by
          rw [← Real.exp_add]; ring_nf
        rw [e]
        ring

/-- `e^{κx}` is integrable under a direction law for `κ ≤ θσ`. -/
theorem SigmaLaw.integrable_exp {A θσ κ : ℝ} {σ : ProbabilityMeasure ℝ} (hσ : SigmaLaw A θσ σ)
    (hκ : κ ≤ θσ) : Integrable (fun x => Real.exp (κ * x)) (σ : Measure ℝ) := by
  have hae : ∀ᵐ x ∂(σ : Measure ℝ), 0 < x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hσ.pos] with x hx
    simpa using hx
  refine hσ.expInt.mono' (by fun_prop) (hae.mono fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hκ hx.le)

/-- `e^{κx}` is integrable under a regular law for `κ ≤ θ/2`. -/
theorem RegLaw.integrable_exp {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hvlo : 0 < vlo) {κ : ℝ} (hκ : κ ≤ θ / 2) :
    Integrable (fun x => Real.exp (κ * x)) (ν : Measure ℝ) := by
  have hae : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hν.pos' hθ hvlo)] with x hx
    simpa using hx
  refine (hν.expMom hθ).integrable.mono' (by fun_prop) (hae.mono fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hκ hx.le)

/-- **Kernel facts**: measurability, the coarse bound, and integrability against laws on
`(0,∞)` with the matching exponential moment. -/
theorem pw_kernel_facts (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ κ₁ K₁ e₁ : ℝ, 0 < κ₁ ∧ 0 ≤ K₁ ∧ 1 ≤ e₁ ∧ ∀ eps, e₁ ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ κ : ℝ, 0 ≤ κ → κ * eps ^ 2 ≤ κ₁ → ∀ F : ℝ → ℝ, Measurable F →
      (∀ y, 0 ≤ y → |F y| ≤ Real.exp (κ * y)) →
        Measurable (insKernel eps ν (fun g => F (stopSum eps g))) ∧
        (∀ x, 0 ≤ x → |insKernel eps ν (fun g => F (stopSum eps g)) x| ≤
          K₁ * eps ^ 4 * Real.exp (κ * x)) ∧
        ∀ ρ : ProbabilityMeasure ℝ, (ρ : Measure ℝ) (Iic 0) = 0 →
          Integrable (fun x => Real.exp (κ * x)) (ρ : Measure ℝ) →
          Integrable (insKernel eps ν (fun g => F (stopSum eps g))) (ρ : Measure ℝ) := by
  obtain ⟨κ₁, K₁, e₁, hκ₁, hK₁, he₁, hker⟩ := kernel_coarse hD hθ hvlo hv
  refine ⟨κ₁, K₁, e₁, hκ₁, hK₁, he₁, fun eps heps ν hν κ hκ0 hκ F hF hFb => ?_⟩
  obtain ⟨hm, hb, -⟩ := hker eps heps ν hν κ hκ0 hκ F hF hFb
  refine ⟨hm, hb, fun ρ hρ hρe => ?_⟩
  have hae : ∀ᵐ x ∂(ρ : Measure ℝ), 0 < x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hρ] with x hx
    simpa using hx
  refine (hρe.const_mul (K₁ * eps ^ 4)).mono' hm.aestronglyMeasurable (hae.mono fun x hx => ?_)
  rw [Real.norm_eq_abs]
  exact hb x hx.le

/-- `J_C` is integrable against every probability law (it is bounded and measurable). -/
theorem pw_lawJC_integrable (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ KJ e0 : ℝ, 0 ≤ KJ ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → Measurable (lawJC eps ν) ∧
        (∀ x, 0 ≤ lawJC eps ν x ∧ lawJC eps ν x ≤ KJ * eps ^ 4) ∧
        ∀ ρ : ProbabilityMeasure ℝ, Integrable (lawJC eps ν) (ρ : Measure ℝ) := by
  obtain ⟨KJ, e0, hKJ, he0, hJ⟩ := pw_lawJC_bound hD hθ hvlo hv
  refine ⟨KJ, e0, hKJ, he0, fun eps heps ν hν => ?_⟩
  obtain ⟨hm, hb⟩ := hJ eps heps ν hν
  refine ⟨hm, hb, fun ρ => Integrable.of_bound hm.aestronglyMeasurable (KJ * eps ^ 4)
    (Eventually.of_forall fun x => ?_)⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]
  exact (hb x).2

/-- **The influence of an output test against a signed direction.** -/
theorem pw_integral_outJ_sub {eps : ℝ} {ν σ : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ}
    (hIσ : Integrable (outIns eps ν ψ) (σ : Measure ℝ))
    (hIν : Integrable (outIns eps ν ψ) (ν : Measure ℝ))
    (hJσ : Integrable (lawJC eps ν) (σ : Measure ℝ))
    (hJν : Integrable (lawJC eps ν) (ν : Measure ℝ)) :
    (∫ x, outJ eps ν ψ x ∂(σ : Measure ℝ)) - ∫ x, outJ eps ν ψ x ∂(ν : Measure ℝ) =
      ((∫ x, outIns eps ν ψ x ∂(σ : Measure ℝ)) - ∫ x, outIns eps ν ψ x ∂(ν : Measure ℝ)) -
        outKappa eps ν ψ / lawC eps ν *
          ((∫ x, lawJC eps ν x ∂(σ : Measure ℝ)) - ∫ x, lawJC eps ν x ∂(ν : Measure ℝ)) := by
  have e : ∀ ρ : ProbabilityMeasure ℝ, Integrable (outIns eps ν ψ) (ρ : Measure ℝ) →
      Integrable (lawJC eps ν) (ρ : Measure ℝ) →
      ∫ x, outJ eps ν ψ x ∂(ρ : Measure ℝ) = ∫ x, outIns eps ν ψ x ∂(ρ : Measure ℝ) -
        outKappa eps ν ψ / lawC eps ν * ∫ x, lawJC eps ν x ∂(ρ : Measure ℝ) := by
    intro ρ hI hJ
    have h2 : (fun x => outKappa eps ν ψ * (lawJC eps ν x / lawC eps ν)) =
        fun x => outKappa eps ν ψ / lawC eps ν * lawJC eps ν x := by
      funext x; ring
    rw [show (fun x => outJ eps ν ψ x) = fun x => outIns eps ν ψ x -
        outKappa eps ν ψ * (lawJC eps ν x / lawC eps ν) from rfl,
      integral_sub hI (by rw [h2]; exact hJ.const_mul _), h2, integral_const_mul]
  rw [e σ hIσ hJσ, e ν hIν hJν]
  ring

/-- **The influence of `A = log v + log C` against a signed direction.** -/
theorem pw_integral_lawJA_sub {eps : ℝ} {ν σ : ProbabilityMeasure ℝ}
    (hJσ : Integrable (lawJC eps ν) (σ : Measure ℝ))
    (hJν : Integrable (lawJC eps ν) (ν : Measure ℝ))
    (hQσ : Integrable (fun x : ℝ => (x - 1) ^ 2) (σ : Measure ℝ))
    (hQν : Integrable (fun x : ℝ => (x - 1) ^ 2) (ν : Measure ℝ))
    (hmσ : lawMean σ = 1) (hmν : lawMean ν = 1) :
    (∫ x, lawJA eps ν x ∂(σ : Measure ℝ)) - ∫ x, lawJA eps ν x ∂(ν : Measure ℝ) =
      ((∫ x, lawJC eps ν x ∂(σ : Measure ℝ)) - ∫ x, lawJC eps ν x ∂(ν : Measure ℝ)) /
        lawC eps ν + (lawVar σ - lawVar ν) / lawVar ν := by
  have e : ∀ ρ : ProbabilityMeasure ℝ, Integrable (lawJC eps ν) (ρ : Measure ℝ) →
      Integrable (fun x : ℝ => (x - 1) ^ 2) (ρ : Measure ℝ) → lawMean ρ = 1 →
      ∫ x, lawJA eps ν x ∂(ρ : Measure ℝ) =
        (∫ x, lawJC eps ν x ∂(ρ : Measure ℝ)) / lawC eps ν + lawVar ρ / lawVar ν := by
    intro ρ hJ hQ hm
    rw [show (fun x => lawJA eps ν x) = fun x => lawJC eps ν x / lawC eps ν +
        (x - 1) ^ 2 / lawVar ν from rfl,
      integral_add (hJ.div_const _) (hQ.div_const _), integral_div, integral_div,
      lawVar_eq_of_mean hm]
  rw [e σ hJσ hQσ hmσ, e ν hJν hQν hmν]
  ring

end

end PGM
