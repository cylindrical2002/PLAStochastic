import PLAStochastic.Index.CEPS.Final.TaylorBox
import PLAStochastic.ForMathlib.Analysis.Complex.PolydiscTaylorParam
import PLAStochastic.ForMathlib.Analysis.Complex.ImaginaryAxisDeriv

/-!
# The analytic box-Taylor pipeline: hypotheses and objects

A kernel of the form `Φ p y = E(p, iy) - ∫ H(p, λ, iy) dλ`, read in the first `d` jet coordinates
`p i` (`i : Fin d`), is analytic in the complexified coordinates `q ∈ ball c₀ R` (sup norm, a
polydisc around the reference jets `c₀ = (p₀ i)ᵢ`) jointly with the frequency `z` in the strip
`|Re z| < δ`, with envelopes `K (1+|z|)ᵉ e^{-c√|z|}` and `g(λ) (1+|z|)ᵉ e^{-c√|z|}`, `g`
integrable (`CepsAnalyticPipeline`). This file defines

* the frequency-level function `cepsPipelinePsi q z = E q z - ∫ H q λ z dλ` and the kernel
  `cepsPipelinePhi p y = cepsPipelinePsi (p) (iy)`;
* the coefficient functions `cepsPipelineCoeffZ α z`: the canonical polydisc Taylor
  coefficients of `E(·, z)` minus the `λ`-integral of those of `H(·, λ, z)`, and
  `cepsPipelineCoeff α y = cepsPipelineCoeffZ α (iy)`;
* the envelope `cepsPipelineWeight c e z = (1+|z|)ᵉ e^{-c√|z|}` and its comparison with
  `cepsStretchedWeight` on discs around the imaginary axis.
-/

noncomputable section
open Complex Finset Metric MeasureTheory Filter
namespace PGM

/-- The first `d` jet coordinates as complex numbers. -/
def cepsPipelineEmb (d : ℕ) (p : ℕ → ℝ) : Fin d → ℂ := fun i => (p i : ℂ)

/-- The frequency envelope `(1+|z|)ᵉ e^{-c√|z|}`. -/
def cepsPipelineWeight (c : ℝ) (e : ℕ) (z : ℂ) : ℝ :=
  (1 + ‖z‖) ^ e * Real.exp (-c * Real.sqrt ‖z‖)

/-- **Hypotheses of the analytic pipeline.** Joint analyticity on polydisc × strip, product
envelopes with an integrable `λ`-factor, and measurability in `λ` inside the analytic region. -/
structure CepsAnalyticPipeline {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ) (d : ℕ)
    (p₀ : ℕ → ℝ) (R δ K c : ℝ) (e : ℕ) (g : Λ → ℝ)
    (E : (Fin d → ℂ) → ℂ → ℂ) (H : (Fin d → ℂ) → Λ → ℂ → ℂ) : Prop where
  R_pos : 0 < R
  δ_pos : 0 < δ
  K_pos : 0 < K
  c_pos : 0 < c
  g_integrable : Integrable g μ
  E_analytic : ∀ q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R, ∀ z : ℂ, |z.re| < δ →
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => E v.1 v.2) (q, z)
  E_bound : ∀ q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R, ∀ z : ℂ, |z.re| < δ →
    ‖E q z‖ ≤ K * (1 + ‖z‖) ^ e * Real.exp (-c * Real.sqrt ‖z‖)
  H_analytic : ∀ᵐ lam ∂μ, ∀ q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R, ∀ z : ℂ, |z.re| < δ →
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => H v.1 lam v.2) (q, z)
  H_bound : ∀ᵐ lam ∂μ, ∀ q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R, ∀ z : ℂ, |z.re| < δ →
    ‖H q lam z‖ ≤ g lam * ((1 + ‖z‖) ^ e * Real.exp (-c * Real.sqrt ‖z‖))
  H_measurable : ∀ q ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R, ∀ z : ℂ, |z.re| < δ →
    AEStronglyMeasurable (fun lam => H q lam z) μ

section Objects

variable {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ) {d : ℕ}
  (E : (Fin d → ℂ) → ℂ → ℂ) (H : (Fin d → ℂ) → Λ → ℂ → ℂ)

/-- The frequency-level kernel `E q z - ∫ H q λ z dλ`. -/
def cepsPipelinePsi (q : Fin d → ℂ) (z : ℂ) : ℂ := E q z - ∫ lam, H q lam z ∂μ

/-- The kernel on the imaginary axis, read in the jet coordinates. -/
def cepsPipelinePhi (p : ℕ → ℝ) (y : ℝ) : ℂ :=
  E (fun i : Fin d => (p i : ℂ)) (Complex.I * y) -
    ∫ lam, H (fun i : Fin d => (p i : ℂ)) lam (Complex.I * y) ∂μ

/-- Coefficient functions of the frequency variable. -/
def cepsPipelineCoeffZ (p₀ : ℕ → ℝ) (α : Fin d → ℕ) (z : ℂ) : ℂ :=
  polydiscTaylorCoeff (fun q => E q z) (fun i : Fin d => (p₀ i : ℂ)) α -
    ∫ lam, polydiscTaylorCoeff (fun q => H q lam z) (fun i : Fin d => (p₀ i : ℂ)) α ∂μ

/-- The box Taylor coefficients of the kernel on the imaginary axis. -/
def cepsPipelineCoeff (p₀ : ℕ → ℝ) (α : Fin d → ℕ) (y : ℝ) : ℂ :=
  cepsPipelineCoeffZ μ E H p₀ α (Complex.I * y)

theorem cepsPipelinePhi_eq (p : ℕ → ℝ) :
    cepsPipelinePhi μ E H p =
      fun y : ℝ => cepsPipelinePsi μ E H (cepsPipelineEmb d p) (Complex.I * y) := rfl

theorem cepsPipelineCoeff_eq (p₀ : ℕ → ℝ) (α : Fin d → ℕ) :
    cepsPipelineCoeff μ E H p₀ α =
      fun y : ℝ => cepsPipelineCoeffZ μ E H p₀ α (Complex.I * y) := rfl

end Objects

/-! ## The envelope -/

theorem cepsPipelineWeight_pos (c : ℝ) (e : ℕ) (z : ℂ) : 0 < cepsPipelineWeight c e z := by
  unfold cepsPipelineWeight
  have : (0 : ℝ) < 1 + ‖z‖ := by positivity
  positivity

theorem cepsPipelineWeight_zero (c : ℝ) (e : ℕ) : cepsPipelineWeight c e 0 = 1 := by
  simp [cepsPipelineWeight]

theorem continuous_cepsPipelineWeight (c : ℝ) (e : ℕ) :
    Continuous (cepsPipelineWeight c e) := by
  unfold cepsPipelineWeight
  exact (continuous_const.add continuous_norm).pow e |>.mul
    (Real.continuous_exp.comp (continuous_const.mul (Real.continuous_sqrt.comp continuous_norm)))

theorem sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sqrt_nonneg a
  have h4 := Real.sqrt_nonneg b
  have hle : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by nlinarith
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-- On a disc of radius `r` around `iy` the envelope is comparable to the stretched weight
of `y`. -/
theorem cepsPipelineWeight_le_of_mem_ball {c : ℝ} (hc : 0 ≤ c) (e : ℕ) {r : ℝ} (hr : 0 ≤ r)
    {y : ℝ} {z : ℂ} (hz : z ∈ ball (Complex.I * (y : ℂ)) r) :
    cepsPipelineWeight c e z ≤
      (1 + r) ^ e * Real.exp (c * Real.sqrt r) * cepsStretchedWeight c e y := by
  have hIy : ‖Complex.I * (y : ℂ)‖ = |y| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [mem_ball, dist_eq_norm] at hz
  have h1 : ‖z‖ ≤ |y| + r := by
    have := norm_le_norm_add_norm_sub' z (Complex.I * (y : ℂ))
    rw [hIy] at this
    linarith
  have h2 : |y| ≤ ‖z‖ + r := by
    have := norm_le_norm_add_norm_sub' (Complex.I * (y : ℂ)) z
    rw [hIy, norm_sub_rev] at this
    linarith
  have hpow : (1 + ‖z‖) ^ e ≤ (1 + r) ^ e * (1 + |y|) ^ e := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg y]) e
  have hsq : Real.sqrt |y| ≤ Real.sqrt ‖z‖ + Real.sqrt r :=
    (Real.sqrt_le_sqrt h2).trans (sqrt_add_le_sqrt_add_sqrt (norm_nonneg _) hr)
  have hexp : Real.exp (-c * Real.sqrt ‖z‖) ≤
      Real.exp (c * Real.sqrt r) * Real.exp (-c * Real.sqrt |y|) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hsq hc])
  unfold cepsPipelineWeight cepsStretchedWeight
  calc (1 + ‖z‖) ^ e * Real.exp (-c * Real.sqrt ‖z‖)
      ≤ ((1 + r) ^ e * (1 + |y|) ^ e) *
          (Real.exp (c * Real.sqrt r) * Real.exp (-c * Real.sqrt |y|)) :=
        mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
    _ = (1 + r) ^ e * Real.exp (c * Real.sqrt r) *
          ((1 + |y|) ^ e * Real.exp (-c * Real.sqrt |y|)) := by ring

/-! ## Real jet coordinates inside the polydisc -/

theorem cepsPipelineEmb_sub_norm_le {d : ℕ} {p₀ p : ℕ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hp : ∀ i : Fin d, |p i - p₀ i| ≤ ρ) :
    ‖cepsPipelineEmb d p - cepsPipelineEmb d p₀‖ ≤ ρ :=
  (pi_norm_le_iff_of_nonneg hρ).mpr fun i => by
    simp only [cepsPipelineEmb, Pi.sub_apply, ← ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact hp i

theorem cepsPipelineEmb_mem_ball {d : ℕ} {p₀ p : ℕ → ℝ} {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    (hp : ∀ i : Fin d, |p i - p₀ i| ≤ ρ) :
    cepsPipelineEmb d p ∈ ball (cepsPipelineEmb d p₀) R := by
  rw [mem_ball, dist_eq_norm]
  exact (cepsPipelineEmb_sub_norm_le hρ hp).trans_lt hρR

theorem cepsPipelineEmb_monomial {d : ℕ} (p₀ p : ℕ → ℝ) (α : Fin d → ℕ) :
    (∏ i, (cepsPipelineEmb d p - cepsPipelineEmb d p₀) i ^ α i) =
      (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ) := by
  simp [cepsPipelineEmb, cepsMonomial]

theorem cepsPipelineEmb_sum_norm {d : ℕ} (p₀ p : ℕ → ℝ) :
    (∑ i, ‖(cepsPipelineEmb d p - cepsPipelineEmb d p₀) i‖) = ∑ i : Fin d, |p i - p₀ i| := by
  refine sum_congr rfl fun i _ => ?_
  simp only [cepsPipelineEmb, Pi.sub_apply, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

end PGM
