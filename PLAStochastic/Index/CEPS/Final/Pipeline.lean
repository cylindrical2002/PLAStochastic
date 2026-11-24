import PLAStochastic.Index.CEPS.Final.PipelineBounds

/-!
# The analytic box-Taylor pipeline: CEPS-format conclusions

Under `CepsAnalyticPipeline` (joint analyticity of `E` and of the `λ`-integrand `H` on the
polydisc `ball c₀ R` × strip `|Re z| < δ`, envelopes `K (1+|z|)ᵉ e^{-c√|z|}` and
`g(λ) (1+|z|)ᵉ e^{-c√|z|}` with `g` integrable, measurability in `λ` on the analytic region),
the kernel `Φ p y = E(p, iy) - ∫ H(p, λ, iy) dλ` read in the first `d` jet coordinates satisfies:

* (C1) `jetRepresentation_of_eq`: smooth coefficient functions `T α` with stretched-exponential
  bounds of every derivative, and for every frequency derivative order `m` and box order `N` the
  box Taylor remainder `K (1+|y|)ᵉ e^{-c√|y|} (∑ᵢ |pᵢ - p₀ᵢ|)^{N+1}` (the `Gk` field of
  `CepsKernelJetRepresentation`);
* (C2) `phiRegular_of_eq`: on a fixed box around `p₀`, `Φ p` is smooth and all its derivatives
  are bounded by stretched-exponential weights uniformly in `p`;
* (C3) `zeroFrequency_of_eq`, `scalar_re_of_eq`: the scalar box Taylor representations at
  `y = 0` (the `Cs` field shape, also for real parts of frequency derivatives at `0`).

The `_of_eq` forms apply to any `Φ` that agrees with the pipeline kernel on some box around `p₀`.
Frequency derivatives come from the Cauchy estimate on discs of radius `δ` around `iy` applied to
the holomorphic remainder `z ↦ Ψ(p, z) - ∑ T̃ α(z) (p - p₀)^α`; no commutation of derivatives is
used.
-/

noncomputable section
open Complex Finset Metric MeasureTheory Filter
open scoped ContDiff
namespace PGM

/-- Linearity of real iterated derivatives for a finite combination with constant
coefficients. -/
theorem iteratedDeriv_sub_sum_mul_const {ι : Type*} (s : Finset ι) {f : ℝ → ℂ}
    {g : ι → ℝ → ℂ} (a : ι → ℂ) {m : ℕ} (hf : ContDiff ℝ m f)
    (hg : ∀ i ∈ s, ContDiff ℝ m (g i)) (y : ℝ) :
    iteratedDeriv m (fun y => f y - ∑ i ∈ s, g i y * a i) y =
      iteratedDeriv m f y - ∑ i ∈ s, iteratedDeriv m (g i) y * a i := by
  have hg' : ∀ i ∈ s, ContDiff ℝ m (fun y => g i y * a i) := fun i hi =>
    (hg i hi).mul contDiff_const
  have hsum : ContDiff ℝ m (fun y => ∑ i ∈ s, g i y * a i) := ContDiff.sum hg'
  have h1 : (fun y => f y - ∑ i ∈ s, g i y * a i) = f - fun y => ∑ i ∈ s, g i y * a i := rfl
  rw [h1, iteratedDeriv_sub hf.contDiffAt hsum.contDiffAt,
    iteratedDeriv_fun_sum fun i hi => (hg' i hi).contDiffAt]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have h2 : (fun y => g i y * a i) = fun y => a i * g i y := by
    funext y
    ring
  rw [h2, iteratedDeriv_const_mul _ (hg i hi).contDiffAt, mul_comm]

namespace CepsAnalyticPipeline

variable {Λ : Type*} [MeasurableSpace Λ] {μ : Measure Λ} {d : ℕ} {p₀ : ℕ → ℝ}
  {R δ K c : ℝ} {e : ℕ} {g : Λ → ℝ}
  {E : (Fin d → ℂ) → ℂ → ℂ} {H : (Fin d → ℂ) → Λ → ℂ → ℂ}

section

variable (hP : CepsAnalyticPipeline μ d p₀ R δ K c e g E H)
include hP

theorem KG_nonneg : 0 ≤ K + ∫ lam, g lam ∂μ := add_nonneg hP.K_pos.le hP.integral_g_nonneg

/-- The constant `(1+δ)ᵉ e^{c√δ}` comparing envelopes on discs of radius `δ`. -/
theorem disc_factor_pos : 0 < (1 + δ) ^ e * Real.exp (c * Real.sqrt δ) := by
  have := hP.δ_pos
  positivity

/-! ## Smoothness and derivative bounds -/

theorem phi_contDiff {p : ℕ → ℝ}
    (hp : cepsPipelineEmb d p ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R) :
    ContDiff ℝ ∞ (cepsPipelinePhi μ E H p) := by
  rw [cepsPipelinePhi_eq]
  exact contDiff_comp_I_mul (isOpen_imagStrip δ) (hP.psi_differentiableOn hp)
    (I_mul_ofReal_mem_imagStrip hP.δ_pos)

theorem coeff_contDiff (α : Fin d → ℕ) : ContDiff ℝ ∞ (cepsPipelineCoeff μ E H p₀ α) := by
  rw [cepsPipelineCoeff_eq]
  exact contDiff_comp_I_mul (isOpen_imagStrip δ) (hP.coeffZ_differentiableOn α)
    (I_mul_ofReal_mem_imagStrip hP.δ_pos)

theorem norm_iteratedDeriv_phi_le {p : ℕ → ℝ}
    (hp : cepsPipelineEmb d p ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R) (m : ℕ) (y : ℝ) :
    ‖iteratedDeriv m (cepsPipelinePhi μ E H p) y‖ ≤
      (m.factorial * ((K + ∫ lam, g lam ∂μ) * ((1 + δ) ^ e * Real.exp (c * Real.sqrt δ))) /
        (δ / 2) ^ m) * cepsStretchedWeight c e y := by
  rw [cepsPipelinePhi_eq]
  refine (norm_iteratedDeriv_comp_I_mul_le hP.δ_pos (hP.psi_differentiableOn hp) y
    (M := (K + ∫ lam, g lam ∂μ) * ((1 + δ) ^ e * Real.exp (c * Real.sqrt δ) *
      cepsStretchedWeight c e y)) (fun z hz => ?_) m).trans (le_of_eq (by ring))
  exact (hP.psi_bound hp (ball_I_mul_subset_imagStrip δ y hz)).trans
    (mul_le_mul_of_nonneg_left
      (cepsPipelineWeight_le_of_mem_ball hP.c_pos.le e hP.δ_pos.le hz) hP.KG_nonneg)

theorem norm_iteratedDeriv_coeff_le (α : Fin d → ℕ) (m : ℕ) (y : ℝ) :
    ‖iteratedDeriv m (cepsPipelineCoeff μ E H p₀ α) y‖ ≤
      (m.factorial * ((K + ∫ lam, g lam ∂μ) * (2 / R) ^ (∑ i, α i) *
        ((1 + δ) ^ e * Real.exp (c * Real.sqrt δ))) / (δ / 2) ^ m) *
        cepsStretchedWeight c e y := by
  rw [cepsPipelineCoeff_eq]
  refine (norm_iteratedDeriv_comp_I_mul_le hP.δ_pos (hP.coeffZ_differentiableOn α) y
    (M := (K + ∫ lam, g lam ∂μ) * (2 / R) ^ (∑ i, α i) *
      ((1 + δ) ^ e * Real.exp (c * Real.sqrt δ) * cepsStretchedWeight c e y))
    (fun z hz => ?_) m).trans (le_of_eq (by ring))
  exact (hP.coeffZ_bound α (ball_I_mul_subset_imagStrip δ y hz)).trans
    (mul_le_mul_of_nonneg_left
      (cepsPipelineWeight_le_of_mem_ball hP.c_pos.le e hP.δ_pos.le hz)
      (mul_nonneg hP.KG_nonneg (pow_nonneg (div_nonneg zero_le_two hP.R_pos.le) _)))

/-! ## The box Taylor remainder of every frequency derivative -/

/-- The remainder bound for the pipeline kernel itself, on the box of radius `R/4`. -/
theorem remainder_le (m N : ℕ) (y : ℝ) {p : ℕ → ℝ} (hp : ∀ i : Fin d, |p i - p₀ i| ≤ R / 4) :
    ‖iteratedDeriv m (cepsPipelinePhi μ E H p) y - ∑ α ∈ cepsTaylorBox d N,
        iteratedDeriv m (cepsPipelineCoeff μ E H p₀ α) y *
          (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)‖ ≤
      (m.factorial * polydiscRemainderConst d N * (K + ∫ lam, g lam ∂μ) *
          ((1 + δ) ^ e * Real.exp (c * Real.sqrt δ)) / (δ / 2) ^ m / R ^ (N + 1)) *
        cepsStretchedWeight c e y * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1) := by
  have hR4 : 0 ≤ R / 4 := by linarith [hP.R_pos]
  have hpmem : cepsPipelineEmb d p ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R :=
    cepsPipelineEmb_mem_ball hR4 (by linarith [hP.R_pos]) hp
  set x : Fin d → ℂ := cepsPipelineEmb d p - cepsPipelineEmb d p₀ with hxdef
  have hx : ‖x‖ ≤ R / 4 := cepsPipelineEmb_sub_norm_le hR4 hp
  have hcx : (fun i : Fin d => (p₀ i : ℂ)) + x = cepsPipelineEmb d p := add_sub_cancel _ _
  set sz := ∑ i : Fin d, |p i - p₀ i|
  set mono : (Fin d → ℕ) → ℂ := fun α => (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)
  set Rem : ℂ → ℂ := fun z => cepsPipelinePsi μ E H (cepsPipelineEmb d p) z -
    ∑ α ∈ cepsTaylorBox d N, cepsPipelineCoeffZ μ E H p₀ α z * mono α
  have hRem_diff : DifferentiableOn ℂ Rem (imagStrip δ) :=
    (hP.psi_differentiableOn hpmem).sub
      (DifferentiableOn.fun_sum fun α _ => (hP.coeffZ_differentiableOn α).mul_const _)
  have hRem_bound : ∀ z ∈ imagStrip δ, ‖Rem z‖ ≤ polydiscRemainderConst d N *
      (K + ∫ lam, g lam ∂μ) * cepsPipelineWeight c e z * (sz / R) ^ (N + 1) := by
    intro z hz
    have h := hP.psi_box hz N hx
    rw [hcx, cepsPipelineEmb_sum_norm] at h
    simp_rw [hxdef, cepsPipelineEmb_monomial] at h
    exact h
  have hid : iteratedDeriv m (cepsPipelinePhi μ E H p) y - ∑ α ∈ cepsTaylorBox d N,
      iteratedDeriv m (cepsPipelineCoeff μ E H p₀ α) y * mono α =
        iteratedDeriv m (fun y : ℝ => Rem (Complex.I * (y : ℂ))) y := by
    rw [← iteratedDeriv_sub_sum_mul_const (cepsTaylorBox d N) mono
      (contDiff_infty.mp (hP.phi_contDiff hpmem) m)
      (fun α _ => contDiff_infty.mp (hP.coeff_contDiff α) m) y]
    rfl
  rw [hid]
  set A := (1 + δ) ^ e * Real.exp (c * Real.sqrt δ)
  have hbd := norm_iteratedDeriv_comp_I_mul_le hP.δ_pos hRem_diff y
    (M := polydiscRemainderConst d N * (K + ∫ lam, g lam ∂μ) *
      (A * cepsStretchedWeight c e y) * (sz / R) ^ (N + 1)) (fun z hz => ?_) m
  · refine hbd.trans (le_of_eq ?_)
    rw [div_pow]
    field_simp
  · refine (hRem_bound z (ball_I_mul_subset_imagStrip δ y hz)).trans ?_
    have hs : 0 ≤ (sz / R) ^ (N + 1) :=
      pow_nonneg (div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) hP.R_pos.le) _
    have hc : 0 ≤ polydiscRemainderConst d N * (K + ∫ lam, g lam ∂μ) :=
      mul_nonneg (polydiscRemainderConst_nonneg d N) hP.KG_nonneg
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (cepsPipelineWeight_le_of_mem_ball hP.c_pos.le e hP.δ_pos.le hz) hc) hs

/-! ## CEPS-format conclusions -/

/-- **(C1)** Box Taylor representation of every frequency derivative, with smooth
stretched-exponentially decaying coefficient functions, for any `Φ` agreeing with the pipeline
kernel near `p₀`. The coefficients are `cepsPipelineCoeff μ E H p₀`. -/
theorem jetRepresentation_of_eq {Φ : (ℕ → ℝ) → ℝ → ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hΦ : ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ₀) → ∀ y : ℝ,
      Φ p y = E (fun i : Fin d => (p i : ℂ)) (Complex.I * y) -
        ∫ lam, H (fun i : Fin d => (p i : ℂ)) lam (Complex.I * y) ∂μ) :
    ∃ T : (Fin d → ℕ) → ℝ → ℂ,
      (∀ (α : Fin d → ℕ) (n : ℕ), ContDiff ℝ n (T α)) ∧
      (∀ (α : Fin d → ℕ) (m : ℕ), ∃ K c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ y : ℝ,
        ‖iteratedDeriv m (T α) y‖ ≤ K * cepsStretchedWeight c e y) ∧
      ∀ m N : ℕ, ∃ ρ K c : ℝ, 0 < ρ ∧ 0 < c ∧ ∃ e : ℕ, ∀ (y : ℝ) (p : ℕ → ℝ),
        (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
          ‖iteratedDeriv m (Φ p) y - ∑ α ∈ cepsTaylorBox d N, iteratedDeriv m (T α) y *
              (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)‖ ≤
            K * cepsStretchedWeight c e y * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1) := by
  refine ⟨cepsPipelineCoeff μ E H p₀, fun α n => contDiff_infty.mp (hP.coeff_contDiff α) n,
    fun α m => ⟨_, c, hP.c_pos, e, hP.norm_iteratedDeriv_coeff_le α m⟩, fun m N => ?_⟩
  refine ⟨min ρ₀ (R / 4), m.factorial * polydiscRemainderConst d N * (K + ∫ lam, g lam ∂μ) *
      ((1 + δ) ^ e * Real.exp (c * Real.sqrt δ)) / (δ / 2) ^ m / R ^ (N + 1), c,
    lt_min hρ₀ (by linarith [hP.R_pos]), hP.c_pos, e, fun y p hp => ?_⟩
  have hΦp : Φ p = cepsPipelinePhi μ E H p :=
    funext (hΦ p fun i => (hp i).trans (min_le_left _ _))
  rw [hΦp]
  exact hP.remainder_le m N y fun i => (hp i).trans (min_le_right _ _)

/-- **(C2)** On a fixed box around `p₀`, `Φ p` is smooth and every derivative has a
stretched-exponential bound uniform in `p`. -/
theorem phiRegular_of_eq {Φ : (ℕ → ℝ) → ℝ → ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hΦ : ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ₀) → ∀ y : ℝ,
      Φ p y = E (fun i : Fin d => (p i : ℂ)) (Complex.I * y) -
        ∫ lam, H (fun i : Fin d => (p i : ℂ)) lam (Complex.I * y) ∂μ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ) → ∀ n : ℕ, ContDiff ℝ n (Φ p)) ∧
      ∀ m : ℕ, ∃ K c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
        ∀ y : ℝ, ‖iteratedDeriv m (Φ p) y‖ ≤ K * cepsStretchedWeight c e y := by
  have hR4 : 0 < R / 4 := by linarith [hP.R_pos]
  have hmem : ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ min ρ₀ (R / 4)) →
      Φ p = cepsPipelinePhi μ E H p ∧
        cepsPipelineEmb d p ∈ ball (fun i : Fin d => (p₀ i : ℂ)) R := fun p hp =>
    ⟨funext (hΦ p fun i => (hp i).trans (min_le_left _ _)),
      cepsPipelineEmb_mem_ball hR4.le (by linarith [hP.R_pos])
        fun i => (hp i).trans (min_le_right _ _)⟩
  refine ⟨min ρ₀ (R / 4), lt_min hρ₀ hR4, fun p hp n => ?_, fun m => ?_⟩
  · obtain ⟨h1, h2⟩ := hmem p hp
    rw [h1]
    exact contDiff_infty.mp (hP.phi_contDiff h2) n
  · refine ⟨m.factorial * ((K + ∫ lam, g lam ∂μ) *
        ((1 + δ) ^ e * Real.exp (c * Real.sqrt δ))) / (δ / 2) ^ m, c, hP.c_pos, e,
      fun p hp y => ?_⟩
    obtain ⟨h1, h2⟩ := hmem p hp
    rw [h1]
    exact hP.norm_iteratedDeriv_phi_le h2 m y

/-- **(C3)** The zero-frequency scalar representation with the coefficients `T α 0` of (C1). -/
theorem zeroFrequency_of_eq {Φ : (ℕ → ℝ) → ℝ → ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hΦ : ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ₀) → ∀ y : ℝ,
      Φ p y = E (fun i : Fin d => (p i : ℂ)) (Complex.I * y) -
        ∫ lam, H (fun i : Fin d => (p i : ℂ)) lam (Complex.I * y) ∂μ) (N : ℕ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
      ‖Φ p 0 - ∑ α ∈ cepsTaylorBox d N, cepsPipelineCoeff μ E H p₀ α 0 *
          (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)‖ ≤
        K * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1) := by
  have hR4 : 0 < R / 4 := by linarith [hP.R_pos]
  refine ⟨min ρ₀ (R / 4), Nat.factorial 0 * polydiscRemainderConst d N *
      (K + ∫ lam, g lam ∂μ) * ((1 + δ) ^ e * Real.exp (c * Real.sqrt δ)) / (δ / 2) ^ 0 /
        R ^ (N + 1), lt_min hρ₀ hR4, fun p hp => ?_⟩
  have hΦp : Φ p = cepsPipelinePhi μ E H p :=
    funext (hΦ p fun i => (hp i).trans (min_le_left _ _))
  have h := hP.remainder_le 0 N 0 fun i => (hp i).trans (min_le_right _ _)
  simp only [iteratedDeriv_zero, cepsStretchedWeight_at_zero, mul_one] at h
  rw [hΦp]
  exact h

/-- **(C3, real parts)** For a real scalar `S p = Re (a ∂_yᵐ Φ(p, 0))` near `p₀` there are real
coefficients with box remainders `K (∑ᵢ |pᵢ - p₀ᵢ|)^{N+1}` for every `N` (the `Cs` field shape;
`m = 0, a = 1` is the value at zero frequency). -/
theorem scalar_re_of_eq {Φ : (ℕ → ℝ) → ℝ → ℂ} {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hΦ : ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ₀) → ∀ y : ℝ,
      Φ p y = E (fun i : Fin d => (p i : ℂ)) (Complex.I * y) -
        ∫ lam, H (fun i : Fin d => (p i : ℂ)) lam (Complex.I * y) ∂μ)
    (m : ℕ) (a : ℂ) {S : (ℕ → ℝ) → ℝ}
    (hS : ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ₀) →
      S p = (a * iteratedDeriv m (Φ p) 0).re) :
    ∃ T : (Fin d → ℕ) → ℝ, ∀ N : ℕ, ∃ ρ K : ℝ, 0 < ρ ∧
      ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
        |S p - ∑ α ∈ cepsTaylorBox d N, T α * cepsMonomial (fun i : Fin d => p i - p₀ i) α| ≤
          K * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1) := by
  have hR4 : 0 < R / 4 := by linarith [hP.R_pos]
  refine ⟨fun α => (a * iteratedDeriv m (cepsPipelineCoeff μ E H p₀ α) 0).re, fun N => ?_⟩
  refine ⟨min ρ₀ (R / 4), ‖a‖ * (m.factorial * polydiscRemainderConst d N *
      (K + ∫ lam, g lam ∂μ) * ((1 + δ) ^ e * Real.exp (c * Real.sqrt δ)) / (δ / 2) ^ m /
        R ^ (N + 1)), lt_min hρ₀ hR4, fun p hp => ?_⟩
  have hp₀ : ∀ i : Fin d, |p i - p₀ i| ≤ ρ₀ := fun i => (hp i).trans (min_le_left _ _)
  have hΦp : Φ p = cepsPipelinePhi μ E H p := funext (hΦ p hp₀)
  have h := hP.remainder_le m N 0 fun i => (hp i).trans (min_le_right _ _)
  rw [cepsStretchedWeight_at_zero, mul_one] at h
  rw [hS p hp₀, hΦp]
  have hre : (a * iteratedDeriv m (cepsPipelinePhi μ E H p) 0).re -
      ∑ α ∈ cepsTaylorBox d N, (a * iteratedDeriv m (cepsPipelineCoeff μ E H p₀ α) 0).re *
        cepsMonomial (fun i : Fin d => p i - p₀ i) α =
      (a * (iteratedDeriv m (cepsPipelinePhi μ E H p) 0 - ∑ α ∈ cepsTaylorBox d N,
        iteratedDeriv m (cepsPipelineCoeff μ E H p₀ α) 0 *
          (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ))).re := by
    simp only [mul_sub, Finset.mul_sum, sub_re, re_sum]
    congr 1
    refine sum_congr rfl fun α _ => ?_
    rw [← mul_assoc, re_mul_ofReal]
  rw [hre]
  refine (abs_re_le_norm _).trans ?_
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg a)

end

/-! ## The pipeline kernel itself -/

/-- (C1) for the pipeline kernel `cepsPipelinePhi`. -/
theorem jetRepresentation (hP : CepsAnalyticPipeline μ d p₀ R δ K c e g E H) :
    ∃ T : (Fin d → ℕ) → ℝ → ℂ,
      (∀ (α : Fin d → ℕ) (n : ℕ), ContDiff ℝ n (T α)) ∧
      (∀ (α : Fin d → ℕ) (m : ℕ), ∃ K c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ y : ℝ,
        ‖iteratedDeriv m (T α) y‖ ≤ K * cepsStretchedWeight c e y) ∧
      ∀ m N : ℕ, ∃ ρ K c : ℝ, 0 < ρ ∧ 0 < c ∧ ∃ e : ℕ, ∀ (y : ℝ) (p : ℕ → ℝ),
        (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
          ‖iteratedDeriv m (cepsPipelinePhi μ E H p) y - ∑ α ∈ cepsTaylorBox d N,
              iteratedDeriv m (T α) y *
                (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)‖ ≤
            K * cepsStretchedWeight c e y * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1) :=
  hP.jetRepresentation_of_eq one_pos fun _ _ _ => rfl

end CepsAnalyticPipeline
end PGM
