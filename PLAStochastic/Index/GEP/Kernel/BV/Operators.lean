import PLAStochastic.Index.GEP.Kernel.BV.L2Multiplier
import PLAStochastic.Index.GEP.Kernel.BV.LowPass

/-!
# The real convolution, killed operator, and actual low/high frequency split

All operators are built from the characteristic function of the actual step law
and the unitary Fourier transform. The convolution identification links this
construction to `kConv`; no kernel-regularity conclusion is assumed.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory FourierTransform Set

/-- The exact Fourier multiplier of the free backward step. -/
def kBVStepMultiplier (ν : Measure ℝ) (β a ξ : ℝ) : ℂ :=
  Complex.exp (↑(2 * Real.pi * ξ * β) * Complex.I) *
    charFun ν (-(2 * Real.pi * a * ξ))

theorem kBVStepMultiplier_measurable (ν : Measure ℝ) [IsFiniteMeasure ν] (β a : ℝ) :
    Measurable (kBVStepMultiplier ν β a) := by
  unfold kBVStepMultiplier
  exact (by fun_prop : Measurable (fun ξ : ℝ =>
    Complex.exp (↑(2 * Real.pi * ξ * β) * Complex.I))).mul
      ((measurable_charFun (μ := ν)).comp (by fun_prop))

theorem kBVStepMultiplier_norm (ν : Measure ℝ) (β a ξ : ℝ) :
    ‖kBVStepMultiplier ν β a ξ‖ = ‖charFun ν (-(2 * Real.pi * a * ξ))‖ := by
  rw [kBVStepMultiplier, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem kBVStepMultiplier_bound (ν : Measure ℝ) [IsProbabilityMeasure ν] (β a ξ : ℝ) :
    ‖kBVStepMultiplier ν β a ξ‖ ≤ 1 := by
  rw [kBVStepMultiplier_norm]
  exact norm_charFun_le_one _

/-- The actual free step acting on `L²`. -/
def kBVConvolutionL2 (ν : Measure ℝ) [IsProbabilityMeasure ν] (β a : ℝ) :
    KernelL2 →L[ℂ] KernelL2 :=
  kBVFourierInvL2 * kBVMulL2 (kBVStepMultiplier ν β a)
    (kBVStepMultiplier_measurable ν β a) 1 (kBVStepMultiplier_bound ν β a) * kBVFourierL2

/-- The multiplier construction agrees with the original integral convolution. -/
theorem kBVConvolutionL2_toLp (ν : Measure ℝ) [IsProbabilityMeasure ν] (β a : ℝ)
    {u : ℝ → ℂ} (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2) :
    kBVConvolutionL2 ν β a (h2.toLp u) =
      ((memLp_two_kConv ν hu h1 h2 β a).1).toLp (kConv ν β a u) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change 𝓕 (𝓕⁻ (kBVMulL2 (kBVStepMultiplier ν β a)
    (kBVStepMultiplier_measurable ν β a) 1 (kBVStepMultiplier_bound ν β a)
      (𝓕 (h2.toLp u)))) =
    𝓕 (((memLp_two_kConv ν hu h1 h2 β a).1).toLp (kConv ν β a u))
  rw [fourier_fourierInv_eq]
  apply Lp.ext
  filter_upwards [kBVMulL2_coe (kBVStepMultiplier_measurable ν β a)
      (kBVStepMultiplier_bound ν β a) (𝓕 (h2.toLp u)),
    kill_fourier_toLp_two_ae_eq h1 h2,
    kill_fourier_toLp_two_ae_eq (integrable_kConv ν hu h1 β a)
      (memLp_two_kConv ν hu h1 h2 β a).1] with ξ hM hU hC
  rw [hM, hU, hC, fourier_kConv ν hu h1 β a ξ]
  rfl

theorem kBVConvolutionL2_bound (ν : Measure ℝ) [IsProbabilityMeasure ν] (β a : ℝ)
    (u : KernelL2) : ‖kBVConvolutionL2 ν β a u‖ ≤ ‖u‖ := by
  change ‖kBVFourierInvL2 (kBVMulL2 _ _ _ _ (kBVFourierL2 u))‖ ≤ _
  rw [kBVFourierInvL2_norm]
  simpa only [one_mul, kBVFourierL2_apply, Lp.norm_fourier_eq] using
    kBVMulL2_bound (kBVStepMultiplier_measurable ν β a) (kBVStepMultiplier_bound ν β a)
      (kBVFourierL2 u)

/-- The true killed operator `P C P` on `L²`. -/
def kBVKilledL2 (J : Set ℝ) (hJ : MeasurableSet J) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (β a : ℝ) : KernelL2 →L[ℂ] KernelL2 :=
  kBVProject J hJ * kBVConvolutionL2 ν β a * kBVProject J hJ

/-- The hard low-frequency projection, conjugated into physical space. -/
def kBVLowProjectL2 : KernelL2 →L[ℂ] KernelL2 :=
  kBVFourierInvL2 * kBVProject (Icc (-1 : ℝ) 1) measurableSet_Icc * kBVFourierL2

/-- Low-frequency regularizing step with both physical interval projections retained. -/
def kBVLowStepL2 (J : Set ℝ) (hJ : MeasurableSet J) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (β a : ℝ) : KernelL2 →L[ℂ] KernelL2 :=
  kBVProject J hJ * kBVLowProjectL2 * kBVConvolutionL2 ν β a * kBVProject J hJ

/-- The actual high-frequency remainder. -/
def kBVHighStepL2 (J : Set ℝ) (hJ : MeasurableSet J) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (β a : ℝ) : KernelL2 →L[ℂ] KernelL2 :=
  kBVKilledL2 J hJ ν β a - kBVLowStepL2 J hJ ν β a

/-- Exact decomposition of the actual killed operator. -/
theorem kBV_killed_eq_low_add_high (J : Set ℝ) (hJ : MeasurableSet J) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (β a : ℝ) :
    kBVKilledL2 J hJ ν β a = kBVLowStepL2 J hJ ν β a + kBVHighStepL2 J hJ ν β a := by
  unfold kBVHighStepL2
  abel

/-- The low-frequency `L²` projection has the same continuous representative as
`kBVLowPass` whenever the input is integrable. -/
theorem kBVLowProjectL2_toLp {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    kBVLowProjectL2 (h2.toLp u) =
      (kBVLowPass_memLp h1 h2).toLp (kBVLowPass u) := by
  have hproj : kBVProject (Icc (-1 : ℝ) 1) measurableSet_Icc (𝓕 (h2.toLp u)) =
      (kBVLowFreq_memLp h1 h2).toLp (kBVLowFreq u) := by
    apply Lp.ext
    filter_upwards [kBVProject_coe (Icc (-1 : ℝ) 1) measurableSet_Icc (𝓕 (h2.toLp u)),
      kill_fourier_toLp_two_ae_eq h1 h2, (kBVLowFreq_memLp h1 h2).coeFn_toLp] with ξ hp hF hl
    rw [hp, hl]
    by_cases hξ : ξ ∈ Icc (-1 : ℝ) 1 <;> simp [kBVLowFreq, hξ, hF]
  change 𝓕⁻ (kBVProject _ _ (𝓕 (h2.toLp u))) = _
  rw [hproj]
  apply Lp.ext
  exact (kBV_fourierInv_toLp_two_ae_eq (kBVLowFreq_integrable h1 h2)
    (kBVLowFreq_memLp h1 h2)).trans (kBVLowPass_memLp h1 h2).coeFn_toLp.symm

/-- A high-frequency multiplier gap gives strict contraction of the actual
high-frequency killed remainder, without discarding interval projections. -/
theorem kBVHighStepL2_bound {J : Set ℝ} (hJ : MeasurableSet J) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (β a : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hgap : ∀ ξ, ξ ∉ Icc (-1 : ℝ) 1 → ‖kBVStepMultiplier ν β a ξ‖ ≤ ρ)
    (u : KernelL2) : ‖kBVHighStepL2 J hJ ν β a u‖ ≤ ρ * ‖u‖ := by
  let P := kBVProject J hJ
  let F := kBVFourierL2
  let Fi := kBVFourierInvL2
  let L := kBVProject (Icc (-1 : ℝ) 1) measurableSet_Icc
  let A := kBVMulL2 (kBVStepMultiplier ν β a)
    (kBVStepMultiplier_measurable ν β a) 1 (kBVStepMultiplier_bound ν β a)
  let z : KernelL2 := F (P u)
  have heq : kBVHighStepL2 J hJ ν β a u = P (Fi (A z - L (A z))) := by
    change P (Fi (A z)) - P (Fi (L (𝓕 (𝓕⁻ (A z)))) ) = P (Fi (A z - L (A z)))
    rw [fourier_fourierInv_eq, map_sub, map_sub]
  have hnorm : ‖A z - L (A z)‖ ≤ ρ * ‖z‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (A z) (L (A z)),
      kBVProject_coe (Icc (-1 : ℝ) 1) measurableSet_Icc (A z),
      kBVMulL2_coe (kBVStepMultiplier_measurable ν β a)
        (kBVStepMultiplier_bound ν β a) z] with ξ hs hl ha
    rw [hs]
    simp only [Pi.sub_apply]
    change ‖(A z : ℝ → ℂ) ξ - (L (A z) : ℝ → ℂ) ξ‖ ≤ _
    rw [hl]
    by_cases hξ : ξ ∈ Icc (-1 : ℝ) 1
    · simp only [indicator_of_mem hξ, sub_self, norm_zero]
      positivity
    · rw [indicator_of_notMem hξ, sub_zero, ha, norm_mul]
      exact mul_le_mul_of_nonneg_right (hgap ξ hξ) (norm_nonneg _)
  rw [heq]
  calc ‖P (Fi (A z - L (A z)))‖ ≤ ‖Fi (A z - L (A z))‖ := kBVProject_bound J hJ _
    _ = ‖A z - L (A z)‖ := kBVFourierInvL2_norm _
    _ ≤ ρ * ‖z‖ := hnorm
    _ ≤ ρ * ‖u‖ := by
      apply mul_le_mul_of_nonneg_left _ hρ
      change ‖𝓕 (P u)‖ ≤ ‖u‖
      rw [Lp.norm_fourier_eq]
      exact kBVProject_bound J hJ u

/-- The high-frequency multiplier bound follows directly from the original
regular-law Fourier gap, for both signs of the slope. -/
theorem kBVStepMultiplier_high_bound {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {ξ : ℝ} (hξ : ξ ∉ Icc (-1 : ℝ) 1) :
    ‖kBVStepMultiplier (ν : Measure ℝ) β a ξ‖ ≤ Real.sqrt (1 - killCnu D vlo vhi) := by
  have hg := kBV_regLaw_mult_gap hD hθ hvlo hν ha ξ
  have ht : 1 ≤ ξ ^ 2 := by
    have hh : ¬ |ξ| ≤ 1 := by simpa only [abs_le, mem_Icc] using hξ
    have hh' := lt_of_not_ge hh
    nlinarith [sq_abs ξ]
  simp only [kMult, sub_zero, one_mul, zero_mul, add_zero, min_eq_right ht, mul_one] at hg
  rw [kBVStepMultiplier_norm]
  have hnonneg : 0 ≤ 1 - killCnu D vlo vhi := (sq_nonneg _).trans hg
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rwa [Real.sq_sqrt hnonneg]

/-- The actual high-frequency remainder is strictly contracting under `RegLaw`.
The constant is uniform over the input class and both residual-walk directions. -/
theorem kBVHighStepL2_regLaw_bound {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {J : Set ℝ} (hJ : MeasurableSet J) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|)
    (u : KernelL2) :
    ‖kBVHighStepL2 J hJ (ν : Measure ℝ) β a u‖ ≤ Real.sqrt (1 - killCnu D vlo vhi) * ‖u‖ :=
  kBVHighStepL2_bound hJ (ν : Measure ℝ) β a (Real.sqrt_nonneg _)
    (fun _ hξ => kBVStepMultiplier_high_bound hD hθ hvlo hν β ha hξ) u

theorem kBVHighStepL2_regLaw_factor_lt_one {D vlo vhi : ℝ} (hD : 0 < D)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) : Real.sqrt (1 - killCnu D vlo vhi) < 1 := by
  have hc := killCnu_pos hD hvlo hvhi
  exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by nlinarith)

end
end PGM
