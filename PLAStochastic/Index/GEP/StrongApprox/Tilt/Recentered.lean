import PLAStochastic.Index.GEP.StrongApprox.Tilt.Cumulants
import PLAStochastic.Index.GEP.StrongApprox.Tilt.StandardizedCramer
import PLAStochastic.Index.GEP.StrongApprox.LocalCLT.DensityLocalCLT

/-! # Recentered tilted laws and uniform density local CLT inputs -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-- The tilted centered gap, recentered at its actual tilted mean. -/
def saRecenteredTilt (ν : ProbabilityMeasure ℝ) (lam : ℝ) : Measure ℝ :=
  (centeredTilt ν lam).map (fun x => x - 1 -
    deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam)

/-- A class-uniform absolute third moment after recentering the tilt. -/
def saTiltThirdMoment (B θ : ℝ) : ℝ :=
  4 * (saMoment B θ 3 + saMoment B θ 1 ^ 3)

theorem saTiltThirdMoment_pos (B : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    0 < saTiltThirdMoment B θ := by
  unfold saTiltThirdMoment
  have := saMoment_pos B hθ 3
  have := saMoment_pos B hθ 1
  positivity

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

/-- Every absolute centered moment remains uniformly bounded under a half-range tilt. -/
theorem UnivClass.centeredTilt_abs_moment (h : UnivClass vlo vhi κ₃ B θ ν)
    (hθ : 0 < θ) {lam : ℝ} (hlam : |lam| ≤ θ / 2) (k : ℕ) :
    Integrable (fun x : ℝ => |x - 1| ^ k) (centeredTilt ν lam) ∧
      (∫ x : ℝ, |x - 1| ^ k ∂centeredTilt ν lam) ≤ saMoment B θ k := by
  have hl : |lam| ≤ θ := hlam.trans (by linarith)
  have hw := h.centered_weighted_moment hθ hlam k
  have hM := h.one_le_integral_exp_centered hl
  constructor
  · apply (integrable_tilted_iff (h.integrable_exp_centered hl) _).mpr
    simpa only [smul_eq_mul, mul_comm] using hw.1
  · rw [centeredTilt, integral_tilted]
    simp_rw [smul_eq_mul, div_mul_eq_mul_div, mul_comm (Real.exp _) (|_ - 1| ^ k)]
    rw [integral_div]
    exact (div_le_self (integral_nonneg fun x => by positivity) hM).trans hw.2

/-- The recentered tilt is a probability measure in the admissible range. -/
theorem UnivClass.isProbabilityMeasure_saRecenteredTilt (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| ≤ θ) : IsProbabilityMeasure (saRecenteredTilt ν lam) := by
  let := h.isProbabilityMeasure_centeredTilt hlam
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The recentered tilted law has a finite third moment. -/
theorem UnivClass.memLp_saRecenteredTilt (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) : MemLp id 3 (saRecenteredTilt ν lam) := by
  let := h.isProbabilityMeasure_centeredTilt hlam.le
  rw [saRecenteredTilt, memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)]
  exact (memLp_tilted_mul (h.centered_mem_interior hlam) (3 : ℝ≥0)).sub (memLp_const _)

/-- Recentring subtracts exactly the tilted mean. -/
theorem UnivClass.integral_saRecenteredTilt (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) :
    (∫ x : ℝ, x ∂saRecenteredTilt ν lam) = 0 := by
  let := h.isProbabilityMeasure_centeredTilt hlam.le
  have hi : Integrable (fun x : ℝ => x - 1) (centeredTilt ν lam) :=
    (memLp_tilted_mul (h.centered_mem_interior hlam) (1 : ℝ≥0)).integrable (by norm_num)
  rw [saRecenteredTilt, integral_map (by fun_prop) (by fun_prop),
    integral_sub hi (integrable_const _), h.integral_centered_centeredTilt hlam]
  simp

/-- The raw second moment after recentering is the second cumulant derivative. -/
theorem UnivClass.second_saRecenteredTilt (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| < θ) :
    (∫ x : ℝ, x ^ 2 ∂saRecenteredTilt ν lam) =
      iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam := by
  rw [saRecenteredTilt, integral_map (by fun_prop) (by fun_prop)]
  rw [← h.variance_centeredTilt hlam, variance_eq_integral (by fun_prop),
    h.integral_centered_centeredTilt hlam]

/-- An actual uniform third moment, not an assumed tilted-moment package. -/
theorem UnivClass.third_saRecenteredTilt (h : UnivClass vlo vhi κ₃ B θ ν)
    (hθ : 0 < θ) {lam : ℝ} (hlam : |lam| ≤ θ / 2) :
    (∫ x : ℝ, |x| ^ 3 ∂saRecenteredTilt ν lam) ≤ saTiltThirdMoment B θ := by
  have hl : |lam| < θ := hlam.trans_lt (by linarith)
  let := h.isProbabilityMeasure_centeredTilt hl.le
  let m := deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam
  have hm : |m| ≤ saMoment B θ 1 := by
    dsimp [m]
    rw [← h.integral_centered_centeredTilt hl]
    exact abs_integral_le_integral_abs.trans (by simpa using (h.centeredTilt_abs_moment hθ hlam 1).2)
  have hi : Integrable (fun x : ℝ => |x - 1 - m| ^ 3) (centeredTilt ν lam) := by
    have hm3 := (memLp_tilted_mul (h.centered_mem_interior hl) (3 : ℝ≥0)).sub (memLp_const m)
    simpa only [Real.norm_eq_abs, Pi.sub_apply, centeredTilt] using
      hm3.integrable_norm_pow (by norm_num)
  rw [saRecenteredTilt, integral_map (by fun_prop) (by fun_prop)]
  change (∫ x : ℝ, |x - 1 - m| ^ 3 ∂centeredTilt ν lam) ≤ _
  calc
    _ ≤ ∫ x : ℝ, 4 * (|x - 1| ^ 3 + |m| ^ 3) ∂centeredTilt ν lam := by
      apply integral_mono hi (((h.centeredTilt_abs_moment hθ hlam 3).1.add (integrable_const _)).const_mul 4)
      intro x
      change |x - 1 - m| ^ 3 ≤ 4 * (|x - 1| ^ 3 + |m| ^ 3)
      apply (pow_le_pow_left₀ (abs_nonneg _) (abs_sub (x - 1) m) 3).trans
      convert add_pow_le (abs_nonneg (x - 1)) (abs_nonneg m) 3 using 1
      norm_num
    _ = 4 * ((∫ x : ℝ, |x - 1| ^ 3 ∂centeredTilt ν lam) + |m| ^ 3) := by
      rw [integral_const_mul, integral_add (h.centeredTilt_abs_moment hθ hlam 3).1 (integrable_const _)]
      simp
    _ ≤ saTiltThirdMoment B θ := by
      unfold saTiltThirdMoment
      have hm3 := pow_le_pow_left₀ (abs_nonneg m) hm 3
      linarith [(h.centeredTilt_abs_moment hθ hlam 3).2]

/-- Recentring the tilt preserves every Fourier modulus exactly. -/
theorem norm_charFun_saRecenteredTilt (ν : ProbabilityMeasure ℝ) (lam t : ℝ) :
    ‖charFun (saRecenteredTilt ν lam) t‖ = ‖charFun (centeredTilt ν lam) t‖ := by
  have he : saRecenteredTilt ν lam = (centeredTilt ν lam).map
      (fun x => x - (1 + deriv (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam)) := by
    unfold saRecenteredTilt
    congr 1
    funext x
    ring
  rw [he, norm_charFun_map_sub_const]

/-- A single standardized third-moment constant for all the recentered tilts. -/
def saTiltStandardizedThird (vlo B θ : ℝ) : ℝ :=
  max 1 (saTiltThirdMoment B θ / Real.sqrt (3 / 4 * vlo) ^ 3)

theorem one_le_saTiltStandardizedThird (vlo B θ : ℝ) :
    1 ≤ saTiltStandardizedThird vlo B θ := le_max_left _ _

/-- A Cramer gap at the common low-frequency cutoff for the tilted class. -/
def saTiltCramerGap (vlo vhi B θ D c : ℝ) : ℝ :=
  min (1 / 2) (smoothPartCramerGap
    (tiltComponentFactor θ B c * D) (tiltComponentFactor θ B c * (c / 2))
    (tiltRawSecondBound θ B)
    (1 / (saTiltStandardizedThird vlo B θ * Real.sqrt (5 / 4 * vhi))))

theorem saTiltCramerGap_pos {vlo vhi B θ D c : ℝ}
    (hvhi : 0 < vhi) (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    0 < saTiltCramerGap vlo vhi B θ D c := by
  have hβ : 0 < saTiltStandardizedThird vlo B θ :=
    lt_of_lt_of_le zero_lt_one (one_le_saTiltStandardizedThird _ _ _)
  have hq : 0 < tiltComponentFactor θ B c := by
    unfold tiltComponentFactor
    positivity
  have hC : 0 < tiltRawSecondBound θ B := by unfold tiltRawSecondBound; positivity
  unfold saTiltCramerGap
  exact lt_min (by norm_num) (PGM.smoothPartCramerGap_pos
    (mul_pos hq hD) (by positivity) hC (by positivity))

theorem saTiltCramerGap_le_one (vlo vhi B θ D c : ℝ) :
    saTiltCramerGap vlo vhi B θ D c ≤ 1 :=
  (min_le_left _ _).trans (by norm_num)

/-- All analytic inputs to the density local CLT hold for the actual recentered tilt. -/
theorem UnivClass.saRecenteredTilt_lclt_inputs {D c : ℝ}
    (h : UnivClass vlo vhi κ₃ B θ ν) (hs : SmoothPart D c ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (hc : 0 < c)
    {lam : ℝ} (hlam : |lam| ≤ saTiltRadius vlo B θ) :
    let σ := Real.sqrt (iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam)
    let β := saTiltStandardizedThird vlo B θ
    let κ := saTiltCramerGap vlo vhi B θ D c
    0 < σ ∧
      (∫ x : ℝ, x ^ 2 ∂saRecenteredTilt ν lam) = σ ^ 2 ∧
      3 / 4 * vlo ≤ σ ^ 2 ∧ σ ^ 2 ≤ 5 / 4 * vhi ∧
      (∫ x : ℝ, |x| ^ 3 ∂saRecenteredTilt ν lam) ≤ β * σ ^ 3 ∧
      ∀ t : ℝ, 1 / (β * σ) ≤ |t| →
        ‖charFun (saRecenteredTilt ν lam) t‖ ≤ 1 - κ := by
  dsimp only
  let V := iteratedDeriv 2 (cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)) lam
  let β := saTiltStandardizedThird vlo B θ
  have hlhalf := hlam.trans (saTiltRadius_le_half vlo B hθ)
  have hl : |lam| < θ := hlhalf.trans_lt (by linarith)
  have hv := h.centered_cgf_variance_bracket hvlo hθ hlam
  have hVlo : 3 / 4 * vlo ≤ V := by dsimp [V]; linarith [h.var_ge]
  have hVhi : V ≤ 5 / 4 * vhi := by dsimp [V]; linarith [h.var_le]
  have hV : 0 < V := lt_of_lt_of_le (by positivity) hVlo
  have hσ : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hσsq : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV.le
  have hβ : 1 ≤ β := one_le_saTiltStandardizedThird _ _ _
  have hβ0 : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  refine ⟨hσ, (h.second_saRecenteredTilt hl).trans hσsq.symm, by rwa [hσsq],
    by rwa [hσsq], ?_, ?_⟩
  · apply (h.third_saRecenteredTilt hθ hlhalf).trans
    have hlow : 0 < Real.sqrt (3 / 4 * vlo) := Real.sqrt_pos.mpr (by positivity)
    have hratio : saTiltThirdMoment B θ / Real.sqrt (3 / 4 * vlo) ^ 3 ≤ β := le_max_right _ _
    rw [div_le_iff₀ (pow_pos hlow 3)] at hratio
    apply hratio.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hlow.le (Real.sqrt_le_sqrt hVlo) 3) hβ0.le
  · intro t ht
    let ρ : ProbabilityMeasure ℝ := ⟨centeredTilt ν lam, h.isProbabilityMeasure_centeredTilt hl.le⟩
    have hvhi : 0 < vhi := by linarith
    have hcut : 0 < 1 / (β * Real.sqrt (5 / 4 * vhi)) := by positivity
    have hnorm := (h.centeredTilt_cramer hs hθ hc hcut hlhalf (ρ := ρ) rfl).2
    rw [norm_charFun_saRecenteredTilt]
    have ht' : 1 / (β * Real.sqrt (5 / 4 * vhi)) ≤ |t| := by
      apply le_trans _ ht
      exact one_div_le_one_div_of_le (mul_pos hβ0 hσ)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hVhi) hβ0.le)
    apply (hnorm t ht').trans
    exact sub_le_sub_left (min_le_right (1 / 2) _) 1

/-- The tilted class has a genuine, uniform density local CLT with constants before the law. -/
theorem exists_uniform_saRecenteredTilt_density
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ lam : ℝ, |lam| ≤ saTiltRadius vlo B θ → ∀ h : ℝ, 0 < h →
      ∀ l : ℕ, 2 ≤ l → 1 / h ≤ (l : ℝ) ^ 8 → ∀ x : ℝ,
        |saGaussianDensity ((convPow (saRecenteredTilt ν lam) l).map ((Real.sqrt l)⁻¹ * ·))
          (Real.toNNReal (h ^ 2)) x - gaussianPDFReal 0
          (Real.toNNReal (iteratedDeriv 2 (cgf (fun y : ℝ => y - 1) (ν : Measure ℝ)) lam + h ^ 2)) x|
          ≤ C / Real.sqrt l := by
  let β := saTiltStandardizedThird vlo B θ
  let κ := saTiltCramerGap vlo vhi B θ D c
  have hβ : 1 ≤ β := one_le_saTiltStandardizedThird _ _ _
  have hκ : 0 < κ := saTiltCramerGap_pos hvhi hB hθ hD hc
  refine ⟨(2 * Real.pi)⁻¹ * saFourierCLTConstant (3 / 4 * vlo) (5 / 4 * vhi) β κ,
    mul_pos (by positivity) (saFourierCLTConstant_pos (by linarith) hκ), ?_⟩
  intro ν hν hs lam hlam h hh l hl hscale x
  have hlhalf := hlam.trans (saTiltRadius_le_half vlo B hθ)
  have hlt : |lam| < θ := hlhalf.trans_lt (by linarith)
  let := hν.isProbabilityMeasure_saRecenteredTilt hlt.le
  obtain ⟨hσ, hvar, hlo, hhi, hthird, hgap⟩ :=
    hν.saRecenteredTilt_lclt_inputs hs hvlo hθ hc hlam
  have he := saGaussianDensity_normalized_convPow_error_le
    (hν.memLp_saRecenteredTilt hlt) (hν.integral_saRecenteredTilt hlt) hvar hσ hβ hthird
    (show 0 < 3 / 4 * vlo by positivity) hlo hhi hκ
    (saTiltCramerGap_le_one _ _ _ _ _ _) hgap hh hl hscale x
  have hV : 0 ≤ iteratedDeriv 2 (cgf (fun y : ℝ => y - 1) (ν : Measure ℝ)) lam :=
    Real.sqrt_pos.mp hσ |>.le
  rwa [Real.sq_sqrt hV] at he

end

end PGM
