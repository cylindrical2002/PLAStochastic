import PLAStochastic.Index.CEPS.Glue.Defs
import PLAStochastic.Index.GEP.Response.Score.UniformBounds
import PLAStochastic.Index.GEP.PointwiseSmall.MixtureClass

/-!
# WP11a: class facts for the glue

* `cepsOutChar_eq_actual`: `φ_ν(u) = E e^{-t S_T}` at `t = -iu/C`;
* `ceps_class_moments`: on a regular class and for `ε ≥ ε₀`, `C/ε² ∈ [s_lo, s_hi]` with
  `s_lo > 0`, Wald's identity `E S_T = C`, and `E S_T² ≤ B₂ ε⁴` (from the uniform exponential
  moment of the normalised output).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- The output characteristic function is the actual transform at `t = -iu/C`. -/
theorem cepsOutChar_eq_actual (eps : ℝ) (ν : ProbabilityMeasure ℝ) (u : ℝ) :
    cepsOutChar eps ν u =
      cepsActualTransform eps ν (Complex.I * ((-(u / lawC eps ν) : ℝ) : ℂ)) := by
  unfold cepsOutChar cepsActualTransform
  change ∫ x, Complex.exp (Complex.I * u * x) ∂((iidLaw ν).map
    (fun g => stopSum eps g / lawC eps ν)) = _
  rw [integral_map ((measurable_stopSum eps).div_const _).aemeasurable
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (Complex.I * u * x)).aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  congr 1
  push_cast
  ring

/-- **Class facts.** Bounds on `C/ε²`, Wald's identity and the second moment of `S_T`. -/
theorem ceps_class_moments {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hv : vlo ≤ vhi) :
    ∃ e₀ s_lo s_hi B₂ : ℝ, 1 ≤ e₀ ∧ 0 < s_lo ∧ 0 ≤ B₂ ∧ ∀ eps : ℝ, e₀ ≤ eps →
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
        s_lo ≤ lawC eps ν / eps ^ 2 ∧ lawC eps ν / eps ^ 2 ≤ s_hi ∧
        Integrable (stopSum eps) (iidLaw ν) ∧ ∫ g, stopSum eps g ∂(iidLaw ν) = lawC eps ν ∧
        Integrable (fun g => stopSum eps g ^ 2) (iidLaw ν) ∧
        ∫ g, stopSum eps g ^ 2 ∂(iidLaw ν) ≤ B₂ * eps ^ 4 := by
  obtain ⟨e0, he01, hfacts⟩ := regLaw_facts hD hθ hvlo hv
  have hv0 := regV_pos hvlo
  have hb0 : 0 < regB vhi := hv0.trans_le (regV_le_regB hv)
  set s_hi : ℝ := cPlus / regV vlo with hs_hi
  have hs_hi0 : 0 ≤ s_hi := div_nonneg cPlus_pos.le hv0.le
  refine ⟨max e0 (epsZero (regB vhi) (regBeta D θ vlo)), 1 / (128 * regB vhi), s_hi,
    2 * CK * s_hi ^ 2 / θK ^ 2, le_trans he01 (le_max_left _ _), by positivity,
    by have := CK_pos; have := θK_pos; positivity, fun eps heps ν hν => ?_⟩
  have he0 : e0 ≤ eps := le_trans (le_max_left _ _) heps
  have hez : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps := le_trans (le_max_right _ _) heps
  obtain ⟨-, hClo, -, hE, -, hpos⟩ := hfacts eps he0 ν hν
  have hm := hν.momClass hθ hvlo
  obtain ⟨-, heps1, -, hvm, -, -, -, hCp, -⟩ := momClass_setup hv0 hez hm
  have hepspos : 0 < eps := lt_of_lt_of_le one_pos heps1
  have he2 : 0 < eps ^ 2 := by positivity
  have hvar : 0 < lawVar ν := hv0.trans_le hm.var_ge
  have hC0 : 0 < lawC eps ν := lt_of_lt_of_le (by positivity) hClo
  -- bounds on `C/ε²`
  have hlo : 1 / (128 * regB vhi) ≤ lawC eps ν / eps ^ 2 := by
    rw [le_div_iff₀ he2]
    calc 1 / (128 * regB vhi) * eps ^ 2 = eps ^ 2 / (128 * regB vhi) := by ring
      _ ≤ lawC eps ν := hClo
  have hhi : lawC eps ν / eps ^ 2 ≤ s_hi := by
    rw [div_le_iff₀ he2]
    calc lawC eps ν ≤ cPlus * (eps ^ 2 / lawVar ν) := hCp
      _ ≤ cPlus * (eps ^ 2 / regV vlo) := mul_le_mul_of_nonneg_left hvm cPlus_pos.le
      _ = s_hi * eps ^ 2 := by rw [hs_hi]; ring
  -- the second moment
  obtain ⟨hint, hle⟩ := integrable_exp_output hE
  set C := lawC eps ν with hC
  have hθK := θK_pos
  have hbound : ∀ g, 0 ≤ stopSum eps g →
      stopSum eps g ^ 2 ≤ 2 * C ^ 2 / θK ^ 2 * Real.exp (θK * (stopSum eps g / C)) := by
    intro g hg
    have hx : 0 ≤ θK * (stopSum eps g / C) := by positivity
    have h1 := Real.pow_div_factorial_le_exp _ hx 2
    rw [Nat.factorial_two, Nat.cast_two] at h1
    have e : stopSum eps g ^ 2 = 2 * C ^ 2 / θK ^ 2 * ((θK * (stopSum eps g / C)) ^ 2 / 2) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hS2 : Integrable (fun g => stopSum eps g ^ 2) (iidLaw ν) := by
    refine Integrable.mono' (hint.const_mul (2 * C ^ 2 / θK ^ 2))
      ((measurable_stopSum eps).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hpos] with g hg
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound g hg.le
  have hS1 : Integrable (stopSum eps) (iidLaw ν) := by
    refine Integrable.mono' ((integrable_const 1).add hS2)
      (measurable_stopSum eps).aestronglyMeasurable (Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (|stopSum eps g| - 1), sq_abs (stopSum eps g), abs_nonneg (stopSum eps g)]
  refine ⟨hlo, hhi, hS1, pw_integral_stopSum hv0 hez hm, hS2, ?_⟩
  calc ∫ g, stopSum eps g ^ 2 ∂(iidLaw ν)
      ≤ ∫ g, 2 * C ^ 2 / θK ^ 2 * Real.exp (θK * (stopSum eps g / C)) ∂(iidLaw ν) := by
        refine integral_mono_ae hS2 (hint.const_mul _) ?_
        filter_upwards [hpos] with g hg
        exact hbound g hg.le
    _ = 2 * C ^ 2 / θK ^ 2 * ∫ g, Real.exp (θK * (stopSum eps g / C)) ∂(iidLaw ν) :=
        integral_const_mul _ _
    _ ≤ 2 * C ^ 2 / θK ^ 2 * CK := mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ 2 * (s_hi * eps ^ 2) ^ 2 / θK ^ 2 * CK := by
        have hC2 : C ≤ s_hi * eps ^ 2 := by rwa [div_le_iff₀ he2] at hhi
        have := CK_pos
        gcongr
    _ = 2 * CK * s_hi ^ 2 / θK ^ 2 * eps ^ 4 := by ring

end

end PGM
