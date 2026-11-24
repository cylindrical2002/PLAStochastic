import PLAStochastic.Index.GEP.StrongApprox.Saddle.Parameters
import Mathlib.Analysis.Calculus.Taylor

/-!
# Uniform exponential inputs for the killed-walk potential

The two signs of the centered increment have the same positive mgf gap.
A small negative drift consumes only part of it. Exponential tail truncation
then supplies a common killing-potential constant across the entire law class.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

theorem UnivClass.kernel_centered_cgf_lower (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {t : ℝ} (ht : |t| ≤ saTiltRadius vlo B θ) :
    3 / 8 * vlo * t ^ 2 ≤ cgf (fun x : ℝ => x - 1) (ν : Measure ℝ) t := by
  by_cases ht0 : t = 0
  · simp [ht0]
  let f := cgf (fun x : ℝ => x - 1) (ν : Measure ℝ)
  have hwin : uIcc 0 t ⊆ Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ) :=
    (convex_Icc _ _).ordConnected.uIcc_subset
      (by constructor <;> linarith [saTiltRadius_pos (B := B) hvlo hθ]) (abs_le.mp ht)
  have hana (z : ℝ) (hz : z ∈ uIcc 0 t) : AnalyticAt ℝ f z :=
    analyticAt_cgf (h.centered_mem_interior
      (lt_of_le_of_lt ((abs_le.mpr (hwin hz)).trans (saTiltRadius_le_half vlo B hθ))
        (by linarith)))
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (n := 1) (x₀ := 0) (x := t) (Ne.symm ht0)
    (fun z hz => (hana z hz).contDiffAt.contDiffWithinAt)
  have hdif := uniqueDiffOn_uIcc (Ne.symm ht0)
  have hd (k : ℕ) : iteratedDerivWithin k f (uIcc 0 t) 0 = iteratedDeriv k f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hdif
      (hana 0 left_mem_uIcc).contDiffAt left_mem_uIcc
  have hf0 : f 0 = 0 := by simp [f]
  have hf'0 : deriv f 0 = 0 := h.deriv_centered_cgf_zero hθ
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, hd, iteratedDeriv_one,
    Nat.factorial, Nat.cast_one, Nat.cast_zero, zero_add, Nat.cast_mul, mul_one,
    smul_eq_mul, hf0, hf'0, sub_zero] at he
  have hlow := (h.centered_cgf_variance_bracket hvlo hθ
    (abs_le.mpr (hwin ⟨hz.1.le, hz.2.le⟩))).1
  have hp := mul_le_mul_of_nonneg_right
    (show 3 / 4 * vlo ≤ iteratedDeriv 2 f z by nlinarith [h.var_ge]) (sq_nonneg t)
  norm_num at he
  change 3 / 8 * vlo * t ^ 2 ≤ f t
  nlinarith

theorem UnivClass.kernel_centered_mgf_lower (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {t : ℝ} (ht : |t| ≤ saTiltRadius vlo B θ) :
    Real.exp (3 / 8 * vlo * t ^ 2) ≤
      ∫ x : ℝ, Real.exp (t * (x - 1)) ∂(ν : Measure ℝ) := by
  have hi := h.integrable_exp_centered (ht.trans (saTiltRadius_le_half vlo B hθ) |>.trans (by linarith))
  have hp := mgf_pos' (NeZero.ne (ν : Measure ℝ)) hi
  have he := Real.exp_le_exp.mpr (h.kernel_centered_cgf_lower hvlo hθ ht)
  change Real.exp (3 / 8 * vlo * t ^ 2) ≤
    Real.exp (Real.log (mgf (fun x : ℝ => x - 1) (ν : Measure ℝ) t)) at he
  rw [Real.exp_log hp] at he
  exact he

/-- A uniform positive-tail bound leaves a fixed part of the exponential budget. -/
theorem kernel_survival_tail_pointwise {θ lam R : ℝ} (hθ : 0 < θ)
    (hlam : lam ≤ θ / 4) (hR : 0 ≤ R) (y : ℝ) :
    (Ioi R).indicator (fun y => (y + 1) * Real.exp (lam * y)) y ≤
      (4 / θ + 1) * Real.exp (-(θ / 4) * R) * Real.exp (θ * |y|) := by
  by_cases hy : y ∈ Ioi R
  · rw [indicator_of_mem hy]
    have hy0 : 0 ≤ y := hR.trans hy.le
    have hexp : 1 ≤ Real.exp (θ / 4 * y) := Real.one_le_exp (by positivity)
    have hye : θ / 4 * y ≤ Real.exp (θ / 4 * y) := by
      linarith [Real.add_one_le_exp (θ / 4 * y)]
    have hyp : y + 1 ≤ (4 / θ + 1) * Real.exp (θ / 4 * y) := by
      have hpoly : y ≤ 4 / θ * Real.exp (θ / 4 * y) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hθ]
        linarith
      nlinarith
    calc
      (y + 1) * Real.exp (lam * y) ≤
          ((4 / θ + 1) * Real.exp (θ / 4 * y)) * Real.exp (lam * y) :=
        mul_le_mul_of_nonneg_right hyp (Real.exp_pos _).le
      _ = (4 / θ + 1) * Real.exp (θ / 4 * y + lam * y) := by rw [Real.exp_add]; ring
      _ ≤ (4 / θ + 1) * Real.exp (-(θ / 4) * R + θ * |y|) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        rw [abs_of_nonneg hy0]
        have hRy : R ≤ y := hy.le
        nlinarith [mul_le_mul_of_nonneg_right hlam hy0,
          mul_le_mul_of_nonneg_left hRy hθ.le]
      _ = _ := by rw [Real.exp_add]; ring
  · rw [indicator_of_notMem hy]
    positivity

theorem kernel_survival_tail_le {μ : Measure ℝ} {θ lam R B : ℝ}
    (hθ : 0 < θ) (hlam : lam ≤ θ / 4) (hR : 0 ≤ R)
    (hi : Integrable (fun y : ℝ => Real.exp (θ * |y|)) μ)
    (hB : (∫ y : ℝ, Real.exp (θ * |y|) ∂μ) ≤ B) :
    Integrable ((Ioi R).indicator (fun y => (y + 1) * Real.exp (lam * y))) μ ∧
    (∫ y, (Ioi R).indicator (fun y => (y + 1) * Real.exp (lam * y)) y ∂μ) ≤
      (4 / θ + 1) * B * Real.exp (-(θ / 4) * R) := by
  have hnonneg (y : ℝ) :
      0 ≤ (Ioi R).indicator (fun y => (y + 1) * Real.exp (lam * y)) y := by
    apply indicator_nonneg
    intro y hy
    exact mul_nonneg (by have hRy : R < y := hy; linarith) (Real.exp_pos _).le
  have hb := hi.const_mul ((4 / θ + 1) * Real.exp (-(θ / 4) * R))
  have hint : Integrable ((Ioi R).indicator (fun y => (y + 1) * Real.exp (lam * y))) μ := by
    apply hb.mono' ((by fun_prop : Measurable (fun y : ℝ => (y + 1) * Real.exp (lam * y))).indicator
      measurableSet_Ioi).aestronglyMeasurable
    exact ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg y)]
      exact kernel_survival_tail_pointwise hθ hlam hR y
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ y, ((4 / θ + 1) * Real.exp (-(θ / 4) * R)) * Real.exp (θ * |y|) ∂μ :=
      integral_mono hint hb (kernel_survival_tail_pointwise hθ hlam hR)
    _ = ((4 / θ + 1) * Real.exp (-(θ / 4) * R)) * ∫ y, Real.exp (θ * |y|) ∂μ :=
      integral_const_mul _ _
    _ ≤ (4 / θ + 1) * B * Real.exp (-(θ / 4) * R) := by
      nlinarith [mul_le_mul_of_nonneg_left hB
        (by positivity : 0 ≤ (4 / θ + 1) * Real.exp (-(θ / 4) * R))]

theorem kernel_survival_exists_tail_cutoff {θ B g : ℝ} (hθ : 0 < θ) (hg : 0 < g) :
    ∃ R : ℝ, 0 ≤ R ∧ (4 / θ + 1) * B * Real.exp (-(θ / 4) * R) ≤ g := by
  have ht : Tendsto (fun R : ℝ => (4 / θ + 1) * B * Real.exp (-(θ / 4) * R))
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show -(θ / 4) < 0 by linarith))).const_mul
        ((4 / θ + 1) * B)
  obtain ⟨R, hR, hRg⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (ht.eventually (gt_mem_nhds hg))).exists
  exact ⟨R, hR, hRg.le⟩

/-- Signed affine increments; the sign is absorbed into `a`. -/
def kernelSurvivalLaw (ν : ProbabilityMeasure ℝ) (a ρ : ℝ) : ProbabilityMeasure ℝ :=
  ν.map (show AEMeasurable (fun x : ℝ => a * (x - 1) - ρ) (ν : Measure ℝ) from by fun_prop)

theorem UnivClass.kernelSurvivalLaw_integrable (h : UnivClass vlo vhi κ₃ B θ ν)
    (a ρ : ℝ) : Integrable (fun y : ℝ => y) (kernelSurvivalLaw ν a ρ : Measure ℝ) := by
  rw [kernelSurvivalLaw, ProbabilityMeasure.toMeasure_map,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  exact (((h.memLp3.integrable (by norm_num)).sub (integrable_const 1)).const_mul a).sub
    (integrable_const ρ)

theorem UnivClass.kernelSurvivalLaw_mean (h : UnivClass vlo vhi κ₃ B θ ν)
    (a ρ : ℝ) : (∫ y : ℝ, y ∂(kernelSurvivalLaw ν a ρ : Measure ℝ)) = -ρ := by
  rw [kernelSurvivalLaw, ProbabilityMeasure.toMeasure_map, integral_map (by fun_prop) (by fun_prop)]
  have hi : Integrable (fun x : ℝ => a * (x - 1)) (ν : Measure ℝ) :=
    ((h.memLp3.integrable (by norm_num)).sub (integrable_const 1)).const_mul a
  rw [integral_sub hi (integrable_const ρ), integral_const_mul, h.integral_centered_eq_zero]
  simp

theorem UnivClass.kernelSurvivalLaw_exp_abs (h : UnivClass vlo vhi κ₃ B θ ν)
    (hθ : 0 < θ) {a ρ : ℝ} (ha : |a| ≤ 2) (hρ : |ρ| ≤ 1) :
    Integrable (fun y : ℝ => Real.exp (θ / 4 * |y|))
      (kernelSurvivalLaw ν a ρ : Measure ℝ) ∧
    (∫ y : ℝ, Real.exp (θ / 4 * |y|) ∂(kernelSurvivalLaw ν a ρ : Measure ℝ)) ≤
      Real.exp (θ / 4) * (Real.exp θ * max B 1) := by
  have hi := h.integrable_exp_abs_sub_one hθ.le le_rfl
  have hpt (x : ℝ) : Real.exp (θ / 4 * |a * (x - 1) - ρ|) ≤
      Real.exp (θ / 4) * Real.exp (θ * |x - 1|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha' : |a * (x - 1)| ≤ 2 * |x - 1| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    have hab := (abs_sub _ _).trans (add_le_add ha' hρ)
    have hh : |a * (x - 1) - ρ| ≤ 2 * |x - 1| + 1 := hab
    nlinarith [abs_nonneg (x - 1)]
  have hi' : Integrable (fun x : ℝ => Real.exp (θ / 4 * |a * (x - 1) - ρ|)) (ν : Measure ℝ) :=
    (hi.const_mul (Real.exp (θ / 4))).mono' (by fun_prop)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hpt x)
  constructor
  · rw [kernelSurvivalLaw, ProbabilityMeasure.toMeasure_map,
      integrable_map_measure (by fun_prop) (by fun_prop)]
    exact hi'
  · rw [kernelSurvivalLaw, ProbabilityMeasure.toMeasure_map, integral_map (by fun_prop) (by fun_prop)]
    calc
      _ ≤ ∫ x : ℝ, Real.exp (θ / 4) * Real.exp (θ * |x - 1|) ∂(ν : Measure ℝ) :=
        integral_mono hi' (hi.const_mul _) hpt
      _ = Real.exp (θ / 4) * ∫ x : ℝ, Real.exp (θ * |x - 1|) ∂(ν : Measure ℝ) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (h.integral_exp_abs_sub_one_le hθ) (Real.exp_pos _).le

theorem UnivClass.kernelSurvivalLaw_mgf_lower (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {a ρ lam : ℝ}
    (ht : |lam * a| ≤ saTiltRadius vlo B θ) :
    Integrable (fun y : ℝ => Real.exp (lam * y)) (kernelSurvivalLaw ν a ρ : Measure ℝ) ∧
    Real.exp (3 / 8 * vlo * (lam * a) ^ 2 - lam * ρ) ≤
      ∫ y : ℝ, Real.exp (lam * y) ∂(kernelSurvivalLaw ν a ρ : Measure ℝ) := by
  have hi := h.integrable_exp_centered
    (ht.trans (saTiltRadius_le_half vlo B hθ) |>.trans (by linarith))
  have heq : (fun x : ℝ => Real.exp (lam * (a * (x - 1) - ρ))) =
      fun x => Real.exp (-lam * ρ) * Real.exp ((lam * a) * (x - 1)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · rw [kernelSurvivalLaw, ProbabilityMeasure.toMeasure_map,
      integrable_map_measure (by fun_prop) (by fun_prop)]
    dsimp only [Function.comp_def]
    rw [heq]
    exact hi.const_mul _
  · rw [kernelSurvivalLaw, ProbabilityMeasure.toMeasure_map,
      integral_map (by fun_prop) (by fun_prop), heq, integral_const_mul]
    have hb := mul_le_mul_of_nonneg_left (h.kernel_centered_mgf_lower hvlo hθ ht)
      (Real.exp_pos (-lam * ρ)).le
    calc
      _ = Real.exp (-lam * ρ) * Real.exp (3 / 8 * vlo * (lam * a) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := hb

end
end PGM
