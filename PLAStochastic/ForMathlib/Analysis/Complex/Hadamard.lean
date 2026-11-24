import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The second-order Hadamard quotient

For `ψ : ℂ → ℂ` set `hadamard2 ψ b u = ∫₀¹ (1 - t) ψ''(b + t u) dt`. If `ψ` is holomorphic on an
open set containing the segment `[b, b + u]`, then (`hadamard2_spec`)

  `ψ (b + u) = ψ b + ψ'(b) u + u² · hadamard2 ψ b u`,

`hadamard2 ψ b 0 = ψ''(b)/2` (`hadamard2_zero`), and `‖hadamard2 ψ b u - c/2‖ ≤ K/2` when
`‖ψ'' - c‖ ≤ K` on the segment (`norm_hadamard2_sub_le`). If `ψ` is holomorphic on `B(0, ρ)`, then
`(b, u) ↦ hadamard2 ψ b u` is jointly holomorphic on `{‖b‖ + ‖u‖ < ρ}`
(`differentiableOn_hadamard2`).
-/

noncomputable section

open Set Metric Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace PGM

theorem integral_one_sub_unit : ∫ t in (0 : ℝ)..1, (1 - t) = 1 / 2 := by
  have h := intervalIntegral.integral_sub (μ := volume) (a := 0) (b := 1)
    (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t) intervalIntegrable_const
    (continuous_id.intervalIntegrable 0 1)
  rw [h, intervalIntegral.integral_const, integral_id]
  norm_num

theorem integral_one_sub_unit_complex : ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) = (1 / 2 : ℂ) := by
  rw [intervalIntegral.integral_ofReal, integral_one_sub_unit]
  norm_num

/-- `∫₀¹ (1 - t) ψ''(b + t u) dt`. -/
@[irreducible] def hadamard2 (ψ : ℂ → ℂ) (b u : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) * deriv (deriv ψ) (b + t * u)

variable {ψ : ℂ → ℂ}

theorem hasDerivAt_comp_affine {g g' : ℂ → ℂ} {b u : ℂ} {t : ℝ}
    (hg : HasDerivAt g (g' (b + t * u)) (b + t * u)) :
    HasDerivAt (fun s : ℝ => g (b + s * u)) (g' (b + t * u) * u) t := by
  have h1 : HasDerivAt (fun s : ℝ => b + (s : ℂ) * u) u t := by
    have := ((hasDerivAt_id (t : ℂ)).mul_const u).const_add b
    simpa using this.comp_ofReal
  exact hg.comp t h1

theorem hadamard2_spec {U : Set ℂ} (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U) {b u : ℂ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, b + t * u ∈ U) :
    ψ (b + u) = ψ b + deriv ψ b * u + u ^ 2 * hadamard2 ψ b u := by
  have hψ' : DifferentiableOn ℂ (deriv ψ) U := hψ.deriv hU
  have hψ'' : DifferentiableOn ℂ (deriv (deriv ψ)) U := hψ'.deriv hU
  set g : ℝ → ℂ := fun t => ψ (b + t * u) + ((1 - t : ℝ) : ℂ) * u * deriv ψ (b + t * u) with hg
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt g
      (u ^ 2 * (((1 - t : ℝ) : ℂ) * deriv (deriv ψ) (b + t * u))) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hmem := hseg t ht
    have h1 : HasDerivAt (fun s : ℝ => ψ (b + s * u)) (deriv ψ (b + t * u) * u) t :=
      hasDerivAt_comp_affine ((hψ _ hmem).differentiableAt (hU.mem_nhds hmem)).hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => deriv ψ (b + s * u)) (deriv (deriv ψ) (b + t * u) * u) t :=
      hasDerivAt_comp_affine ((hψ' _ hmem).differentiableAt (hU.mem_nhds hmem)).hasDerivAt
    have h3 : HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ) * u) (-u) t := by
      have : HasDerivAt (fun s : ℝ => ((1 - s : ℝ) : ℂ)) (-1) t := by
        have := ((hasDerivAt_id t).const_sub 1).ofReal_comp
        simpa using this
      simpa using this.mul_const u
    have := h1.add (h3.mul h2)
    refine this.congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun t : ℝ =>
      u ^ 2 * (((1 - t : ℝ) : ℂ) * deriv (deriv ψ) (b + t * u))) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul (by fun_prop) ?_)
    refine hψ''.continuousOn.comp (by fun_prop) ?_
    intro t ht; exact hseg t ht
  have hint := integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable)
  rw [intervalIntegral.integral_const_mul] at hint
  have h1 : g 1 = ψ (b + u) := by simp [hg]
  have h0 : g 0 = ψ b + u * deriv ψ b := by simp [hg]
  rw [h1, h0] at hint
  unfold hadamard2
  linear_combination -hint

theorem hadamard2_zero (b : ℂ) : hadamard2 ψ b 0 = deriv (deriv ψ) b / 2 := by
  unfold hadamard2
  simp only [mul_zero, add_zero]
  rw [intervalIntegral.integral_mul_const, integral_one_sub_unit_complex]; ring

/-- `‖hadamard2 ψ b u - c/2‖ ≤ K/2` when `‖ψ''(b + t u) - c‖ ≤ K` for `t ∈ [0,1]`. -/
theorem norm_hadamard2_sub_le {U : Set ℂ} (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U)
    {b u c : ℂ} {K : ℝ} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, b + t * u ∈ U)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (deriv ψ) (b + t * u) - c‖ ≤ K) :
    ‖hadamard2 ψ b u - c / 2‖ ≤ K / 2 := by
  have hψ'' : DifferentiableOn ℂ (deriv (deriv ψ)) U := (hψ.deriv hU).deriv hU
  have hc : c / 2 = ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) * c := by
    rw [intervalIntegral.integral_mul_const, integral_one_sub_unit_complex]; ring
  have hcont : ContinuousOn (fun t : ℝ => ((1 - t : ℝ) : ℂ) * deriv (deriv ψ) (b + t * u))
      (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.mul (by fun_prop) ?_
    refine hψ''.continuousOn.comp (by fun_prop) ?_
    intro t ht; exact hseg t ht
  have e : hadamard2 ψ b u - c / 2 =
      ∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) * (deriv (deriv ψ) (b + t * u) - c) := by
    rw [hc, hadamard2, ← intervalIntegral.integral_sub hcont.intervalIntegrable
      ((by fun_prop : Continuous fun t : ℝ => ((1 - t : ℝ) : ℂ) * c).intervalIntegrable 0 1)]
    congr 1; funext t; ring
  rw [e]
  have hb : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖((1 - t : ℝ) : ℂ) * (deriv (deriv ψ) (b + t * u) - c)‖ ≤ (1 - t) * K := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
    exact mul_le_mul_of_nonneg_left (hK t ht') (by linarith [ht.2])
  have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) zero_le_one
    (Eventually.of_forall hb)
    ((by fun_prop : Continuous fun t : ℝ => (1 - t) * K).intervalIntegrable 0 1)
  refine this.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const, integral_one_sub_unit]
  ring

/-- Joint holomorphy of the Hadamard quotient on `{‖b‖ + ‖u‖ < ρ}`. -/
theorem differentiableOn_hadamard2 {ρ : ℝ} (hψ : DifferentiableOn ℂ ψ (ball 0 ρ)) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => hadamard2 ψ x.1 x.2) {x | ‖x.1‖ + ‖x.2‖ < ρ} := by
  have hψ1 : DifferentiableOn ℂ (deriv ψ) (ball 0 ρ) := hψ.deriv isOpen_ball
  have hψ2 : DifferentiableOn ℂ (deriv (deriv ψ)) (ball 0 ρ) := hψ1.deriv isOpen_ball
  have hψ3 : DifferentiableOn ℂ (deriv (deriv (deriv ψ))) (ball 0 ρ) := hψ2.deriv isOpen_ball
  rintro ⟨b₀, u₀⟩ hx₀
  change ‖b₀‖ + ‖u₀‖ < ρ at hx₀
  set ε : ℝ := (ρ - ‖b₀‖ - ‖u₀‖) / 4 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set ρ' : ℝ := ‖b₀‖ + ‖u₀‖ + 2 * ε with hρ'
  have hρ'ρ : ρ' < ρ := by rw [hρ', hε]; linarith
  -- points `b + t u` with `(b, u)` near `(b₀, u₀)` stay in `closedBall 0 ρ'`
  have hpt : ∀ x ∈ ball ((b₀, u₀) : ℂ × ℂ) ε, ∀ t ∈ Icc (0 : ℝ) 1,
      x.1 + t * x.2 ∈ closedBall (0 : ℂ) ρ' := by
    intro x hx t ht
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hx
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖x.1‖ ≤ ‖b₀‖ + ε := by
      calc ‖x.1‖ = ‖(x.1 - b₀) + b₀‖ := by ring_nf
        _ ≤ ‖x.1 - b₀‖ + ‖b₀‖ := norm_add_le _ _
        _ ≤ ‖b₀‖ + ε := by linarith [hx.1]
    have h2 : ‖x.2‖ ≤ ‖u₀‖ + ε := by
      calc ‖x.2‖ = ‖(x.2 - u₀) + u₀‖ := by ring_nf
        _ ≤ ‖x.2 - u₀‖ + ‖u₀‖ := norm_add_le _ _
        _ ≤ ‖u₀‖ + ε := by linarith [hx.2]
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2
    calc ‖x.1 + t * x.2‖ ≤ ‖x.1‖ + ‖(t : ℂ)‖ * ‖x.2‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ ‖x.1‖ + 1 * ‖x.2‖ := by gcongr
      _ ≤ ρ' := by rw [hρ']; linarith
  have hsub : closedBall (0 : ℂ) ρ' ⊆ ball 0 ρ := closedBall_subset_ball hρ'ρ
  -- a bound on `ψ'''` on `closedBall 0 ρ'`
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) ρ').exists_bound_of_continuousOn
    (hψ3.continuousOn.mono hsub)
  set F : ℂ × ℂ → ℝ → ℂ := fun x t => ((1 - t : ℝ) : ℂ) * deriv (deriv ψ) (x.1 + t * x.2)
    with hF
  set F' : ℂ × ℂ → ℝ → ℂ × ℂ →L[ℂ] ℂ := fun x t =>
    (((1 - t : ℝ) : ℂ) * deriv (deriv (deriv ψ)) (x.1 + t * x.2)) •
      (ContinuousLinearMap.fst ℂ ℂ ℂ + (t : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) with hF'
  have hball : ball ((b₀, u₀) : ℂ × ℂ) ε ∈ 𝓝 ((b₀, u₀) : ℂ × ℂ) := ball_mem_nhds _ hε0
  have hdiffF : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ ball ((b₀, u₀) : ℂ × ℂ) ε,
      HasFDerivAt (fun x => F x t) (F' x t) x := by
    intro t ht x hx
    have hmem := hsub (hpt x hx t ht)
    have hlin : HasFDerivAt (fun x : ℂ × ℂ => x.1 + (t : ℂ) * x.2)
        (ContinuousLinearMap.fst ℂ ℂ ℂ + (t : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) x := by
      have h1 := hasFDerivAt_fst (𝕜 := ℂ) (p := x)
      have h2 := (hasFDerivAt_snd (𝕜 := ℂ) (p := x)).const_smul (t : ℂ)
      exact h1.add h2
    have hd := ((hψ2 _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)).hasDerivAt
    have hcomp := hd.comp_hasFDerivAt x hlin
    have h2 : HasFDerivAt (fun x => F x t) ((((1 - t : ℝ) : ℂ)) •
        (deriv (deriv (deriv ψ)) (x.1 + ↑t * x.2) •
          (ContinuousLinearMap.fst ℂ ℂ ℂ + (t : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ))) x :=
      hcomp.const_mul (((1 - t : ℝ) : ℂ))
    rw [smul_smul] at h2
    exact h2
  have hint : ∀ x ∈ ball ((b₀, u₀) : ℂ × ℂ) ε, ContinuousOn (F x) (Icc 0 1) := by
    intro x hx
    refine ContinuousOn.mul (by fun_prop) ?_
    exact (hψ2.continuousOn.mono hsub).comp (by fun_prop) (fun t ht => hpt x hx t ht)
  have hx₀b : ((b₀, u₀) : ℂ × ℂ) ∈ ball ((b₀, u₀) : ℂ × ℂ) ε := mem_ball_self hε0
  have hmain := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (a := 0) (b := 1) (bound := fun _ => 2 * B) (F := F) (F' := F')
    (x₀ := ((b₀, u₀) : ℂ × ℂ)) hball ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · have e : (fun x : ℂ × ℂ => hadamard2 ψ x.1 x.2) = fun x => ∫ t in (0 : ℝ)..1, F x t := by
      funext x; rw [hadamard2]
    rw [e]
    exact hmain.differentiableAt.differentiableWithinAt
  · filter_upwards [hball] with x hx
    rw [uIoc_of_le zero_le_one]
    exact ((hint x hx).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · exact ((hint _ hx₀b).intervalIntegrable_of_Icc zero_le_one)
  · rw [uIoc_of_le zero_le_one]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    have hc : ContinuousOn (fun t : ℝ => ((1 - t : ℝ) : ℂ) *
        deriv (deriv (deriv ψ)) (b₀ + t * u₀)) (Ioc 0 1) := by
      refine ContinuousOn.mul (by fun_prop) ?_
      exact (hψ3.continuousOn.mono hsub).comp (by fun_prop)
        (fun t ht => hpt _ hx₀b t (Ioc_subset_Icc_self ht))
    have hl : Continuous fun t : ℝ =>
        (ContinuousLinearMap.fst ℂ ℂ ℂ + (t : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) := by
      fun_prop
    exact hc.smul hl.continuousOn
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    simp only [hF']
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [ht'.2])]
    have h1 : ‖deriv (deriv (deriv ψ)) (x.1 + t * x.2)‖ ≤ B := hB _ (hpt x hx t ht')
    have h2 : ‖ContinuousLinearMap.fst ℂ ℂ ℂ + (t : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ‖ ≤ 2 := by
      calc _ ≤ ‖ContinuousLinearMap.fst ℂ ℂ ℂ‖ + ‖(t : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ‖ :=
            norm_add_le _ _
        _ ≤ 1 + 1 := by
            gcongr
            · exact ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ
            · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.1]
              exact mul_le_one₀ ht'.2 (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ)
        _ = 2 := by norm_num
    have hB0 : 0 ≤ B := (norm_nonneg _).trans h1
    calc (1 - t) * ‖deriv (deriv (deriv ψ)) (x.1 + t * x.2)‖ *
          ‖ContinuousLinearMap.fst ℂ ℂ ℂ + (t : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ‖
        ≤ 1 * B * 2 := by
          gcongr
          · linarith [ht'.1]
      _ = 2 * B := by ring
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [uIoc_of_le zero_le_one] at ht
    exact hdiffF t (Ioc_subset_Icc_self ht) x hx

end PGM
