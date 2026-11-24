import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Osgood's lemma in two complex variables

A function `F : ℂ × ℂ → ℂ` that is continuous on an open set `U` and holomorphic in each variable
separately is jointly (Fréchet) holomorphic on `U` (`osgood`).

Proof: near `x₀ = (z₀, w₀)`, the one-variable Cauchy formula in `z` writes
`F(z, w) = (2πi)⁻¹ ∮_{|ζ - z₀| = ρ} (ζ - z)⁻¹ F(ζ, w) dζ`; the integrand is jointly differentiable
in `(z, w)` with derivative bounded by Cauchy estimates in `w`, and differentiation under the
integral sign gives joint differentiability. Measurability of the `w`-derivative along the circle
is obtained as a limit of difference quotients (`aestronglyMeasurable_deriv_param`).
-/

noncomputable section

open Set Metric Filter Topology MeasureTheory Complex
open scoped Interval

namespace PGM

/-- A parametric complex derivative is a.e. strongly measurable when the difference quotients
are. -/
theorem aestronglyMeasurable_deriv_param {α : Type*} [MeasurableSpace α] {m : Measure α}
    {G : α → ℂ → ℂ} {q₀ : ℂ} {h : ℕ → ℂ} (hne : ∀ n, h n ≠ 0) (hlim : Tendsto h atTop (𝓝 0))
    (hm : ∀ n, AEStronglyMeasurable (fun y => G y (q₀ + h n)) m)
    (hm0 : AEStronglyMeasurable (fun y => G y q₀) m) (hd : ∀ y, DifferentiableAt ℂ (G y) q₀) :
    AEStronglyMeasurable (fun y => deriv (G y) q₀) m := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n y => (h n)⁻¹ • (G y (q₀ + h n) - G y q₀))
    (fun n => by have := ((hm n).sub hm0).const_smul (h n)⁻¹; exact this)
    (Eventually.of_forall fun y => ?_)
  have h1 := (hd y).hasDerivAt.tendsto_slope_zero
  have h2 : Tendsto h atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hne⟩
  exact h1.comp h2

/-- The sequence `ρ/(n+1)` as complex numbers tends to `0` through nonzero values. -/
theorem tendsto_ofReal_div_succ {ρ : ℝ} (hρ : 0 < ρ) :
    (∀ n : ℕ, ((ρ / (n + 1) : ℝ) : ℂ) ≠ 0) ∧
      Tendsto (fun n : ℕ => ((ρ / (n + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
  refine ⟨fun n => ofReal_ne_zero.mpr (by positivity), ?_⟩
  have h2 : Tendsto (fun n : ℕ => ρ / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h3 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ρ
    rw [mul_zero] at h3
    refine h3.congr fun n => ?_
    rw [mul_one_div]
  have h4 := (continuous_ofReal.tendsto 0).comp h2
  rw [ofReal_zero] at h4
  exact h4

set_option maxHeartbeats 1000000 in
/-- **Osgood's lemma.** Continuous and separately holomorphic on an open set of `ℂ²` implies
jointly holomorphic. -/
theorem osgood {U : Set (ℂ × ℂ)} (hU : IsOpen U) {F : ℂ × ℂ → ℂ} (hc : ContinuousOn F U)
    (h1 : ∀ x ∈ U, DifferentiableAt ℂ (fun z => F (z, x.2)) x.1)
    (h2 : ∀ x ∈ U, DifferentiableAt ℂ (fun w => F (x.1, w)) x.2) :
    DifferentiableOn ℂ F U := by
  intro x₀ hx₀
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  set r : ℝ := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨z₀, w₀⟩ := x₀
  -- the closed polydisc of radius `2r`
  have hK : closedBall ((z₀, w₀) : ℂ × ℂ) (2 * r) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨M, hM⟩ := (isCompact_closedBall ((z₀, w₀) : ℂ × ℂ) (2 * r)).exists_bound_of_continuousOn
    (hc.mono hK)
  have hmemK : ∀ z w : ℂ, ‖z - z₀‖ ≤ 2 * r → ‖w - w₀‖ ≤ 2 * r →
      ((z, w) : ℂ × ℂ) ∈ closedBall ((z₀, w₀) : ℂ × ℂ) (2 * r) := by
    intro z w hz hw
    rw [mem_closedBall, Prod.dist_eq, max_le_iff, dist_eq_norm, dist_eq_norm]
    exact ⟨hz, hw⟩
  set ρ : ℝ := 3 * r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  -- Cauchy representation near `x₀`
  set G : ℂ × ℂ → ℂ := fun x => (2 * Real.pi * I : ℂ)⁻¹ • ∮ ζ in C(z₀, ρ), (ζ - x.1)⁻¹ • F (ζ, x.2)
    with hG
  have hrep : ∀ x ∈ ball ((z₀, w₀) : ℂ × ℂ) r, F x = G x := by
    rintro ⟨z, w⟩ hx
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hx
    have hdiff : DifferentiableOn ℂ (fun ζ => F (ζ, w)) (ball z₀ (2 * r)) := by
      intro ζ hζ
      rw [mem_ball, dist_eq_norm] at hζ
      have hmem : ((ζ, w) : ℂ × ℂ) ∈ U := hK (hmemK ζ w hζ.le (by linarith [hx.2]))
      exact (h1 _ hmem).differentiableWithinAt
    have hdc := hdiff.diffContOnCl_ball (c := z₀) (R := ρ)
      (closedBall_subset_ball (by rw [hρ]; linarith))
    have hzmem : z ∈ ball z₀ ρ := by rw [mem_ball, dist_eq_norm, hρ]; linarith [hx.1]
    exact (hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hzmem).symm
  have hev : F =ᶠ[𝓝 ((z₀, w₀) : ℂ × ℂ)] G :=
    Filter.eventually_of_mem (ball_mem_nhds _ hr0) hrep
  suffices hGd : DifferentiableAt ℂ G (z₀, w₀) from
    (hGd.congr_of_eventuallyEq hev).differentiableWithinAt
  -- differentiate under the circle integral
  set ζ : ℝ → ℂ := circleMap z₀ ρ with hζ
  have hζn : ∀ θ, ‖ζ θ - z₀‖ = ρ := by
    intro θ; rw [hζ, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ0]
  set Φ : ℂ × ℂ → ℝ → ℂ := fun x θ => deriv (circleMap z₀ ρ) θ • ((ζ θ - x.1)⁻¹ • F (ζ θ, x.2))
    with hΦ
  set dF : ℝ → ℂ → ℂ := fun θ w => deriv (fun w => F (ζ θ, w)) w with hdF
  set Φ' : ℂ × ℂ → ℝ → ℂ × ℂ →L[ℂ] ℂ := fun x θ =>
    (deriv (circleMap z₀ ρ) θ * (((ζ θ - x.1) ^ 2)⁻¹ * F (ζ θ, x.2))) •
        ContinuousLinearMap.fst ℂ ℂ ℂ +
      (deriv (circleMap z₀ ρ) θ * ((ζ θ - x.1)⁻¹ * dF θ x.2)) • ContinuousLinearMap.snd ℂ ℂ ℂ
    with hΦ'
  have hball : ∀ x ∈ ball ((z₀, w₀) : ℂ × ℂ) r, ‖x.1 - z₀‖ < r ∧ ‖x.2 - w₀‖ < r := by
    intro x hx
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hx
    exact hx
  have hsep : ∀ θ, ∀ x ∈ ball ((z₀, w₀) : ℂ × ℂ) r, r / 2 ≤ ‖ζ θ - x.1‖ := by
    intro θ x hx
    have h := (hball x hx).1
    have := norm_sub_norm_le (ζ θ - z₀) (x.1 - z₀)
    rw [hζn θ, show ζ θ - z₀ - (x.1 - z₀) = ζ θ - x.1 by ring] at this
    rw [hρ] at this; linarith
  have hmemU : ∀ θ, ∀ w : ℂ, ‖w - w₀‖ < 2 * r → ((ζ θ, w) : ℂ × ℂ) ∈ U := by
    intro θ w hw
    exact hK (hmemK _ _ (by rw [hζn θ, hρ]; linarith) hw.le)
  -- `w`-derivative bound by Cauchy
  have hdFb : ∀ θ, ∀ w : ℂ, ‖w - w₀‖ < r → ‖dF θ w‖ ≤ 2 * M / r := by
    intro θ w hw
    have hdiff : DifferentiableOn ℂ (fun w => F (ζ θ, w)) (ball w r) := by
      intro w' hw'
      rw [mem_ball, dist_eq_norm] at hw'
      have : ‖w' - w₀‖ < 2 * r := by
        calc ‖w' - w₀‖ = ‖(w' - w) + (w - w₀)‖ := by ring_nf
          _ ≤ ‖w' - w‖ + ‖w - w₀‖ := norm_add_le _ _
          _ < 2 * r := by linarith
      exact (h2 _ (hmemU θ w' this)).differentiableWithinAt
    have hb : ∀ w' ∈ ball w r, ‖F (ζ θ, w')‖ ≤ M := by
      intro w' hw'
      rw [mem_ball, dist_eq_norm] at hw'
      exact hM _ (hmemK _ _ (by rw [hζn θ, hρ]; linarith) (by
        calc ‖w' - w₀‖ = ‖(w' - w) + (w - w₀)‖ := by ring_nf
          _ ≤ ‖w' - w‖ + ‖w - w₀‖ := norm_add_le _ _
          _ ≤ 2 * r := by linarith))
    have := norm_iteratedDeriv_le_of_ball 1 hr0 hdiff hb
    rw [iteratedDeriv_one] at this
    calc ‖dF θ w‖ ≤ (Nat.factorial 1) * M / (r / 2) ^ 1 := this
      _ = 2 * M / r := by simp; field_simp
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (mem_closedBall_self (by positivity)))
  have hderivc : ∀ θ, ‖deriv (circleMap z₀ ρ) θ‖ = ρ := by
    intro θ; rw [deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one, abs_of_pos hρ0]
  -- differentiability of the integrand
  have hdiffΦ : ∀ θ, ∀ x ∈ ball ((z₀, w₀) : ℂ × ℂ) r, HasFDerivAt (fun x => Φ x θ) (Φ' x θ) x := by
    intro θ x hx
    have hne : ζ θ - x.1 ≠ 0 := by
      intro h0; have := hsep θ x hx; rw [h0, norm_zero] at this; linarith
    have hw : ‖x.2 - w₀‖ < 2 * r := by linarith [(hball x hx).2]
    have hFw : HasDerivAt (fun w => F (ζ θ, w)) (dF θ x.2) x.2 :=
      (h2 _ (hmemU θ x.2 hw)).hasDerivAt
    have hA : HasFDerivAt (fun x : ℂ × ℂ => F (ζ θ, x.2)) (dF θ x.2 • ContinuousLinearMap.snd ℂ ℂ ℂ)
        x := hFw.comp_hasFDerivAt x (hasFDerivAt_snd (𝕜 := ℂ) (p := x))
    have hK1 : HasDerivAt (fun z : ℂ => (ζ θ - z)⁻¹) (-((ζ θ - x.1) ^ 2)⁻¹ * (-1)) x.1 :=
      (hasDerivAt_inv hne).comp x.1 ((hasDerivAt_id x.1).const_sub (ζ θ))
    have hK : HasFDerivAt (fun x : ℂ × ℂ => (ζ θ - x.1)⁻¹)
        ((-((ζ θ - x.1) ^ 2)⁻¹ * (-1)) • ContinuousLinearMap.fst ℂ ℂ ℂ) x :=
      hK1.comp_hasFDerivAt x (hasFDerivAt_fst (𝕜 := ℂ) (p := x))
    have hprod : HasFDerivAt (fun x : ℂ × ℂ => (ζ θ - x.1)⁻¹ * F (ζ θ, x.2))
        ((ζ θ - x.1)⁻¹ • (dF θ x.2 • ContinuousLinearMap.snd ℂ ℂ ℂ) +
          F (ζ θ, x.2) • ((-((ζ θ - x.1) ^ 2)⁻¹ * (-1)) • ContinuousLinearMap.fst ℂ ℂ ℂ)) x :=
      hK.mul hA
    have hfull := hprod.const_mul (deriv (circleMap z₀ ρ) θ)
    have e1 : (fun x : ℂ × ℂ => deriv (circleMap z₀ ρ) θ * ((ζ θ - x.1)⁻¹ * F (ζ θ, x.2))) =
        fun x => Φ x θ := by
      funext x; simp only [hΦ, smul_eq_mul]
    rw [e1] at hfull
    refine hfull.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp [hΦ']
    ring
  have hΦ'b : ∀ θ, ∀ x ∈ ball ((z₀, w₀) : ℂ × ℂ) r, ‖Φ' x θ‖ ≤ 12 * M / r := by
    intro θ x hx
    have hs := hsep θ x hx
    have hs0 : 0 < ‖ζ θ - x.1‖ := by linarith
    have hFb : ‖F (ζ θ, x.2)‖ ≤ M :=
      hM _ (hmemK _ _ (by rw [hζn θ, hρ]; linarith) (by linarith [(hball x hx).2]))
    have hdb := hdFb θ x.2 (hball x hx).2
    have hinv : ‖(ζ θ - x.1)⁻¹‖ ≤ 2 / r := by
      rw [norm_inv]
      rw [inv_le_comm₀ hs0 (by positivity)]
      calc (2 / r)⁻¹ = r / 2 := by rw [inv_div]
        _ ≤ ‖ζ θ - x.1‖ := hs
    have hinv2 : ‖((ζ θ - x.1) ^ 2)⁻¹‖ ≤ (2 / r) ^ 2 := by
      rw [← inv_pow, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hinv 2
    simp only [hΦ']
    calc ‖(deriv (circleMap z₀ ρ) θ * (((ζ θ - x.1) ^ 2)⁻¹ * F (ζ θ, x.2))) •
          ContinuousLinearMap.fst ℂ ℂ ℂ +
        (deriv (circleMap z₀ ρ) θ * ((ζ θ - x.1)⁻¹ * dF θ x.2)) • ContinuousLinearMap.snd ℂ ℂ ℂ‖
        ≤ ρ * ((2 / r) ^ 2 * M) * 1 + ρ * ((2 / r) * (2 * M / r)) * 1 := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, norm_mul, norm_mul, hderivc]
            exact mul_le_mul (mul_le_mul_of_nonneg_left
              (mul_le_mul hinv2 hFb (norm_nonneg _) (by positivity)) hρ0.le)
              (ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ) (norm_nonneg _) (by positivity)
          · rw [norm_smul, norm_mul, norm_mul, hderivc]
            exact mul_le_mul (mul_le_mul_of_nonneg_left
              (mul_le_mul hinv hdb (norm_nonneg _) (by positivity)) hρ0.le)
              (ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ) (norm_nonneg _) (by positivity)
      _ = 12 * M / r := by rw [hρ]; field_simp; ring
  -- continuity in `θ`
  have hFθ : ∀ w : ℂ, ‖w - w₀‖ < 2 * r → Continuous fun θ => F (ζ θ, w) := by
    intro w hw
    refine continuous_iff_continuousAt.mpr fun θ => ?_
    have hcU := (hc _ (hmemU θ w hw)).continuousAt (hU.mem_nhds (hmemU θ w hw))
    exact ContinuousAt.comp (g := F) (f := fun θ => ((ζ θ, w) : ℂ × ℂ)) hcU
      ((continuous_circleMap z₀ ρ).continuousAt.prodMk continuousAt_const)
  have hcontΦ : ∀ x ∈ ball ((z₀, w₀) : ℂ × ℂ) r, Continuous (Φ x) := by
    intro x hx
    have hw : ‖x.2 - w₀‖ < 2 * r := by linarith [(hball x hx).2]
    have hd : Continuous fun θ => deriv (circleMap z₀ ρ) θ := by
      rw [show (fun θ => deriv (circleMap z₀ ρ) θ) = fun θ => circleMap 0 ρ θ * I by
        funext θ; exact deriv_circleMap z₀ ρ θ]
      exact (continuous_circleMap 0 ρ).mul continuous_const
    have hinvc : Continuous fun θ => (ζ θ - x.1)⁻¹ := by
      refine ((continuous_circleMap z₀ ρ).sub continuous_const).inv₀ fun θ => ?_
      show ζ θ - x.1 ≠ 0
      intro h0; have := hsep θ x hx; rw [h0, norm_zero] at this; linarith
    exact hd.smul (hinvc.smul (hFθ x.2 hw))
  -- measurability of `Φ' x₀`
  have hx₀b : ((z₀, w₀) : ℂ × ℂ) ∈ ball ((z₀, w₀) : ℂ × ℂ) r := mem_ball_self hr0
  obtain ⟨hhne, hhlim⟩ := tendsto_ofReal_div_succ hr0
  have hd : Continuous fun θ => deriv (circleMap z₀ ρ) θ := by
    rw [show (fun θ => deriv (circleMap z₀ ρ) θ) = fun θ => circleMap 0 ρ θ * I by
      funext θ; exact deriv_circleMap z₀ ρ θ]
    exact (continuous_circleMap 0 ρ).mul continuous_const
  have hne0 : ∀ θ, ζ θ - z₀ ≠ 0 := by
    intro θ h0; have := hζn θ; rw [h0, norm_zero] at this; linarith
  have hinvc : Continuous fun θ => (ζ θ - z₀)⁻¹ :=
    ((continuous_circleMap z₀ ρ).sub continuous_const).inv₀ hne0
  have hinvc2 : Continuous fun θ => ((ζ θ - z₀) ^ 2)⁻¹ :=
    (((continuous_circleMap z₀ ρ).sub continuous_const).pow 2).inv₀ fun θ => pow_ne_zero 2 (hne0 θ)
  have hw0 : ‖w₀ - w₀‖ < 2 * r := by rw [sub_self, norm_zero]; linarith
  have hmeasdF : AEStronglyMeasurable (fun θ => dF θ w₀) (volume.restrict (Ι 0 (2 * Real.pi))) := by
    refine aestronglyMeasurable_deriv_param (G := fun θ w => F (ζ θ, w)) hhne hhlim
      (fun n => (hFθ _ ?_).aestronglyMeasurable) (hFθ w₀ hw0).aestronglyMeasurable
      (fun θ => h2 _ (hmemU θ w₀ hw0))
    rw [add_sub_cancel_left, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc r / ((n : ℝ) + 1) ≤ r := div_le_self hr0.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      _ < 2 * r := by linarith
  have hmeas' : AEStronglyMeasurable (Φ' (z₀, w₀)) (volume.restrict (Ι 0 (2 * Real.pi))) := by
    have hA : AEStronglyMeasurable (fun θ => deriv (circleMap z₀ ρ) θ *
        (((ζ θ - z₀) ^ 2)⁻¹ * F (ζ θ, w₀))) (volume.restrict (Ι 0 (2 * Real.pi))) :=
      (hd.mul (hinvc2.mul (hFθ w₀ hw0))).aestronglyMeasurable
    have hB : AEStronglyMeasurable (fun θ => deriv (circleMap z₀ ρ) θ *
        ((ζ θ - z₀)⁻¹ * dF θ w₀)) (volume.restrict (Ι 0 (2 * Real.pi))) :=
      hd.aestronglyMeasurable.mul (hinvc.aestronglyMeasurable.mul hmeasdF)
    exact (hA.smul_const _).add (hB.smul_const _)
  have hmain := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (a := 0) (b := 2 * Real.pi) (bound := fun _ => 12 * M / r) (F := Φ) (F' := Φ')
    (x₀ := ((z₀, w₀) : ℂ × ℂ)) (ball_mem_nhds _ hr0)
    (Filter.eventually_of_mem (ball_mem_nhds _ hr0) fun x hx =>
      (hcontΦ x hx).aestronglyMeasurable)
    ((hcontΦ _ hx₀b).intervalIntegrable 0 (2 * Real.pi)) hmeas'
    (Eventually.of_forall fun θ _ x hx => hΦ'b θ x hx) intervalIntegrable_const
    (Eventually.of_forall fun θ _ x hx => hdiffΦ θ x hx)
  have e : G = fun x => (2 * Real.pi * I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, Φ x θ := by
    funext x; rfl
  rw [e]
  exact hmain.differentiableAt.const_smul ((2 * Real.pi * I : ℂ)⁻¹)


/-- For `F` jointly holomorphic on an open `U ⊆ ℂ²`, the partial derivative in the first
variable at a fixed `z₀` is continuous in the second variable. -/
theorem continuousAt_deriv_fst {U : Set (ℂ × ℂ)} (hU : IsOpen U) {F : ℂ × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {z₀ w₀ : ℂ} (hx₀ : ((z₀, w₀) : ℂ × ℂ) ∈ U) :
    ContinuousAt (fun w => deriv (fun z => F (z, w)) z₀) w₀ := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU _ hx₀
  set r : ℝ := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hK : closedBall ((z₀, w₀) : ℂ × ℂ) (2 * r) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨M, hM⟩ := (isCompact_closedBall ((z₀, w₀) : ℂ × ℂ) (2 * r)).exists_bound_of_continuousOn
    (hF.continuousOn.mono hK)
  have hmemK : ∀ z w : ℂ, ‖z - z₀‖ ≤ 2 * r → ‖w - w₀‖ ≤ 2 * r →
      ((z, w) : ℂ × ℂ) ∈ closedBall ((z₀, w₀) : ℂ × ℂ) (2 * r) := by
    intro z w hz hw
    rw [mem_closedBall, Prod.dist_eq, max_le_iff, dist_eq_norm, dist_eq_norm]
    exact ⟨hz, hw⟩
  -- Cauchy formula for the derivative, uniformly for `w` near `w₀`
  set I₀ : ℂ → ℂ := fun w => ∮ z in C(z₀, r), (1 / (z - z₀) ^ 2) • F (z, w) with hI₀
  have hrep : ∀ w : ℂ, ‖w - w₀‖ < r →
      deriv (fun z => F (z, w)) z₀ = (2 * Real.pi * I : ℂ)⁻¹ * I₀ w := by
    intro w hw
    have hdiff : DifferentiableOn ℂ (fun z => F (z, w)) (ball z₀ (2 * r)) := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      have hmem := hK (hmemK z w hz.le (by linarith))
      have h1 := (hF _ hmem).differentiableAt (hU.mem_nhds hmem)
      exact (DifferentiableAt.fun_comp' (g := F) (f := fun z : ℂ => ((z, w) : ℂ × ℂ)) z h1
        (differentiableAt_id.prodMk (differentiableAt_const _))).differentiableWithinAt
    have hdc := hdiff.diffContOnCl_ball (c := z₀) (R := r) (closedBall_subset_ball (by linarith))
    have h := hdc.deriv_eq_smul_circleIntegral hr0
    rw [hI₀]
    simp only at h ⊢
    rw [h, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  have hev : (fun w => deriv (fun z => F (z, w)) z₀) =ᶠ[𝓝 w₀]
      fun w => (2 * Real.pi * I : ℂ)⁻¹ * I₀ w := by
    filter_upwards [Metric.ball_mem_nhds w₀ hr0] with w hw
    rw [mem_ball, dist_eq_norm] at hw
    exact hrep w hw
  refine ContinuousAt.congr ?_ hev.symm
  refine ContinuousAt.mul continuousAt_const ?_
  -- continuity of the circle integral in `w`
  have hcirc : ∀ θ : ℝ, ‖circleMap z₀ r θ - z₀‖ = r := by
    intro θ; rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr0]
  have hcF : ∀ θ : ℝ, ∀ w : ℂ, ‖w - w₀‖ < r → ContinuousAt (fun w => F (circleMap z₀ r θ, w)) w := by
    intro θ w hw
    have hmem := hK (hmemK _ w (by rw [hcirc θ]; linarith) (by linarith))
    have h1 := (hF _ hmem).differentiableAt (hU.mem_nhds hmem)
    exact (DifferentiableAt.fun_comp' (g := F) (f := fun w : ℂ => ((circleMap z₀ r θ, w) : ℂ × ℂ)) w
      h1 ((differentiableAt_const _).prodMk differentiableAt_id)).continuousAt
  have hcθ : ∀ w : ℂ, ‖w - w₀‖ < r → Continuous fun θ => F (circleMap z₀ r θ, w) := by
    intro w hw
    refine continuous_iff_continuousAt.mpr fun θ => ?_
    have hmem := hK (hmemK _ w (by rw [hcirc θ]; linarith) (by linarith))
    have h1 := (hF _ hmem).differentiableAt (hU.mem_nhds hmem)
    exact ContinuousAt.comp (g := F) (f := fun θ => ((circleMap z₀ r θ, w) : ℂ × ℂ))
      h1.continuousAt ((continuous_circleMap z₀ r).continuousAt.prodMk continuousAt_const)
  have hd : Continuous fun θ => deriv (circleMap z₀ r) θ := by
    rw [show (fun θ => deriv (circleMap z₀ r) θ) = fun θ => circleMap 0 r θ * I by
      funext θ; exact deriv_circleMap z₀ r θ]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hne : ∀ θ, circleMap z₀ r θ - z₀ ≠ 0 := by
    intro θ h0; have := hcirc θ; rw [h0, norm_zero] at this; linarith
  have hk : Continuous fun θ => 1 / (circleMap z₀ r θ - z₀) ^ 2 :=
    continuous_const.div (((continuous_circleMap z₀ r).sub continuous_const).pow 2)
      fun θ => pow_ne_zero 2 (hne θ)
  have e : I₀ = fun w => ∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap z₀ r) θ • ((1 / (circleMap z₀ r θ - z₀) ^ 2) • F (circleMap z₀ r θ, w)) := by
    funext w; rfl
  rw [e]
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => r * (r ^ 2)⁻¹ * M)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds w₀ hr0) fun w hw => ?_)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds w₀ hr0) fun w hw => ?_)
    intervalIntegrable_const (Eventually.of_forall fun θ _ => ?_)
  · rw [mem_ball, dist_eq_norm] at hw
    exact (hd.smul (hk.smul (hcθ w hw))).aestronglyMeasurable
  · rw [mem_ball, dist_eq_norm] at hw
    refine Eventually.of_forall fun θ _ => ?_
    have hFb : ‖F (circleMap z₀ r θ, w)‖ ≤ M :=
      hM _ (hmemK _ w (by rw [hcirc θ]; linarith) (by linarith))
    rw [norm_smul, norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one,
      abs_of_pos hr0, norm_div, norm_one, norm_pow, hcirc θ, one_div]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFb (by positivity)) hr0.le
      |>.trans_eq (by ring)
  · have h3 := hcF θ w₀ (by simpa using hr0)
    exact (continuousAt_const (y := deriv (circleMap z₀ r) θ)).smul
      ((continuousAt_const (y := 1 / (circleMap z₀ r θ - z₀) ^ 2)).smul h3)

end PGM
