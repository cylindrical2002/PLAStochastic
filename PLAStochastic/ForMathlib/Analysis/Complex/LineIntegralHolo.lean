import PLAStochastic.ForMathlib.Analysis.Complex.Osgood
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Holomorphy of Cauchy-type line integrals with a holomorphic parameter

`differentiableOn_lineIntegral_param`: `(ζ, q) ↦ ∫ G(y, q)/(c + i y - ζ) dy` is holomorphic on
`{Re ζ < c} × B(0, R)` if every `G(y, ·)` is holomorphic on `B(0, R)` and bounded there by `B(y)`,
`y ↦ G(y, q)` is measurable, and `B(y)/|c + i y - ζ|` is integrable for every `Re ζ < c`.
-/

noncomputable section

open MeasureTheory Set Metric Complex Filter Topology

namespace PGM

theorem differentiableOn_lineIntegral_param {c R : ℝ} {G : ℝ → ℂ → ℂ} {B : ℝ → ℝ}
    (hd : ∀ y, DifferentiableOn ℂ (G y) (ball 0 R))
    (hb : ∀ y, ∀ q ∈ ball (0 : ℂ) R, ‖G y q‖ ≤ B y)
    (hm : ∀ q ∈ ball (0 : ℂ) R, AEStronglyMeasurable (fun y => G y q) volume)
    (hi : ∀ ζ : ℂ, ζ.re < c → Integrable (fun y : ℝ => B y / ‖(c : ℂ) + y * I - ζ‖)) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => ∫ y : ℝ, G y x.2 / ((c : ℂ) + y * I - x.1))
      {x : ℂ × ℂ | x.1.re < c ∧ ‖x.2‖ < R} := by
  rintro ⟨ζ₀, q₀⟩ ⟨hζ₀, hq₀⟩
  simp only at hζ₀ hq₀
  have hsre : ∀ y : ℝ, ((c : ℂ) + y * I).re = c := by intro y; simp
  set δ : ℝ := min ((c - ζ₀.re) / 2) ((R - ‖q₀‖) / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ (c - ζ₀.re) / 2 := min_le_left _ _
  have hδ2 : δ ≤ (R - ‖q₀‖) / 4 := min_le_right _ _
  set x₀ : ℂ × ℂ := (ζ₀, q₀) with hx₀
  set g : ℂ × ℂ → ℝ → ℂ := fun x y => G y x.2 / ((c : ℂ) + y * I - x.1) with hg
  set g' : ℂ × ℂ → ℝ → ℂ × ℂ →L[ℂ] ℂ := fun x y =>
    (G y x.2 / ((c : ℂ) + y * I - x.1) ^ 2) • ContinuousLinearMap.fst ℂ ℂ ℂ +
      (deriv (G y) x.2 / ((c : ℂ) + y * I - x.1)) • ContinuousLinearMap.snd ℂ ℂ ℂ with hg'
  have hball : ∀ x ∈ ball x₀ δ, x.1.re < c - δ ∧ ‖x.2‖ < R - 3 * δ ∧ ‖x.1 - ζ₀‖ < δ := by
    intro x hx
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hx
    refine ⟨?_, ?_, hx.1⟩
    · have := (re_le_norm (x.1 - ζ₀)).trans_lt hx.1; rw [sub_re] at this; linarith
    · have := norm_sub_norm_le x.2 q₀; linarith [hx.2]
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg q₀) hq₀
  have hB0 : ∀ y, 0 ≤ B y := fun y =>
    (norm_nonneg _).trans (hb y 0 (mem_ball_self hR))
  have hGd' : ∀ (y : ℝ) (q : ℂ), ‖q‖ < R - 2 * δ → ‖deriv (G y) q‖ ≤ B y / δ := by
    intro y q hq
    have hsub : ball q (2 * δ) ⊆ ball (0 : ℂ) R := by
      intro q' hq'
      rw [mem_ball, dist_eq_norm] at hq'
      rw [mem_ball, dist_zero_right]
      have := norm_sub_norm_le q' q; linarith
    have := norm_iteratedDeriv_le_of_ball 1 (by positivity) ((hd y).mono hsub)
      (fun q' hq' => hb y q' (hsub hq'))
    rw [iteratedDeriv_one] at this
    calc ‖deriv (G y) q‖ ≤ (Nat.factorial 1) * B y / (2 * δ / 2) ^ 1 := this
      _ = B y / δ := by simp
  have hGdiff : ∀ (y : ℝ) (q : ℂ), ‖q‖ < R → DifferentiableAt ℂ (G y) q := fun y q hq =>
    (hd y q (by rw [mem_ball, dist_zero_right]; exact hq)).differentiableAt
      (isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; exact hq))
  set bound : ℝ → ℝ := fun y => 4 / δ * (B y / ‖(c : ℂ) + y * I - ζ₀‖) with hbound
  have hlow : ∀ (y : ℝ), 2 * δ ≤ ‖(c : ℂ) + y * I - ζ₀‖ := by
    intro y
    have := re_le_norm ((c : ℂ) + y * I - ζ₀)
    rw [sub_re, hsre] at this; linarith
  have hlow2 : ∀ (y : ℝ) (x : ℂ × ℂ), x ∈ ball x₀ δ →
      ‖(c : ℂ) + y * I - ζ₀‖ / 2 ≤ ‖(c : ℂ) + y * I - x.1‖ := by
    intro y x hx
    have h1 := (hball x hx).2.2
    have h2 := hlow y
    have : ‖(c : ℂ) + y * I - ζ₀‖ ≤ ‖(c : ℂ) + y * I - x.1‖ + ‖x.1 - ζ₀‖ := by
      calc ‖(c : ℂ) + y * I - ζ₀‖ = ‖((c : ℂ) + y * I - x.1) + (x.1 - ζ₀)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  have hlow3 : ∀ (y : ℝ) (x : ℂ × ℂ), x ∈ ball x₀ δ → δ ≤ ‖(c : ℂ) + y * I - x.1‖ := by
    intro y x hx
    have h1 := (hball x hx).1
    have := re_le_norm ((c : ℂ) + y * I - x.1)
    rw [sub_re, hsre] at this; linarith
  have hderiv : ∀ y, ∀ x ∈ ball x₀ δ, HasFDerivAt (fun x => g x y) (g' x y) x := by
    intro y x hx
    obtain ⟨h1, h2, -⟩ := hball x hx
    have hne : (c : ℂ) + y * I - x.1 ≠ 0 := by
      intro h0; have := congrArg re h0; rw [sub_re, hsre, zero_re] at this; linarith
    have hGx : HasDerivAt (G y) (deriv (G y) x.2) x.2 :=
      (hGdiff y x.2 (by linarith)).hasDerivAt
    have hA : HasFDerivAt (fun x : ℂ × ℂ => G y x.2)
        ((deriv (G y) x.2) • ContinuousLinearMap.snd ℂ ℂ ℂ) x :=
      hGx.comp_hasFDerivAt x (hasFDerivAt_snd (p := x))
    have hK : HasFDerivAt (fun x : ℂ × ℂ => ((c : ℂ) + y * I - x.1)⁻¹)
        ((((c : ℂ) + y * I - x.1) ^ 2)⁻¹ • ContinuousLinearMap.fst ℂ ℂ ℂ) x := by
      have h1 : HasDerivAt (fun z : ℂ => ((c : ℂ) + y * I - z)⁻¹)
          (-(((c : ℂ) + y * I - x.1) ^ 2)⁻¹ * (-1)) x.1 :=
        (hasDerivAt_inv hne).comp x.1 ((hasDerivAt_id x.1).const_sub ((c : ℂ) + y * I))
      have h2 := h1.comp_hasFDerivAt x (hasFDerivAt_fst (𝕜 := ℂ) (p := x))
      rw [show -(((c : ℂ) + y * I - x.1) ^ 2)⁻¹ * (-1) = (((c : ℂ) + y * I - x.1) ^ 2)⁻¹ by ring]
        at h2
      exact h2
    have hprod : HasFDerivAt (fun x : ℂ × ℂ => G y x.2 * ((c : ℂ) + y * I - x.1)⁻¹)
        (G y x.2 • ((((c : ℂ) + y * I - x.1) ^ 2)⁻¹ • ContinuousLinearMap.fst ℂ ℂ ℂ) +
          ((c : ℂ) + y * I - x.1)⁻¹ • ((deriv (G y) x.2) • ContinuousLinearMap.snd ℂ ℂ ℂ)) x :=
      hA.mul hK
    have e1 : (fun x : ℂ × ℂ => G y x.2 * ((c : ℂ) + y * I - x.1)⁻¹) = fun x => g x y := by
      funext x; simp only [hg, div_eq_mul_inv]
    rw [e1] at hprod
    convert hprod using 1
    refine ContinuousLinearMap.ext fun v => ?_
    simp [hg', div_eq_mul_inv]
    ring
  have hderiv_bound : ∀ y, ∀ x ∈ ball x₀ δ, ‖g' x y‖ ≤ bound y := by
    intro y x hx
    obtain ⟨h1, h2, h3⟩ := hball x hx
    have hl := hlow2 y x hx
    have hl0 := hlow y
    have hl3 := hlow3 y x hx
    set b := 1 / ‖(c : ℂ) + y * I - ζ₀‖ with hb'
    set w := ‖(c : ℂ) + y * I - x.1‖ with hw
    have hw0 : 0 < w := lt_of_lt_of_le hδ0 hl3
    have hb0 : 0 ≤ b := by positivity
    have hinv : 1 / w ≤ 2 * b := by
      have h00 : 0 < ‖(c : ℂ) + y * I - ζ₀‖ := by linarith
      calc 1 / w ≤ 1 / (‖(c : ℂ) + y * I - ζ₀‖ / 2) :=
            one_div_le_one_div_of_le (by positivity) hl
        _ = 2 * b := by rw [hb']; field_simp
    have hinvδ : 1 / w ≤ 1 / δ := one_div_le_one_div_of_le hδ0 hl3
    have hG1 : ‖G y x.2‖ ≤ B y := hb y x.2 (by rw [mem_ball, dist_zero_right]; linarith)
    have hG2 := hGd' y x.2 (by linarith)
    have hBy := hB0 y
    have hnorm : ‖g' x y‖ ≤ ‖G y x.2‖ / w ^ 2 + ‖deriv (G y) x.2‖ / w := by
      simp only [hg']
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, norm_div, norm_pow, ← hw]
        exact mul_le_of_le_one_right (by positivity) (ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ)
      · rw [norm_smul, norm_div, ← hw]
        exact mul_le_of_le_one_right (by positivity) (ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ)
    have t1 : ‖G y x.2‖ / w ^ 2 ≤ B y * (2 * b) * (1 / δ) := by
      rw [div_eq_mul_one_div, show 1 / w ^ 2 = (1 / w) * (1 / w) by ring]
      have : 1 / w * (1 / w) ≤ 2 * b * (1 / δ) :=
        mul_le_mul hinv hinvδ (by positivity) (by positivity)
      calc ‖G y x.2‖ * (1 / w * (1 / w)) ≤ B y * (2 * b * (1 / δ)) :=
            mul_le_mul hG1 this (by positivity) hBy
        _ = _ := by ring
    have t2 : ‖deriv (G y) x.2‖ / w ≤ B y * (2 * b) * (1 / δ) := by
      rw [div_eq_mul_one_div]
      calc ‖deriv (G y) x.2‖ * (1 / w) ≤ B y / δ * (2 * b) :=
            mul_le_mul hG2 hinv (by positivity) (by positivity)
        _ = _ := by ring
    calc ‖g' x y‖ ≤ _ := hnorm
      _ ≤ B y * (2 * b) * (1 / δ) + B y * (2 * b) * (1 / δ) := add_le_add t1 t2
      _ = bound y := by simp only [hbound, hb']; ring
  -- measurability
  have hden : Continuous fun y : ℝ => (c : ℂ) + y * I - ζ₀ := by fun_prop
  have hden0 : ∀ y : ℝ, (c : ℂ) + y * I - ζ₀ ≠ 0 := by
    intro y h0; have := hlow y; rw [h0, norm_zero] at this; linarith
  have hq₀m : q₀ ∈ ball (0 : ℂ) R := by rw [mem_ball, dist_zero_right]; exact hq₀
  have hmeasA : AEStronglyMeasurable (fun y : ℝ =>
      G y q₀ / ((c : ℂ) + y * I - ζ₀) ^ 2) volume :=
    ((hm q₀ hq₀m).mul ((hden.pow 2).inv₀ fun y => pow_ne_zero 2 (hden0 y)).aestronglyMeasurable)
      |>.congr (Eventually.of_forall fun y => by simp [div_eq_mul_inv])
  have hmeasD : AEStronglyMeasurable (fun y : ℝ => deriv (G y) q₀) volume := by
    obtain ⟨hne, hlim⟩ := tendsto_ofReal_div_succ hδ0
    refine aestronglyMeasurable_deriv_param (G := G) hne hlim (fun n => hm _ ?_) (hm q₀ hq₀m)
      (fun y => hGdiff y q₀ hq₀)
    have hn : ‖((δ / (n + 1) : ℝ) : ℂ)‖ ≤ δ := by
      rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact div_le_self hδ0.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    rw [mem_ball, dist_zero_right]
    calc ‖q₀ + ((δ / (n + 1) : ℝ) : ℂ)‖ ≤ ‖q₀‖ + δ := (norm_add_le _ _).trans (by linarith)
      _ < R := by linarith
  have hmeasB : AEStronglyMeasurable (fun y : ℝ =>
      deriv (G y) q₀ / ((c : ℂ) + y * I - ζ₀)) volume :=
    hmeasD.mul ((hden.inv₀ hden0).aestronglyMeasurable) |>.congr (Eventually.of_forall
      fun y => by simp [div_eq_mul_inv])
  have hmeas' : AEStronglyMeasurable (g' x₀) volume :=
    (hmeasA.smul_const (ContinuousLinearMap.fst ℂ ℂ ℂ)).add
      (hmeasB.smul_const (ContinuousLinearMap.snd ℂ ℂ ℂ))
  have hmeasg : ∀ x ∈ ball x₀ δ, AEStronglyMeasurable (g x) volume := by
    intro x hx
    obtain ⟨h1, h2, -⟩ := hball x hx
    have hx2 : x.2 ∈ ball (0 : ℂ) R := by rw [mem_ball, dist_zero_right]; linarith
    have hd1 : Continuous fun y : ℝ => ((c : ℂ) + y * I - x.1)⁻¹ := by
      refine Continuous.inv₀ (by fun_prop) fun y h0 => ?_
      have := congrArg re h0; rw [sub_re, hsre, zero_re] at this; linarith
    exact ((hm x.2 hx2).mul hd1.aestronglyMeasurable).congr
      (Eventually.of_forall fun y => by simp [hg, div_eq_mul_inv])
  have hint : Integrable (g x₀) volume := by
    refine (hi ζ₀ hζ₀).mono' (hmeasg x₀ (mem_ball_self hδ0)) (Eventually.of_forall fun y => ?_)
    simp only [hg, hx₀]
    rw [norm_div]
    exact div_le_div_of_nonneg_right (hb y q₀ hq₀m) (norm_nonneg _)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := g) (F' := g')
    (bound := bound) (x₀ := x₀) (ball_mem_nhds x₀ hδ0)
    (Filter.eventually_of_mem (ball_mem_nhds x₀ hδ0) hmeasg) hint hmeas'
    (Eventually.of_forall fun y x hx => hderiv_bound y x hx) ((hi ζ₀ hζ₀).const_mul _)
    (Eventually.of_forall fun y x hx => hderiv y x hx)
  exact hmain.differentiableAt.differentiableWithinAt

end PGM
