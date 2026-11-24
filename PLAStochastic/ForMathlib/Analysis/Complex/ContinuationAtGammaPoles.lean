import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Continuation off a countable set and limits at the poles of `Γ(-q)`

Two tools for evaluating a Mellin identity at the nonnegative integers:

* a function holomorphic off a countable closed set that agrees with an entire
  function on a nonempty open set agrees with it off that set;
* at a positive integer `n`, `Γ(-q) H(q) → (-1)^(n+1) / n! · H'(n)` when `H(n) = 0`.
-/

open Complex Filter Set Topology

namespace BrownianAffine

/-- Identity principle off a countable closed set: the complement is open and connected. -/
theorem eqOn_compl_of_countable_closed {F G : ℂ → ℂ} {C V : Set ℂ} (hC : C.Countable)
    (hCc : IsClosed C) (hF : DifferentiableOn ℂ F Cᶜ) (hG : Differentiable ℂ G)
    (hV : IsOpen V) (hVne : V.Nonempty) (hVC : V ⊆ Cᶜ) (hFG : EqOn F G V) :
    EqOn F G Cᶜ := by
  have hU : IsOpen Cᶜ := hCc.isOpen_compl
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hconn : IsPreconnected Cᶜ := (hC.isConnected_compl_of_one_lt_rank hrank).isPreconnected
  obtain ⟨z₀, hz₀⟩ := hVne
  exact (hF.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (hG.differentiableOn.analyticOnNhd hU) hconn (hVC hz₀)
    (Filter.eventuallyEq_of_mem (hV.mem_nhds hz₀) hFG)

/-- `(s + n) Γ(s) = Γ(s + n + 1) / ∏_{k<n} (s + k)` away from the poles. -/
theorem Gamma_mul_eq_div_prod {s : ℂ} (n : ℕ) (hs : ∀ m : ℕ, s ≠ -m) :
    (s + n) * Gamma s = Gamma (s + n + 1) / ∏ k ∈ Finset.range n, (s + k) := by
  have hprod : ∀ N : ℕ, Gamma (s + N) = Gamma s * ∏ k ∈ Finset.range N, (s + k) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hne : s + N ≠ 0 := by
        intro h
        exact hs N (by linear_combination h)
      rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hne, ih]
      ring
  have hnz : ∏ k ∈ Finset.range n, (s + k) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k _ h
    exact hs k (by linear_combination h)
  have hn : s + n ≠ 0 := by
    intro h
    exact hs n (by linear_combination h)
  rw [eq_div_iff hnz, show s + n + 1 = (s + n) + 1 by ring, Complex.Gamma_add_one _ hn, hprod n]
  ring

/-- The residue of `Γ` at `-n`: `(s + n) Γ(s) → (-1)^n / n!`. -/
theorem tendsto_add_nat_mul_Gamma (n : ℕ) :
    Tendsto (fun s : ℂ => (s + n) * Gamma s) (𝓝[≠] (-(n : ℂ))) (𝓝 ((-1) ^ n / n.factorial)) := by
  have hpoles : ∀ᶠ s : ℂ in 𝓝[≠] (-(n : ℂ)), ∀ m : ℕ, s ≠ -(m : ℂ) := by
    have hdisc : ∀ᶠ s : ℂ in 𝓝 (-(n : ℂ)), ∀ m : ℕ, m ≠ n → s ≠ -(m : ℂ) := by
      have hball : Metric.ball (-(n : ℂ)) 1 ∈ 𝓝 (-(n : ℂ)) := Metric.ball_mem_nhds _ one_pos
      filter_upwards [hball] with s hsball m hm hsm
      rw [hsm, Metric.mem_ball, dist_eq_norm, show -(m : ℂ) - -(n : ℂ) = ((n : ℤ) - m : ℤ) by
        push_cast; ring, Complex.norm_intCast] at hsball
      have hne : ((n : ℤ) - m) ≠ 0 := by omega
      have h1 : (1 : ℝ) ≤ |(((n : ℤ) - m : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hne
      linarith
    filter_upwards [nhdsWithin_le_nhds hdisc, self_mem_nhdsWithin] with s hs hsn m
    by_cases hm : m = n
    · subst hm
      exact hsn
    · exact hs m hm
  have hcont : ContinuousAt (fun s : ℂ => Gamma (s + n + 1) / ∏ k ∈ Finset.range n, (s + k))
      (-(n : ℂ)) := by
    have hG : ContinuousAt (fun s : ℂ => Gamma (s + n + 1)) (-(n : ℂ)) := by
      have hd : DifferentiableAt ℂ Gamma ((fun s : ℂ => s + n + 1) (-(n : ℂ))) := by
        show DifferentiableAt ℂ Gamma (-(n : ℂ) + n + 1)
        rw [show -(n : ℂ) + n + 1 = 1 by ring]
        exact differentiableAt_Gamma_one
      exact hd.continuousAt.comp (f := fun s : ℂ => s + n + 1) (by fun_prop)
    have hP : ContinuousAt (fun s : ℂ => ∏ k ∈ Finset.range n, (s + k)) (-(n : ℂ)) := by
      fun_prop
    refine hG.div hP ?_
    rw [Finset.prod_ne_zero_iff]
    intro k hk h
    have : (k : ℂ) = n := by linear_combination h
    have : k = n := by exact_mod_cast this
    simp [this] at hk
  have hval : Gamma (-(n : ℂ) + n + 1) / ∏ k ∈ Finset.range n, (-(n : ℂ) + k) =
      (-1) ^ n / n.factorial := by
    rw [show -(n : ℂ) + n + 1 = 1 by ring, Complex.Gamma_one]
    have hp : ∏ k ∈ Finset.range n, (-(n : ℂ) + k) = (-1) ^ n * n.factorial := by
      have hfact : (n.factorial : ℂ) = ∏ k ∈ Finset.range n, ((k : ℂ) + 1) := by
        rw [← Finset.prod_range_add_one_eq_factorial]
        push_cast
        rfl
      rw [hfact, ← Finset.prod_range_reflect]
      have hterm : ∀ j ∈ Finset.range n, (-(n : ℂ) + ((n - 1 - j : ℕ) : ℂ)) = (-1) * ((j : ℂ) + 1) := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [hp]
    have hsq : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    field_simp
    rw [hsq]
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {(-(n : ℂ))}ᶜ))
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hpoles] with s hs
  exact (Gamma_mul_eq_div_prod n hs).symm

/-- At a natural number `n`, `(q - n) Γ(-q) → (-1)^(n+1) / n!`. -/
theorem tendsto_sub_nat_mul_Gamma_neg (n : ℕ) :
    Tendsto (fun q : ℂ => (q - n) * Gamma (-q)) (𝓝[≠] (n : ℂ))
      (𝓝 ((-1) ^ (n + 1) / n.factorial)) := by
  have hneg : Tendsto (fun q : ℂ => -q) (𝓝[≠] (n : ℂ)) (𝓝[≠] (-(n : ℂ))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (continuous_neg.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq h
      exact hq (by simpa using h)
  have h := ((tendsto_add_nat_mul_Gamma n).comp hneg).neg
  rw [show -((-1 : ℂ) ^ n / n.factorial) = (-1) ^ (n + 1) / n.factorial by ring] at h
  refine h.congr' (Eventually.of_forall fun q => ?_)
  simp only [Function.comp]
  ring

/-- If `H` is differentiable at the natural number `n` with `H n = 0`, then
`Γ(-q) H(q) → (-1)^(n+1) / n! · H'(n)` as `q → n`. -/
theorem tendsto_Gamma_neg_mul_of_zero {H : ℂ → ℂ} {n : ℕ} (hH : DifferentiableAt ℂ H n)
    (h0 : H n = 0) :
    Tendsto (fun q : ℂ => Gamma (-q) * H q) (𝓝[≠] (n : ℂ))
      (𝓝 ((-1) ^ (n + 1) / n.factorial * deriv H n)) := by
  have hslope := hH.hasDerivAt.tendsto_slope
  have hs : Tendsto (fun q : ℂ => (q - n)⁻¹ * H q) (𝓝[≠] (n : ℂ)) (𝓝 (deriv H n)) := by
    refine hslope.congr' (Eventually.of_forall fun q => ?_)
    simp [slope_def_field, h0, div_eq_inv_mul]
  refine ((tendsto_sub_nat_mul_Gamma_neg n).mul hs).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq' : q - n ≠ 0 := sub_ne_zero.mpr hq
  field_simp

end BrownianAffine
