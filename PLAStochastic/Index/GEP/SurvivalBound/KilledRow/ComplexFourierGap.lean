import PLAStochastic.Index.GEP.OrbitClosure.SumDensity
import PLAStochastic.Index.GEP.OrbitClosure.RegularClass
import PLAStochastic.Index.GEP.DirectTerm.Defs

/-!
# WP4 `SurvivalBound`: the class-level complex Fourier gap

Source: `research/2026-09-28-gep-closure/analytic-response-tools.md` §1 (命题 1);
`rawdisc-design.md` §2.3.

For the regular class `RegLaw D θ vlo vhi` there is `c > 0` such that for every direction class
`SigmaLaw A θσ` (`θσ > 0`) there is a radius `r > 0` with: `‖z‖ < r`, `a ∈ [1/2, 2]` give

`‖(1 - z) φ_ν(a t) + z φ_σ(a t)‖² ≤ 1 - c min(t², 1)` for all `t`   (`kill_complex_charFun_gap`).

Proof.  Write `m = φ_ν + z (φ_σ - φ_ν)` at `s = a t`.
* `ν`-gap (`one_sub_norm_charFun_sq_ge`, `lem:charfn`): with `LocBd D` (`RegLaw.envBd.locBd`) and
  variance `v ∈ [vlo, vhi]`, `1 - |φ_ν(s)|² ≥ c₀ min(1, s² v)/(D² v) ≥ c_ν min(t², 1)`,
  `c_ν = c₀ min(1, vlo)/(4 D² vhi)` (`a ≥ 1/2`).
* Both means are one, so `|φ_σ(s) - φ_ν(s)| ≤ (s²/2)(m₂(σ) + m₂(ν))`
  (`‖e^{iu} - 1 - iu‖ ≤ u²/2`, `kill_norm_cexp_sub_one_sub_le`); `m₂(ν) = var + 1 ≤ vhi + 1` and
  `m₂(σ) ≤ 2A/θσ²` (`x² ≤ 2e^{θσ x}/θσ²` on `x ≥ 0`).  Hence `δ = |φ_σ - φ_ν| ≤ 2L min(t², 1)`
  with `L = max(1, 2A/θσ² + vhi + 1)` (`a ≤ 2`, and `δ ≤ 2`).
* `|m|² ≤ (|φ_ν| + |z| δ)² ≤ |φ_ν|² + 4|z|δ ≤ 1 - c_ν μ + 8 r L μ`; take `r = min(1, c_ν/(16L))`
  and `c = min(c_ν/2, 1)`.  The constant `c` does not depend on `(A, θσ)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal Real

/-- `‖e^{is} - 1 - is‖ ≤ s²/2` for `s ≥ 0`. -/
theorem kill_norm_cexp_sub_one_sub_le_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    ‖cexp (s * I) - 1 - s * I‖ ≤ s ^ 2 / 2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (x * I) - 1 - x * I)
      (cexp (x * I) * I - I) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * I) I x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).mul_const I
    have h2 : HasDerivAt (fun x : ℝ => cexp (x * I)) (cexp (x * I) * I) x := h1.cexp
    exact (h2.sub_const 1).sub h1
  have hB : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
    intro x
    simpa using ((hasDerivAt_pow 2 x).div_const 2)
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := s)
    (f := fun x : ℝ => cexp (x * I) - 1 - x * I) (f' := fun x => cexp (x * I) * I - I)
    (B := fun x : ℝ => x ^ 2 / 2) (B' := fun x => x) ?_ ?_ ?_ hB ?_ ⟨hs, le_rfl⟩
  · exact fun x _ => (hd x).continuousAt.continuousWithinAt
  · exact fun x _ => (hd x).hasDerivWithinAt
  · simp
  · intro x hx
    have hx0 : 0 ≤ x := hx.1
    have : cexp (x * I) * I - I = I * (cexp (I * x) - 1) := by ring_nf
    rw [this, norm_mul, Complex.norm_I, one_mul]
    calc ‖cexp (I * x) - 1‖ ≤ ‖x‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = x := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]

/-- **Second-order bound for `e^{iu}`**: `‖e^{iu} - 1 - iu‖ ≤ u²/2`. -/
theorem kill_norm_cexp_sub_one_sub_le (u : ℝ) : ‖cexp (u * I) - 1 - u * I‖ ≤ u ^ 2 / 2 := by
  rcases le_total 0 u with hu | hu
  · exact kill_norm_cexp_sub_one_sub_le_of_nonneg hu
  · have h := kill_norm_cexp_sub_one_sub_le_of_nonneg (neg_nonneg.2 hu)
    have hc : cexp (((-u : ℝ) : ℂ) * I) - 1 - ((-u : ℝ) : ℂ) * I =
        (starRingEnd ℂ) (cexp (u * I) - 1 - u * I) := by
      simp only [map_sub, map_mul, map_one, Complex.conj_ofReal, Complex.conj_I,
        ← Complex.exp_conj]
      push_cast
      ring_nf
    rw [hc, Complex.norm_conj, neg_sq] at h
    exact h

/-- **Characteristic function to second order.**  For a probability measure with finite second
moment, `‖φ_μ(s) - (1 + i s E X)‖ ≤ (s²/2) E X²`. -/
theorem kill_norm_charFun_sub_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ) (h2 : Integrable (fun x : ℝ => x ^ 2) μ) (s : ℝ) :
    ‖charFun μ s - (1 + ((s * ∫ x, x ∂μ : ℝ) : ℂ) * I)‖ ≤ s ^ 2 / 2 * ∫ x, x ^ 2 ∂μ := by
  have hE : Integrable (fun x : ℝ => cexp ((s * x : ℝ) * I)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have hL : Integrable (fun x : ℝ => (1 : ℂ) + ((s * x : ℝ) : ℂ) * I) μ :=
    (integrable_const _).add ((h1.const_mul s).ofReal.mul_const I)
  have hL2 : Integrable (fun x : ℝ => ((s * x : ℝ) : ℂ) * I) μ :=
    (h1.const_mul s).ofReal.mul_const I
  have hlin : ∫ x, ((1 : ℂ) + ((s * x : ℝ) : ℂ) * I) ∂μ = 1 + ((s * ∫ x, x ∂μ : ℝ) : ℂ) * I := by
    rw [integral_add (integrable_const _) hL2, integral_const,
      probReal_univ, one_smul, integral_mul_const, integral_complex_ofReal, integral_const_mul]
  have hcf : charFun μ s = ∫ x, cexp ((s * x : ℝ) * I) ∂μ := by
    rw [charFun_apply_real]
    congr 1; funext x; push_cast; ring_nf
  rw [hcf, ← hlin, ← integral_sub hE hL]
  calc ‖∫ x, (cexp ((s * x : ℝ) * I) - (1 + ((s * x : ℝ) : ℂ) * I)) ∂μ‖
      ≤ ∫ x, ‖cexp ((s * x : ℝ) * I) - (1 + ((s * x : ℝ) : ℂ) * I)‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x, s ^ 2 / 2 * x ^ 2 ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
          (h2.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
        have h := kill_norm_cexp_sub_one_sub_le (s * x)
        simp only
        rw [sub_add_eq_sub_sub]
        calc _ ≤ (s * x) ^ 2 / 2 := h
          _ = s ^ 2 / 2 * x ^ 2 := by ring
    _ = s ^ 2 / 2 * ∫ x, x ^ 2 ∂μ := integral_const_mul _ _

/-- Two laws with the same mean: `‖φ_σ(s) - φ_ν(s)‖ ≤ (s²/2)(E_σ X² + E_ν X²)`. -/
theorem kill_norm_charFun_sub_charFun_le {μ ρ : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ρ] (hμ1 : Integrable (fun x : ℝ => x) μ)
    (hμ2 : Integrable (fun x : ℝ => x ^ 2) μ) (hρ1 : Integrable (fun x : ℝ => x) ρ)
    (hρ2 : Integrable (fun x : ℝ => x ^ 2) ρ) (hmean : ∫ x, x ∂μ = ∫ x, x ∂ρ) (s : ℝ) :
    ‖charFun μ s - charFun ρ s‖ ≤ s ^ 2 / 2 * (∫ x, x ^ 2 ∂μ + ∫ x, x ^ 2 ∂ρ) := by
  have h1 := kill_norm_charFun_sub_le hμ1 hμ2 s
  have h2 := kill_norm_charFun_sub_le hρ1 hρ2 s
  rw [hmean] at h1
  calc ‖charFun μ s - charFun ρ s‖ =
      ‖(charFun μ s - (1 + ((s * ∫ x, x ∂ρ : ℝ) : ℂ) * I)) -
        (charFun ρ s - (1 + ((s * ∫ x, x ∂ρ : ℝ) : ℂ) * I))‖ := by ring_nf
    _ ≤ ‖charFun μ s - (1 + ((s * ∫ x, x ∂ρ : ℝ) : ℂ) * I)‖ +
        ‖charFun ρ s - (1 + ((s * ∫ x, x ∂ρ : ℝ) : ℂ) * I)‖ := norm_sub_le _ _
    _ ≤ s ^ 2 / 2 * ∫ x, x ^ 2 ∂μ + s ^ 2 / 2 * ∫ x, x ^ 2 ∂ρ := add_le_add h1 h2
    _ = s ^ 2 / 2 * (∫ x, x ^ 2 ∂μ + ∫ x, x ^ 2 ∂ρ) := by ring

/-- A direction law has a second moment `E X² ≤ 2A/θσ²`. -/
theorem SigmaLaw.kill_second_moment {A θσ : ℝ} {σ : ProbabilityMeasure ℝ} (h : SigmaLaw A θσ σ)
    (hθσ : 0 < θσ) :
    Integrable (fun x : ℝ => x ^ 2) (σ : Measure ℝ) ∧
      ∫ x, x ^ 2 ∂(σ : Measure ℝ) ≤ 2 * A / θσ ^ 2 := by
  have hae : ∀ᵐ x ∂(σ : Measure ℝ), x ^ 2 ≤ 2 / θσ ^ 2 * Real.exp (θσ * x) := by
    filter_upwards [compl_mem_ae_iff.2 h.pos] with x hx
    have hx0 : 0 ≤ x := by simp at hx; exact hx.le
    have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg hθσ.le hx0)
    have : (θσ * x) ^ 2 / 2 ≤ Real.exp (θσ * x) := by nlinarith [mul_nonneg hθσ.le hx0]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hint : Integrable (fun x : ℝ => x ^ 2) (σ : Measure ℝ) :=
    (h.expInt.const_mul (2 / θσ ^ 2)).mono' (by fun_prop) (by
      filter_upwards [hae] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hx)
  refine ⟨hint, ?_⟩
  calc ∫ x, x ^ 2 ∂(σ : Measure ℝ) ≤ ∫ x, 2 / θσ ^ 2 * Real.exp (θσ * x) ∂(σ : Measure ℝ) :=
        integral_mono_ae hint (h.expInt.const_mul _) hae
    _ = 2 / θσ ^ 2 * ∫ x, Real.exp (θσ * x) ∂(σ : Measure ℝ) := integral_const_mul _ _
    _ ≤ 2 / θσ ^ 2 * A := by gcongr; exact h.expMom
    _ = 2 * A / θσ ^ 2 := by ring

/-- For a mean-one law with finite second moment, `E X² = Var X + 1`. -/
theorem kill_integral_sq_eq_lawVar {ν : ProbabilityMeasure ℝ} (hmean : lawMean ν = 1)
    (h1 : Integrable (fun x : ℝ => x) (ν : Measure ℝ))
    (h2 : Integrable (fun x : ℝ => x ^ 2) (ν : Measure ℝ)) :
    ∫ x, x ^ 2 ∂(ν : Measure ℝ) = lawVar ν + 1 := by
  have hm : ∫ x, x ∂(ν : Measure ℝ) = 1 := hmean
  have e : (fun x : ℝ => (x - lawMean ν) ^ 2) = fun x => x ^ 2 - 2 * x + 1 := by
    funext x; rw [hmean]; ring
  have hv : lawVar ν = ∫ x, x ^ 2 ∂(ν : Measure ℝ) - 1 := by
    have i1 : Integrable (fun x : ℝ => x ^ 2 - 2 * x) (ν : Measure ℝ) := h2.sub (h1.const_mul 2)
    have i2 : Integrable (fun x : ℝ => 2 * x) (ν : Measure ℝ) := h1.const_mul 2
    unfold lawVar
    rw [e, integral_add i1 (integrable_const _), integral_sub h2 i2, integral_const_mul, hm,
      integral_const, probReal_univ, one_smul]
    ring
  linarith

/-- The `ν`-part constant `c_ν = c₀ min(1, vlo)/(4 D² vhi)`. -/
def killCnu (D vlo vhi : ℝ) : ℝ := c0CharFn * min 1 vlo / (4 * D ^ 2 * vhi)

theorem killCnu_pos {D vlo vhi : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    0 < killCnu D vlo vhi := by
  unfold killCnu
  have : 0 < min 1 vlo := lt_min one_pos hvlo
  have : 0 < vhi := lt_of_lt_of_le hvlo hvhi
  have := c0CharFn_pos
  positivity

/-- The `ν`-gap along a slope `a ≥ 1/2`: `1 - ‖φ_ν(a t)‖² ≥ c_ν min(t², 1)`. -/
theorem kill_regLaw_charFun_gap {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) {a : ℝ} (ha : 1 / 2 ≤ a) (t : ℝ) :
    killCnu D vlo vhi * min (t ^ 2) 1 ≤ 1 - ‖charFun (ν : Measure ℝ) (a * t)‖ ^ 2 := by
  have hmc := hν.momClass hθ hvlo
  have hloc : LocBd D (ν : Measure ℝ) := hν.envBd.locBd hD.le hθ.le
  have h2 : MemLp id 2 (ν : Measure ℝ) := hmc.memLp3.mono_exponent (by norm_num)
  set v := lawVar ν with hv
  have hv0 : vlo ≤ v := hν.var_ge
  have hv1 : v ≤ vhi := hν.var_le
  have hvpos : 0 < v := lt_of_lt_of_le hvlo hv0
  set σ₀ := Real.sqrt v with hσ₀
  have hσ₀pos : 0 < σ₀ := Real.sqrt_pos.2 hvpos
  have hσ₀sq : σ₀ ^ 2 = v := Real.sq_sqrt hvpos.le
  have hm : ∫ x, x ∂(ν : Measure ℝ) = 1 := hν.mean
  have hvar : ∫ x, (x - 1) ^ 2 ∂(ν : Measure ℝ) = σ₀ ^ 2 := by
    rw [hσ₀sq, hv]; unfold lawVar; rw [hν.mean]
  have hg := one_sub_norm_charFun_sq_ge hloc h2 hm hvar hσ₀pos (a * t)
  have e1 : (a * t) ^ 2 * σ₀ ^ 2 = (a * t) ^ 2 * v := by rw [hσ₀sq]
  have e2 : (D * σ₀) ^ 2 = D ^ 2 * v := by rw [mul_pow, hσ₀sq]
  rw [e1, e2] at hg
  refine le_trans ?_ hg
  -- arithmetic
  set X := (a * t) ^ 2 with hX
  have hX4 : t ^ 2 / 4 ≤ X := by
    rw [hX, mul_pow]
    have : 1 / 4 ≤ a ^ 2 := by nlinarith
    nlinarith [sq_nonneg t]
  have hmin1 : min 1 vlo * (min (t ^ 2) 1 / 4) ≤ min 1 (X * v) := by
    have hml : min 1 vlo ≤ 1 := min_le_left _ _
    have hml' : min 1 vlo ≤ vlo := min_le_right _ _
    have hml0 : 0 ≤ min 1 vlo := le_min zero_le_one hvlo.le
    have hmt : min (t ^ 2) 1 / 4 ≤ 1 := by
      have : min (t ^ 2) 1 ≤ 1 := min_le_right _ _
      linarith
    have hmt' : min (t ^ 2) 1 / 4 ≤ X := by
      have : min (t ^ 2) 1 ≤ t ^ 2 := min_le_left _ _
      linarith
    refine le_min ?_ ?_
    · calc min 1 vlo * (min (t ^ 2) 1 / 4) ≤ 1 * 1 := by
            gcongr
      _ = 1 := one_mul 1
    · calc min 1 vlo * (min (t ^ 2) 1 / 4) ≤ vlo * X := by
            gcongr
        _ ≤ X * v := by rw [mul_comm]; gcongr
  have hc0 := c0CharFn_pos
  unfold killCnu
  have hD2 : 0 < D ^ 2 := by positivity
  have hvhi : 0 < vhi := lt_of_lt_of_le hvpos hv1
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc c0CharFn * min 1 vlo * min (t ^ 2) 1 * (D ^ 2 * v)
      = c0CharFn * (min 1 vlo * (min (t ^ 2) 1 / 4)) * (4 * D ^ 2 * v) := by ring
    _ ≤ c0CharFn * min 1 (X * v) * (4 * D ^ 2 * vhi) := by
        gcongr

/-- **Class-level complex Fourier gap** (AT 命题 1).  For the regular class `(D, θ, vlo, vhi)`
there is `c ∈ (0, 1]` such that for every direction class `SigmaLaw A θσ` (`θσ > 0`) there is
`r > 0` with: for `RegLaw D θ vlo vhi ν`, `SigmaLaw A θσ σ`, `‖z‖ < r`, `a ∈ [1/2, 2]` and all
`t`, `‖(1 - z) φ_ν(a t) + z φ_σ(a t)‖² ≤ 1 - c min(t², 1)`. -/
theorem kill_complex_charFun_gap (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ A θσ : ℝ, 0 < θσ → ∃ r : ℝ, 0 < r ∧
      ∀ ν σ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν → SigmaLaw A θσ σ →
        ∀ z : ℂ, ‖z‖ < r → ∀ a ∈ Icc (1 / 2 : ℝ) 2, ∀ t : ℝ,
          ‖(1 - z) * charFun (ν : Measure ℝ) (a * t) + z * charFun (σ : Measure ℝ) (a * t)‖ ^ 2 ≤
            1 - c * min (t ^ 2) 1 := by
  set cν := killCnu D vlo vhi with hcν
  have hcν0 : 0 < cν := killCnu_pos hD hvlo hvhi
  refine ⟨min (cν / 2) 1, lt_min (by positivity) one_pos, min_le_right _ _, ?_⟩
  intro A θσ hθσ
  set L := max 1 (2 * A / θσ ^ 2 + vhi + 1) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  refine ⟨min 1 (cν / (16 * L)), lt_min one_pos (by positivity), ?_⟩
  intro ν σ hν hσ z hz a ha t
  have hz1 : ‖z‖ ≤ 1 := hz.le.trans (min_le_left _ _)
  have hzr : ‖z‖ ≤ cν / (16 * L) := hz.le.trans (min_le_right _ _)
  set s := a * t with hs
  set p := ‖charFun (ν : Measure ℝ) s‖ with hp
  set μt := min (t ^ 2) 1 with hμt
  have hμt0 : 0 ≤ μt := le_min (sq_nonneg _) zero_le_one
  have hp0 : 0 ≤ p := norm_nonneg _
  have hp1 : p ≤ 1 := norm_charFun_le_one _
  -- the `ν`-gap
  have hgap : cν * μt ≤ 1 - p ^ 2 := kill_regLaw_charFun_gap hD hθ hvlo hν ha.1 t
  -- moments
  have hmc := hν.momClass hθ hvlo
  have hν2m : MemLp id 2 (ν : Measure ℝ) := hmc.memLp3.mono_exponent (by norm_num)
  have hν2 : Integrable (fun x : ℝ => x ^ 2) (ν : Measure ℝ) := by
    simpa using hν2m.integrable_sq
  have hν1 : Integrable (fun x : ℝ => x) (ν : Measure ℝ) := hν2m.integrable (by norm_num)
  obtain ⟨hσ2, hσ2le⟩ := hσ.kill_second_moment hθσ
  have hσ1 : Integrable (fun x : ℝ => x) (σ : Measure ℝ) := by
    refine Integrable.of_integral_ne_zero ?_
    have : ∫ x, x ∂(σ : Measure ℝ) = 1 := hσ.mean
    rw [this]; exact one_ne_zero
  have hmean : ∫ x, x ∂(σ : Measure ℝ) = ∫ x, x ∂(ν : Measure ℝ) := by
    have h1 : ∫ x, x ∂(σ : Measure ℝ) = 1 := hσ.mean
    have h2 : ∫ x, x ∂(ν : Measure ℝ) = 1 := hν.mean
    rw [h1, h2]
  have hν2eq := kill_integral_sq_eq_lawVar hν.mean hν1 hν2
  -- the difference of the characteristic functions
  set δ := ‖charFun (σ : Measure ℝ) s - charFun (ν : Measure ℝ) s‖ with hδ
  have hδ2 : δ ≤ 2 := by
    calc δ ≤ ‖charFun (σ : Measure ℝ) s‖ + ‖charFun (ν : Measure ℝ) s‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (norm_charFun_le_one _) (norm_charFun_le_one _)
      _ = 2 := by norm_num
  have hδL : δ ≤ 2 * L * μt := by
    have hd := kill_norm_charFun_sub_charFun_le hσ1 hσ2 hν1 hν2 hmean s
    have hm2 : ∫ x, x ^ 2 ∂(σ : Measure ℝ) + ∫ x, x ^ 2 ∂(ν : Measure ℝ) ≤ L := by
      rw [hν2eq]
      have := hν.var_le
      exact le_trans (by linarith) (le_max_right _ _)
    have hs2 : s ^ 2 ≤ 4 * t ^ 2 := by
      rw [hs, mul_pow]
      have : a ^ 2 ≤ 4 := by nlinarith [ha.1, ha.2]
      nlinarith [sq_nonneg t]
    have hm20 : 0 ≤ ∫ x, x ^ 2 ∂(σ : Measure ℝ) + ∫ x, x ^ 2 ∂(ν : Measure ℝ) :=
      add_nonneg (integral_nonneg fun x => sq_nonneg x) (integral_nonneg fun x => sq_nonneg x)
    rcases le_total (t ^ 2) 1 with ht | ht
    · have : μt = t ^ 2 := min_eq_left ht
      rw [this]
      calc δ ≤ s ^ 2 / 2 * (∫ x, x ^ 2 ∂(σ : Measure ℝ) + ∫ x, x ^ 2 ∂(ν : Measure ℝ)) := hd
        _ ≤ (4 * t ^ 2) / 2 * L := by gcongr
        _ = 2 * L * t ^ 2 := by ring
    · have : μt = 1 := min_eq_right ht
      rw [this]
      nlinarith
  -- assembling
  have hdecomp : (1 - z) * charFun (ν : Measure ℝ) s + z * charFun (σ : Measure ℝ) s =
      charFun (ν : Measure ℝ) s + z * (charFun (σ : Measure ℝ) s - charFun (ν : Measure ℝ) s) := by
    ring
  have hnorm : ‖(1 - z) * charFun (ν : Measure ℝ) s + z * charFun (σ : Measure ℝ) s‖ ≤
      p + ‖z‖ * δ := by
    rw [hdecomp]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
  have hzδ0 : 0 ≤ ‖z‖ * δ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hzδ2 : ‖z‖ * δ ≤ 2 := by
    calc ‖z‖ * δ ≤ 1 * 2 := mul_le_mul hz1 hδ2 (norm_nonneg _) zero_le_one
      _ = 2 := one_mul 2
  have hsq : ‖(1 - z) * charFun (ν : Measure ℝ) s + z * charFun (σ : Measure ℝ) s‖ ^ 2 ≤
      p ^ 2 + 4 * (‖z‖ * δ) := by
    calc _ ≤ (p + ‖z‖ * δ) ^ 2 := by gcongr
      _ = p ^ 2 + 2 * p * (‖z‖ * δ) + (‖z‖ * δ) ^ 2 := by ring
      _ ≤ p ^ 2 + 4 * (‖z‖ * δ) := by nlinarith
  have hzδ : 4 * (‖z‖ * δ) ≤ cν / 2 * μt := by
    have h1 : ‖z‖ * δ ≤ cν / (16 * L) * (2 * L * μt) :=
      mul_le_mul hzr hδL (norm_nonneg _) (by positivity)
    have h2 : cν / (16 * L) * (2 * L * μt) = cν / 8 * μt := by
      field_simp; ring
    linarith
  have hc : min (cν / 2) 1 * μt ≤ cν / 2 * μt :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hμt0
  linarith

end

end PGM
