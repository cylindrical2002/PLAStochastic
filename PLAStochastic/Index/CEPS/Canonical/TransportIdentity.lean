import PLAStochastic.Index.CEPS.Canonical.TransportL

/-!
# CEPS WP3, lemma C-4: discount derivative of `L` and the transport identity

* `CepsCanonDomain.hasDerivAt_cepsCanonL_q`: `q ↦ L(ζ; μ, q)` is complex differentiable with
  derivative `(2π)⁻¹ ∫ ∂_q log F(s)/(s - ζ) ds` on the line `Re s = c`.
* `CepsCanonDomain.cepsCanonL_transport`: `∂_μ L(ζ) + ζ ∂_q L(ζ) = ∂_μ L(0)`.
* `CepsCanonDomain.hasDerivAt_cepsCanonR_mu`: `∂_μ (L(ζ) - L(0)) = -ζ ∂_q L(ζ)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

set_option maxHeartbeats 1000000 in
/-- Discount derivative of `L` (no decay hypothesis needed). -/
theorem hasDerivAt_cepsCanonL_q {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 2) (hμη : μ.im = 0)
    {q : ℂ} (hq : ‖q‖ < dom.q₀ / 4) {ζ : ℂ} (hζ : ζ.re < c) :
    Integrable (fun y : ℝ => cepsDqLogF D θ ρW μ q (c + y * I) / ((c : ℂ) + y * I - ζ)) ∧
      HasDerivAt (fun q' : ℂ => cepsCanonL D θ ρW γ c μ q' ζ)
        ((2 * Real.pi : ℂ)⁻¹ *
          ∫ y : ℝ, cepsDqLogF D θ ρW μ q (c + y * I) / ((c : ℂ) + y * I - ζ)) q := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hq0 := dom.q₀_pos
  have hμ' : ‖μ‖ ≤ dom.μ₀ := by have := dom.μ₀_pos; linarith
  have hball : ∀ q' ∈ Metric.ball q (dom.q₀ / 4), ‖q'‖ ≤ dom.q₀ / 2 := by
    intro q' hq'
    rw [Metric.mem_ball, dist_eq_norm] at hq'
    have := norm_sub_norm_le q' q; linarith
  set Cq : ℝ := 3 / dom.dd₀ + 4 * dom.c₀ / dom.q₀ with hCq
  have hdd := dom.dd₀_pos hD
  obtain ⟨hB, -⟩ := integrable_cepsLineBound hW hθ hD (c := c) (by linarith) (by linarith) hζ
  have hpt : ∀ y : ℝ, ∀ q' ∈ Metric.ball q (dom.q₀ / 4),
      ‖cepsDqLogF D θ ρW μ q' (c + y * I) / ((c : ℂ) + y * I - ζ)‖ ≤
        Cq * cepsLineBound ρW c ζ y := by
    intro y q' hq'
    set s : ℂ := (c : ℂ) + y * I with hsdef
    have hsre : s.re = c := by simp [hsdef]
    obtain ⟨-, hdq⟩ := dom.norm_dLogF_le hW hθ hD (μ := μ) (q := q') (s := s) hμ
      (by rw [hμη, abs_zero, zero_mul]; exact dom.η_pos.le) (hball q' hq')
      (by rw [hsre, abs_of_pos (by linarith)]; exact hc1)
      (by rw [hsre, abs_of_pos (by linarith)]; exact hc2)
    have hs0 : 0 < ‖s‖ := by have := re_le_norm s; rw [hsre] at this; linarith
    have hsζ : 0 < ‖s - ζ‖ := by
      have := re_le_norm (s - ζ); rw [sub_re, hsre] at this; linarith
    set a := ‖stepTransform ρW s‖ with ha
    set b := 1 / ‖s - ζ‖ with hb
    set e := 1 / ‖s‖ with he
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ b := by positivity
    have he0 : 0 ≤ e := by positivity
    have hb2 : b ^ 2 = ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹ := by
      rw [hb, one_div, inv_pow, hsdef, norm_line_sub_sq']
    have he2 : e ^ 2 = ((y - 0) ^ 2 + c ^ 2)⁻¹ := by
      rw [he, one_div, inv_pow, hsdef, norm_line_sq']
    have hlb : cepsLineBound ρW c ζ y = a ^ 2 + b ^ 2 + e ^ 2 := by
      rw [cepsLineBound, hb2, he2]
    rw [norm_div, div_eq_mul_one_div, hlb]
    calc ‖cepsDqLogF D θ ρW μ q' s‖ * (1 / ‖s - ζ‖)
        ≤ (3 / dom.dd₀ * a + 4 * dom.c₀ / dom.q₀ * e) * b := mul_le_mul_of_nonneg_right hdq hb0
      _ ≤ Cq * (a ^ 2 + b ^ 2 + e ^ 2) := by
          have h1 : a * b ≤ a ^ 2 + b ^ 2 + e ^ 2 := by nlinarith [sq_nonneg (a - b), sq_nonneg e]
          have h2 : e * b ≤ a ^ 2 + b ^ 2 + e ^ 2 := by nlinarith [sq_nonneg (e - b), sq_nonneg a]
          have h3 : 0 ≤ 3 / dom.dd₀ := by positivity
          have h4 : 0 ≤ 4 * dom.c₀ / dom.q₀ := by positivity
          calc (3 / dom.dd₀ * a + 4 * dom.c₀ / dom.q₀ * e) * b
              = 3 / dom.dd₀ * (a * b) + 4 * dom.c₀ / dom.q₀ * (e * b) := by ring
            _ ≤ 3 / dom.dd₀ * (a ^ 2 + b ^ 2 + e ^ 2) +
                4 * dom.c₀ / dom.q₀ * (a ^ 2 + b ^ 2 + e ^ 2) := by gcongr
            _ = Cq * (a ^ 2 + b ^ 2 + e ^ 2) := by rw [hCq]; ring
  have hdiff : ∀ y : ℝ, ∀ q' ∈ Metric.ball q (dom.q₀ / 4),
      HasDerivAt (fun q'' : ℂ => cepsLineIntegrand D θ ρW γ c μ q'' ζ y)
        (cepsDqLogF D θ ρW μ q' (c + y * I) / ((c : ℂ) + y * I - ζ)) q' := by
    intro y q' hq'
    have hq'' : ‖q'‖ ≤ dom.q₀ := by have := hball q' hq'; linarith
    obtain ⟨hx, hd, hQ, hγs, hslit⟩ := dom.line_point_facts hW hθ hD hγ1 hγ2 hc1 hc2 hμ' hμη hq'' y
    exact (hasDerivAt_logF_q hW hθ hD hx hd hQ hγs hslit).div_const _
  have hqq : ‖q‖ ≤ dom.q₀ := by linarith
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun q' : ℂ => cepsLineIntegrand D θ ρW γ c μ q' ζ)
    (F' := fun q' y => cepsDqLogF D θ ρW μ q' (c + y * I) / ((c : ℂ) + y * I - ζ))
    (bound := fun y => Cq * cepsLineBound ρW c ζ y) (x₀ := q) (s := Metric.ball q (dom.q₀ / 4))
    (Metric.ball_mem_nhds q (show (0 : ℝ) < dom.q₀ / 4 by positivity))
    (Filter.eventually_of_mem (Metric.ball_mem_nhds q (show (0 : ℝ) < dom.q₀ / 4 by positivity))
      fun q' hq' =>
      (dom.continuous_lineIntegrand hW hθ hD hγ1 hγ2 hc1 hc2 hμ' hμη
        (by have := hball q' hq'; linarith) hζ).aestronglyMeasurable)
    (dom.integrable_cepsCanonL_integrand hW hθ hD hγ1 hγ2 hc1 hc2 hμ' hμη hqq hζ)
    (((dom.continuous_dLogF_line hW hθ hD hc1 hc2 hμ' hμη hqq).2.div
      (by fun_prop) (fun y h0 => by
        have := congrArg re h0; simp at this; linarith)).aestronglyMeasurable)
    (Eventually.of_forall fun y q' hq' => hpt y q' hq') (hB.const_mul Cq)
    (Eventually.of_forall fun y q' hq' => hdiff y q' hq')
  refine ⟨hmain.1, ?_⟩
  have e : (fun q' : ℂ => cepsCanonL D θ ρW γ c μ q' ζ) = fun q' : ℂ =>
      (2 * Real.pi : ℂ)⁻¹ * (∫ y, cepsLineIntegrand D θ ρW γ c μ q' ζ y) - Complex.log (γ - ζ) := by
    funext q'; rfl
  rw [e]
  exact (hmain.2.const_mul _).sub_const _

set_option maxHeartbeats 1000000 in
/-- **C-4 (transport identity).** Under line decay of `M₀`, for real `|t| < μ₀/2`,
`‖q‖ < q₀/4` and `Re ζ < c`:
`∂_μ L(ζ; t, q) + ζ ∂_q L(ζ; t, q) = ∂_μ L(0; t, q)` (i.e. `= ∂_μ ℓ`). -/
theorem cepsCanonL_transport {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {K : ℝ}
    (hdec : ∀ y : ℝ, ‖stepTransform ρW (c + y * I)‖ ≤ K / (1 + y ^ 2)) {t : ℝ}
    (ht : |t| < dom.μ₀ / 2) {q : ℂ} (hq : ‖q‖ < dom.q₀ / 4) {ζ : ℂ} (hζ : ζ.re < c) :
    deriv (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ) t +
        ζ * deriv (fun q' : ℂ => cepsCanonL D θ ρW γ c t q' ζ) q =
      deriv (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q 0) t := by
  have hc0 := dom.c₀_pos
  have hq0 := dom.q₀_pos
  have hq2 : ‖q‖ ≤ dom.q₀ / 2 := by linarith
  have hμ : ‖(t : ℂ)‖ ≤ dom.μ₀ / 2 := by rw [norm_real, Real.norm_eq_abs]; linarith
  have h0 : (0 : ℂ).re < c := by simp; linarith
  obtain ⟨iμ, dμ⟩ := dom.hasDerivAt_cepsCanonL_mu hW hθ hD hγ1 hγ2 hc1 hc2 hdec ht hq2 hζ
  obtain ⟨iμ0, dμ0⟩ := dom.hasDerivAt_cepsCanonL_mu hW hθ hD hγ1 hγ2 hc1 hc2 hdec ht hq2 h0
  obtain ⟨iq, dq⟩ := dom.hasDerivAt_cepsCanonL_q hW hθ hD hγ1 hγ2 hc1 hc2 hμ (by simp) hq hζ
  rw [dμ.deriv, dμ0.deriv, dq.deriv]
  -- pointwise reduction
  have hpt : ∀ y : ℝ,
      cepsDmuLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - ζ) +
          ζ * (cepsDqLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - ζ)) -
        cepsDmuLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - 0) =
      cepsSq D θ ρW t q * ζ * (((c : ℂ) + y * I) * ((c : ℂ) + y * I - ζ))⁻¹ := by
    intro y
    have hμ' : ‖(t : ℂ)‖ ≤ dom.μ₀ := by have := dom.μ₀_pos; linarith
    obtain ⟨hx, hd, hQ, -, -⟩ := dom.line_point_facts hW hθ hD (q := q) hγ1 hγ2 hc1 hc2 hμ'
      (by simp) (by linarith) y
    have hT := cepsDmuLogF_add hW hθ hD hx hd hQ
    have hs : (c : ℂ) + y * I ≠ 0 := by intro h; have := congrArg re h; simp at this; linarith
    have hsζ : (c : ℂ) + y * I - ζ ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith
    rw [sub_zero]
    have hdμ : cepsDmuLogF D θ ρW t q (c + y * I) =
        cepsSq D θ ρW t q - ((c : ℂ) + y * I) * cepsDqLogF D θ ρW t q (c + y * I) := by
      rw [← hT]; ring
    rw [hdμ]
    field_simp
    ring
  have hint : ∫ y : ℝ, (cepsDmuLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - ζ) +
        ζ * (cepsDqLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - ζ)) -
        cepsDmuLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - 0)) = 0 := by
    simp_rw [hpt]
    rw [integral_const_mul, integral_inv_mul_line_eq_zero (by linarith) hζ, mul_zero]
  rw [integral_sub (f := fun y : ℝ => cepsDmuLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - ζ) +
        ζ * (cepsDqLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - ζ)))
      (g := fun y : ℝ => cepsDmuLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - 0))
      (iμ.add (iq.const_mul ζ)) iμ0,
    integral_add (f := fun y : ℝ => cepsDmuLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - ζ))
      (g := fun y : ℝ => ζ * (cepsDqLogF D θ ρW t q (c + y * I) / ((c : ℂ) + y * I - ζ)))
      iμ (iq.const_mul ζ), integral_const_mul] at hint
  linear_combination (2 * Real.pi : ℂ)⁻¹ * hint


/-- **C-4, remainder form.** With `R(ζ) = L(ζ) - ℓ`: `∂_μ R(ζ; t, q) = -ζ ∂_q L(ζ; t, q)`. -/
theorem hasDerivAt_cepsCanonR_mu {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {K : ℝ}
    (hdec : ∀ y : ℝ, ‖stepTransform ρW (c + y * I)‖ ≤ K / (1 + y ^ 2)) {t : ℝ}
    (ht : |t| < dom.μ₀ / 2) {q : ℂ} (hq : ‖q‖ < dom.q₀ / 4) {ζ : ℂ} (hζ : ζ.re < c) :
    HasDerivAt (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ - cepsCanonL D θ ρW γ c t' q 0)
      (-(ζ * deriv (fun q' : ℂ => cepsCanonL D θ ρW γ c t q' ζ) q)) t := by
  have hq2 : ‖q‖ ≤ dom.q₀ / 2 := by have := dom.q₀_pos; linarith
  have h0 : (0 : ℂ).re < c := by simp; have := dom.c₀_pos; linarith
  have d1 := (dom.hasDerivAt_cepsCanonL_mu hW hθ hD hγ1 hγ2 hc1 hc2 hdec ht hq2 hζ).2
  have d2 := (dom.hasDerivAt_cepsCanonL_mu hW hθ hD hγ1 hγ2 hc1 hc2 hdec ht hq2 h0).2
  have htr := dom.cepsCanonL_transport hW hθ hD hγ1 hγ2 hc1 hc2 hdec ht hq hζ
  rw [d1.deriv, d2.deriv] at htr
  refine (d1.sub d2).congr_deriv ?_
  linear_combination htr

end

end CepsCanonDomain

end PGM
