import PLAStochastic.Index.CEPS.Ident.Liouville

/-!
# CEPS WP4, lemma C-5 for `Re q > 0`: the glued function is constant

Continuation of `Ident.Liouville`: the glued function `identE` is entire
(`differentiable_identE`), bounded (`exists_bound_identE`) and tends to `1` along the negative
real axis (`tendsto_identE_atBot`); by Liouville `identE ≡ 1`, which gives

* `one_sub_asc_eq_of_re_pos`: `1 - A₊(ζ) = (β₊ - ζ) e^{L^{(2c₀)}(ζ)}` for `Re ζ < 2c₀`;
* `one_sub_asc_eq_canonL_of_re_pos`: `1 - A₊(ζ) = (β₊ - ζ) e^{L(ζ)}` for `Re ζ < c₀`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology Bornology
open PGM.WienerHopf
open scoped ENNReal

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

theorem identE_eq_EL (ρW : Measure ℝ) (μ : ℝ) (q : ℂ) {ζ : ℂ} (hζ : ζ.re < 2 * dom.c₀) :
    dom.identE ρW μ q ζ = dom.identEL ρW μ q ζ := if_pos hζ

theorem norm_cexp_le_exp_norm (z : ℂ) : ‖cexp z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (re_le_norm z)

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

variable {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 < q.re) (hq : ‖q‖ ≤ dom.q₀)
include hμ hq0 hq

theorem identE_eq_ER {ζ : ℂ} (hζ : dom.c₀ < ζ.re) :
    dom.identE ρW μ q ζ = dom.identER ρW μ q ζ := by
  unfold identE
  split_ifs with h
  · exact dom.identEL_eq_identER hW hθ hD hμ hq0 hq hζ h
  · rfl

theorem differentiable_identE : Differentiable ℂ (dom.identE ρW μ q) := by
  intro z
  by_cases hz : z.re < 2 * dom.c₀
  · have hU : IsOpen {w : ℂ | w.re < 2 * dom.c₀} := isOpen_lt continuous_re continuous_const
    exact (dom.differentiableAt_identEL hW hθ hD hμ hq0 hq hz).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => dom.identE_eq_EL ρW μ q hw)
  · push Not at hz
    have hc0 := dom.c₀_pos
    have hz' : dom.c₀ < z.re := by linarith
    have hU : IsOpen {w : ℂ | dom.c₀ < w.re} := isOpen_lt continuous_const continuous_re
    exact (dom.differentiableAt_identER hW hθ hD hμ hq0 hq hz').congr_of_eventuallyEq
      (Filter.eventually_of_mem (hU.mem_nhds hz') fun w hw => dom.identE_eq_ER hW hθ hD hμ hq0 hq hw)

/-- The glued function is bounded. -/
theorem exists_bound_identE : ∃ C, ∀ ζ, ‖dom.identE ρW μ q ζ‖ ≤ C := by
  have := hW.isProbabilityMeasure
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hc1 := dom.c₀_le_small
  have hCL := dom.CL_nonneg
  have hbp := dom.norm_rootPlus_le' hW hθ hD hμ hq
  have hbm := dom.norm_rootMinus_le' hW hθ hD hμ hq
  have hrep := (dom.re_roots hW hθ hD hμ hq0 hq).1
  set βp := cepsRootPlus D θ ρW μ q with hβp
  set βm := cepsRootMinus D θ ρW μ q with hβm
  have hs : ‖cexp (-q)‖ < 1 := norm_cexp_neg_lt_one hq0
  set KΨ : ℝ := dom.CL * (2 * D ^ 2 / θ + 1 / dom.c₀ + 1 / (2 * dom.c₀)) with hKΨ
  set KΦ : ℝ := dom.CL * (2 * D ^ 2 / θ + 1 / dom.c₀ + 1 / (2 * (2 * dom.c₀))) with hKΦ
  set Mp : ℝ := expEntryMass (driftStep ρW μ) (Ioi 0) (θ / 2) with hMp
  set CR : ℝ := 3 * Real.exp KΨ / (1 - ‖cexp (-q)‖) with hCR
  set CL' : ℝ := (1 + Mp) * Real.exp KΦ * (1 + 8 / dom.c₀) with hCL'
  -- right region
  have hRb : ∀ ζ : ℂ, 3 * dom.c₀ / 2 ≤ ζ.re → ‖dom.identE ρW μ q ζ‖ ≤ CR := by
    intro ζ hζ
    rw [dom.identE_eq_ER hW hθ hD hμ hq0 hq (by linarith), identER]
    have h1ζ : 1 ≤ ‖1 + ζ‖ := by
      have := re_le_norm (1 + ζ); simp at this; linarith
    have hnum : ‖ζ - βm‖ ≤ 3 * ‖1 + ζ‖ := by
      calc ‖ζ - βm‖ = ‖(1 + ζ) - (1 + βm)‖ := by ring_nf
        _ ≤ ‖1 + ζ‖ + ‖1 + βm‖ := norm_sub_le _ _
        _ ≤ ‖1 + ζ‖ + (1 + dom.c₀ / 4) := by
            gcongr; exact (norm_add_le _ _).trans (by simp; linarith)
        _ ≤ 3 * ‖1 + ζ‖ := by linarith
    have hΨ : ‖dom.identΨ ρW μ q ζ‖ ≤ KΨ := by
      have h := dom.norm_lineCauchy_logF_le hW hθ hD le_rfl (by linarith) hμ hq (ζ := ζ)
        (by linarith)
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hCL)
      have habs : dom.c₀ / 2 ≤ |dom.c₀ - ζ.re| := by
        rw [abs_of_neg (by linarith)]; linarith
      have : 1 / (2 * |dom.c₀ - ζ.re|) ≤ 1 / dom.c₀ :=
        one_div_le_one_div_of_le hc0 (by linarith)
      linarith
    have hexp : ‖cexp (-dom.identΨ ρW μ q ζ)‖ ≤ Real.exp KΨ :=
      (norm_cexp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by rw [norm_neg]; exact hΨ))
    have hAm : ‖descTransform (driftStep ρW μ) (cexp (-q)) ζ‖ ≤ ‖cexp (-q)‖ :=
      norm_entryTransform_le (norm_cexp_neg_le_one hq0.le)
        (fun x hx => mul_nonpos_of_nonneg_of_nonpos (by linarith) hx)
    have hden : 1 - ‖cexp (-q)‖ ≤ ‖1 - descTransform (driftStep ρW μ) (cexp (-q)) ζ‖ := by
      have := norm_sub_norm_le (1 : ℂ) (descTransform (driftStep ρW μ) (cexp (-q)) ζ)
      rw [norm_one] at this; linarith
    have hpos : 0 < 1 - ‖cexp (-q)‖ := by linarith
    rw [norm_div, norm_mul, norm_mul, div_le_iff₀ (mul_pos (hpos.trans_le hden) (by linarith))]
    calc ‖ζ - βm‖ * ‖cexp (-dom.identΨ ρW μ q ζ)‖
        ≤ (3 * ‖1 + ζ‖) * Real.exp KΨ := mul_le_mul hnum hexp (norm_nonneg _) (by positivity)
      _ = CR * ((1 - ‖cexp (-q)‖) * ‖1 + ζ‖) := by rw [hCR]; field_simp
      _ ≤ CR * (‖1 - descTransform (driftStep ρW μ) (cexp (-q)) ζ‖ * ‖1 + ζ‖) := by
          gcongr
  -- left region outside the disc around `β₊`
  have hLb : ∀ ζ : ℂ, ζ.re ≤ 3 * dom.c₀ / 2 → dom.c₀ / 4 ≤ ‖ζ - βp‖ →
      ‖dom.identE ρW μ q ζ‖ ≤ CL' := by
    intro ζ hζ hd
    have hζ2 : ζ.re < 2 * dom.c₀ := by linarith
    have hne : ζ ≠ βp := by intro h; rw [h, sub_self, norm_zero] at hd; linarith
    have hβζ : 0 < ‖βp - ζ‖ := by rw [norm_sub_rev]; linarith
    rw [dom.identE_eq_EL ρW μ q hζ2, dom.identEL_eq hW hθ hD hμ hq0 hq hne, identP,
      dom.cexp_neg_canonL₂ ρW μ q hζ2, norm_div, div_le_iff₀ hβζ, norm_mul, norm_mul]
    have hA : ‖1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ‖ ≤ 1 + Mp := by
      have h := dom.norm_asc_le hW hθ hD hμ (norm_cexp_neg_le_one hq0.le) (ζ := ζ)
        (by linarith)
      calc _ ≤ ‖(1 : ℂ)‖ + ‖ascTransform (driftStep ρW μ) (cexp (-q)) ζ‖ := norm_sub_le _ _
        _ ≤ 1 + Mp := by rw [norm_one]; linarith
    have hΦ : ‖dom.identΦ ρW μ q ζ‖ ≤ KΦ := by
      have h := dom.norm_lineCauchy_logF_le hW hθ hD (by linarith) le_rfl hμ hq (ζ := ζ)
        (by linarith)
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hCL)
      have habs : dom.c₀ / 2 ≤ |2 * dom.c₀ - ζ.re| := by
        rw [abs_of_pos (by linarith)]; linarith
      have : 1 / (2 * |2 * dom.c₀ - ζ.re|) ≤ 1 / dom.c₀ :=
        one_div_le_one_div_of_le hc0 (by linarith)
      linarith
    have hexp : ‖cexp (-dom.identΦ ρW μ q ζ)‖ ≤ Real.exp KΦ :=
      (norm_cexp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by rw [norm_neg]; exact hΦ))
    have h1ζ : ‖((1 : ℝ) : ℂ) - ζ‖ ≤ (1 + 8 / dom.c₀) * ‖βp - ζ‖ := by
      have h1 : ‖((1 : ℝ) : ℂ) - βp‖ ≤ 2 := by
        rw [ofReal_one]; exact (norm_sub_le _ _).trans (by simp; linarith)
      have h2 : 2 ≤ 8 / dom.c₀ * ‖βp - ζ‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc0]; rw [norm_sub_rev] at hd; nlinarith
      calc ‖((1 : ℝ) : ℂ) - ζ‖ = ‖(((1 : ℝ) : ℂ) - βp) + (βp - ζ)‖ := by ring_nf
        _ ≤ ‖((1 : ℝ) : ℂ) - βp‖ + ‖βp - ζ‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have hMp0 : 0 ≤ Mp := by
      rw [hMp, expEntryMass]
      exact integral_nonneg fun _ => (Real.exp_pos _).le
    calc ‖1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ‖ *
          (‖cexp (-dom.identΦ ρW μ q ζ)‖ * ‖((1 : ℝ) : ℂ) - ζ‖)
        ≤ (1 + Mp) * (Real.exp KΦ * ((1 + 8 / dom.c₀) * ‖βp - ζ‖)) := by
          gcongr
      _ = CL' * ‖βp - ζ‖ := by rw [hCL']; ring
  -- the compact disc
  have hsub : closedBall βp (dom.c₀ / 4) ⊆ {w : ℂ | w.re < 2 * dom.c₀} := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    show w.re < 2 * dom.c₀
    have h1 := re_le_norm (w - βp)
    have h2 := re_le_norm βp
    rw [sub_re] at h1
    linarith
  obtain ⟨CK, hCK⟩ := (isCompact_closedBall βp (dom.c₀ / 4)).exists_bound_of_continuousOn
    (f := dom.identEL ρW μ q) (fun w hw =>
      (dom.differentiableAt_identEL hW hθ hD hμ hq0 hq (hsub hw)).continuousAt.continuousWithinAt)
  refine ⟨max (max CR CL') CK, fun ζ => ?_⟩
  by_cases h1 : 3 * dom.c₀ / 2 ≤ ζ.re
  · exact (hRb ζ h1).trans ((le_max_left _ _).trans (le_max_left _ _))
  · push Not at h1
    by_cases h2 : dom.c₀ / 4 ≤ ‖ζ - βp‖
    · exact (hLb ζ h1.le h2).trans ((le_max_right _ _).trans (le_max_left _ _))
    · push Not at h2
      have hmem : ζ ∈ closedBall βp (dom.c₀ / 4) := by
        rw [mem_closedBall, dist_eq_norm]; exact h2.le
      rw [dom.identE_eq_EL ρW μ q (hsub hmem)]
      exact (hCK ζ hmem).trans (le_max_right _ _)

/-- `identE(t) → 1` as real `t → -∞`. -/
theorem tendsto_identE_atBot : Tendsto (fun t : ℝ => dom.identE ρW μ q t) atBot (𝓝 1) := by
  have := hW.isProbabilityMeasure
  have hc0 := dom.c₀_pos
  have hrep := (dom.re_roots hW hθ hD hμ hq0 hq).1
  set βp := cepsRootPlus D θ ρW μ q with hβp
  have h1 : Tendsto (fun t : ℝ => 1 - ascTransform (driftStep ρW μ) (cexp (-q)) t) atBot
      (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_asc_atBot _ (norm_cexp_neg_le_one hq0.le))
  have h0 : (0 : ℂ).re ≠ 2 * dom.c₀ := by simp; linarith
  have hΦ : Tendsto (fun t : ℝ => dom.identΦ ρW μ q t) atBot (𝓝 ((2 * Real.pi : ℂ)⁻¹ * 0)) :=
    (tendsto_lineCauchy_atBot h0 (dom.integrable_logFLine hW hθ hD (by linarith) le_rfl hμ hq
      h0)).const_mul _
  rw [mul_zero] at hΦ
  have h2 : Tendsto (fun t : ℝ => cexp (-dom.identΦ ρW μ q t)) atBot (𝓝 (cexp (-0))) :=
    (Complex.continuous_exp.tendsto _).comp hΦ.neg
  rw [neg_zero, Complex.exp_zero] at h2
  have h3 : Tendsto (fun t : ℝ => (1 - βp) / (βp - t)) atBot (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => ‖1 - βp‖ / (-t)) atBot (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_neg_atBot_atTop
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_lt_atBot 0] with t ht
    rw [norm_div]
    refine div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) ?_
    have := re_le_norm (βp - (t : ℂ))
    rw [sub_re, ofReal_re] at this
    linarith
  have h4 := (h1.mul h2).mul ((tendsto_const_nhds (x := (1 : ℂ))).add h3)
  rw [sub_zero, mul_one, add_zero, mul_one] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with t ht
  have ht2 : (t : ℂ).re < 2 * dom.c₀ := by rw [ofReal_re]; linarith
  have hne : (t : ℂ) ≠ βp := by
    intro h; have := congrArg re h; rw [ofReal_re] at this; linarith
  have hβt : βp - (t : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  rw [dom.identE_eq_EL ρW μ q ht2, dom.identEL_eq hW hθ hD hμ hq0 hq hne, identP,
    dom.cexp_neg_canonL₂ ρW μ q ht2, ofReal_one, ← hβp]
  field_simp
  ring

theorem identE_eq_one (ζ : ℂ) : dom.identE ρW μ q ζ = 1 := by
  obtain ⟨C, hC⟩ := dom.exists_bound_identE hW hθ hD hμ hq0 hq
  have hb : IsBounded (range (dom.identE ρW μ q)) :=
    isBounded_iff_forall_norm_le.mpr ⟨C, by rintro _ ⟨z, rfl⟩; exact hC z⟩
  have hconst : ∀ z, dom.identE ρW μ q z = dom.identE ρW μ q 0 := fun z =>
    (dom.differentiable_identE hW hθ hD hμ hq0 hq).apply_eq_apply_of_bounded hb z 0
  have hlim := dom.tendsto_identE_atBot hW hθ hD hμ hq0 hq
  have hlim' : Tendsto (fun t : ℝ => dom.identE ρW μ q t) atBot
      (𝓝 (dom.identE ρW μ q 0)) := by
    simp only [hconst]; exact tendsto_const_nhds
  rw [hconst ζ]
  exact tendsto_nhds_unique hlim' hlim

/-- **C-5 for `Re q > 0`, abscissa `2c₀`.** -/
theorem one_sub_asc_eq_of_re_pos {ζ : ℂ} (hζ : ζ.re < 2 * dom.c₀) :
    1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ =
      (cepsRootPlus D θ ρW μ q - ζ) * cexp (cepsCanonL D θ ρW 1 (2 * dom.c₀) μ q ζ) := by
  by_cases hζp : ζ = cepsRootPlus D θ ρW μ q
  · rw [hζp, dom.one_sub_asc_rootPlus hW hθ hD hμ hq0 hq, sub_self, zero_mul]
  · have hβζ : cepsRootPlus D θ ρW μ q - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζp)
    have h1 := dom.identE_eq_one hW hθ hD hμ hq0 hq ζ
    rw [dom.identE_eq_EL ρW μ q hζ, dom.identEL_eq hW hθ hD hμ hq0 hq hζp,
      div_eq_one_iff_eq hβζ, identP] at h1
    calc 1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ
        = (1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ) *
            cexp (-cepsCanonL D θ ρW 1 (2 * dom.c₀) μ q ζ) *
              cexp (cepsCanonL D θ ρW 1 (2 * dom.c₀) μ q ζ) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = _ := by rw [h1]

/-- **C-5 for `Re q > 0`.** `1 - A₊(ζ) = (β₊ - ζ) e^{L(ζ)}` for `Re ζ < c₀`. -/
theorem one_sub_asc_eq_canonL_of_re_pos {ζ : ℂ} (hζ : ζ.re < dom.c₀) :
    1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ =
      (cepsRootPlus D θ ρW μ q - ζ) * cexp (dom.canonL ρW μ q ζ) := by
  have hc0 := dom.c₀_pos
  rw [dom.one_sub_asc_eq_of_re_pos hW hθ hD hμ hq0 hq (by linarith), canonL,
    dom.cepsCanonL_eq_of_abscissa hW hθ hD (γ := 1) (by norm_num) le_rfl le_rfl (by linarith)
      le_rfl (dom.norm_ofReal_le_μ₀ hμ) (by simp) hq hζ]

end

end CepsCanonDomain

end PGM
