import PLAStochastic.Index.CEPS.Ident.LiouvilleMain
import PLAStochastic.Index.CEPS.Ident.Statement
import PLAStochastic.Index.CEPS.Ident.CorollariesQ

/-!
# CEPS WP4, lemma C-5: the Wiener–Hopf identification on `𝔇₊`

* `one_sub_asc_eq_canonL`: `1 - A₊(ζ) = (β₊ - ζ) e^{L(ζ)}` for `Re ζ < c₀` on all of `𝔇₊`
  (`Re q = 0` by continuity from `q_n = (1 - εₙ) q + εₙ² q₀`, `εₙ = 1/(n+1)`);
* the removed-root quotient `Q = cepsQ`: `cepsQ_eq_quotA` (`Q = Q_A` on `B(0, ρA)`),
  `neg_cepsD_eq_mul_cepsQ` (`-d = (ζ - β₊)(ζ - β₋) Q` everywhere), `cepsQ_ne_zero` on the strip
  `|Re ζ| ≤ 2c₀`, `cexp_canonL_add_canonLMinus` (`e^{L + L₋} = Q`, blueprint (3.4));
* `one_sub_desc_eq`: `1 - A₋(ζ) = (ζ - β₋) e^{L₋(ζ)}` for `|Re ζ| < c₀`;
* **`cepsWHIdent`**: the frozen statement `CepsWHIdent dom ρW`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf
open scoped ENNReal

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

variable {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
include hμ

/-- **C-5, ascending factor, on `𝔇₊`.** -/
theorem one_sub_asc_eq_canonL {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) {ζ : ℂ}
    (hζ : ζ.re < dom.c₀) :
    1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ =
      (cepsRootPlus D θ ρW μ q - ζ) * cexp (dom.canonL ρW μ q ζ) := by
  rcases lt_or_eq_of_le hq0 with hpos | hzero
  · exact dom.one_sub_asc_eq_canonL_of_re_pos hW hθ hD hμ hpos hq hζ
  have := hW.isProbabilityMeasure
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hq₀ := dom.q₀_pos
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  -- the approximating discounts
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hε0 : ∀ n, 0 < ε n := fun n => by simp only [hε]; positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    simp only [hε]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set Q : ℕ → ℂ := fun n => ((1 - ε n : ℝ) : ℂ) * q + ((dom.q₀ * ε n ^ 2 : ℝ) : ℂ) with hQ
  have hQre : ∀ n, 0 < (Q n).re := by
    intro n
    simp only [hQ, add_re, re_ofReal_mul, ofReal_re, ← hzero, mul_zero, zero_add]
    have := hε0 n; positivity
  have hQn : ∀ n, ‖Q n‖ ≤ dom.q₀ := by
    intro n
    have h1 := hε0 n
    have h2 := hε1 n
    calc ‖Q n‖ ≤ ‖((1 - ε n : ℝ) : ℂ) * q‖ + ‖((dom.q₀ * ε n ^ 2 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = (1 - ε n) * ‖q‖ + dom.q₀ * ε n ^ 2 := by
          rw [norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), abs_of_nonneg (by positivity)]
      _ ≤ (1 - ε n) * dom.q₀ + dom.q₀ * ε n := by
          exact add_le_add (mul_le_mul_of_nonneg_left hq (by linarith))
            (mul_le_mul_of_nonneg_left (by nlinarith : ε n ^ 2 ≤ ε n) hq₀.le)
      _ = dom.q₀ := by ring
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hQlim : Tendsto Q atTop (𝓝 q) := by
    have h1 : Tendsto (fun n => ((1 - ε n : ℝ) : ℂ)) atTop (𝓝 ((1 - 0 : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub hεlim)
    have h2 : Tendsto (fun n => ((dom.q₀ * ε n ^ 2 : ℝ) : ℂ)) atTop
        (𝓝 ((dom.q₀ * 0 ^ 2 : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto _).comp (tendsto_const_nhds.mul (hεlim.pow 2))
    have h3 := (h1.mul_const q).add h2
    simpa only [hQ, ofReal_sub, ofReal_one, ofReal_zero, sub_zero, one_mul, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, add_zero, ofReal_mul, ofReal_pow] using h3
  have hQmem : ∀ n, Q n ∈ {q : ℂ | 0 ≤ q.re} := fun n => (hQre n).le
  -- limits of both sides
  have hL : Tendsto (fun n => 1 - ascTransform (driftStep ρW μ) (cexp (-Q n)) ζ) atTop
      (𝓝 (1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ)) := by
    have hc := dom.continuousOn_asc_q hW hθ hD hμ (ζ := ζ) (by linarith) q hq0
    exact tendsto_const_nhds.sub (hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hQlim, Eventually.of_forall hQmem⟩))
  have hm : 0 ≤ (q - cepsMorseMin D θ ρW μ).re := by
    rw [sub_re, ← hzero]
    linarith [re_cepsMorseMin_nonpos hW hθ hD (dom.μ_lt_chart hμ')]
  have hβ := (dom.continuousAt_roots hW hθ hD hμ hq hm).1
  have hcL := dom.continuousOn_canonL_q hW hθ hD le_rfl (by linarith) hμ hζ q
    (mem_closedBall_zero_iff.mpr hq)
  have hR : Tendsto (fun n => (cepsRootPlus D θ ρW μ (Q n) - ζ) *
      cexp (dom.canonL ρW μ (Q n) ζ)) atTop
      (𝓝 ((cepsRootPlus D θ ρW μ q - ζ) * cexp (dom.canonL ρW μ q ζ))) := by
    have h1 := (hβ.tendsto.comp hQlim).sub_const ζ
    have h2 : Tendsto (fun n => dom.canonL ρW μ (Q n) ζ) atTop (𝓝 (dom.canonL ρW μ q ζ)) :=
      hcL.tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨hQlim, Eventually.of_forall fun n => mem_closedBall_zero_iff.mpr (hQn n)⟩)
    exact h1.mul ((Complex.continuous_exp.tendsto _).comp h2)
  refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
  exact (dom.one_sub_asc_eq_canonL_of_re_pos hW hθ hD hμ (hQre n) (hQn n) hζ).symm

/-! ### The removed-root quotient `Q` -/

variable {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
include hq

omit hW hμ hq in
theorem ρA_lt_r0 : dom.ρA < cepsCgfRadius D θ := by
  have := dom.ρA_R; have := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have := cepsCgfRadius_pos hD hθ; have := dom.ρA_pos; linarith

/-- The removed quotient identities reuse the compiled C-6 algebra. -/
theorem dslope_negD_eq {z : ℂ} (hz : ‖z‖ < dom.ρA) :
    dslope (fun z => -cepsD ρW μ q z) (cepsRootPlus D θ ρW μ q) z =
      (z - cepsRootMinus D θ ρW μ q) * cepsQuotA D θ ρW μ q z :=
  CepsC6.dslope_negD_eq dom hW hθ hD (dom.norm_ofReal_le_μ₀ hμ) hq
    (mem_ball_zero_iff.mpr hz)

theorem dslope_negD_rootMinus :
    dslope (fun z => -cepsD ρW μ q z) (cepsRootPlus D θ ρW μ q)
      (cepsRootMinus D θ ρW μ q) = 0 := by
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  have hbm := dom.norm_rootMinus_le hW hθ hD hμ' hq
  have := dom.ρA_pos; have := dom.c₀_le; have := dom.c₀_pos
  rw [dom.dslope_negD_eq hW hθ hD hμ hq (by linarith), sub_self, zero_mul]

/-- `Q = Q_A` on the complete root disc, including both roots. -/
theorem cepsQ_eq_quotA {z : ℂ} (hz : ‖z‖ < dom.ρA) :
    cepsQ D θ ρW μ q z = cepsQuotA D θ ρW μ q z :=
  CepsC6.cepsQ_eq_cepsQuotA dom hW hθ hD (dom.norm_ofReal_le_μ₀ hμ) hq
    (mem_ball_zero_iff.mpr hz)

/-- `-d = (ζ - β₊)(ζ - β₋) Q` everywhere. -/
theorem neg_cepsD_eq_mul_cepsQ (ζ : ℂ) :
    -cepsD ρW μ q ζ = (ζ - cepsRootPlus D θ ρW μ q) * (ζ - cepsRootMinus D θ ρW μ q) *
      cepsQ D θ ρW μ q ζ := by
  have hdp : cepsD ρW μ q (cepsRootPlus D θ ρW μ q) = 0 := dom.cepsD_rootPlus hW hθ hD hμ hq
  have hgm := dom.dslope_negD_rootMinus hW hθ hD hμ hq
  have h1 := sub_smul_dslope (fun z => -cepsD ρW μ q z) (cepsRootPlus D θ ρW μ q) ζ
  have h2 := sub_smul_dslope (dslope (fun z => -cepsD ρW μ q z) (cepsRootPlus D θ ρW μ q))
    (cepsRootMinus D θ ρW μ q) ζ
  rw [hgm, sub_zero, smul_eq_mul] at h2
  rw [hdp, neg_zero, sub_zero, smul_eq_mul] at h1
  unfold cepsQ
  rw [mul_assoc, h2, h1]

/-- `Q ≠ 0` on the strip `|Re ζ| ≤ 2c₀`. -/
theorem cepsQ_ne_zero {ζ : ℂ} (hζ : |ζ.re| ≤ 2 * dom.c₀) : cepsQ D θ ρW μ q ζ ≠ 0 := by
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  rcases lt_or_ge ‖ζ‖ dom.ρA with hz | hz
  · rw [dom.cepsQ_eq_quotA hW hθ hD hμ hq hz]
    exact dom.cepsQuotA_ne_zero hW hθ hD hμ' hq hz.le
  · intro h0
    have hbp := dom.norm_rootPlus_le hW hθ hD hμ' hq
    have hbm := dom.norm_rootMinus_le hW hθ hD hμ' hq
    have := dom.c₀_le; have := dom.c₀_pos
    have hd := dom.neg_cepsD_eq_mul_cepsQ hW hθ hD hμ hq ζ
    rw [h0, mul_zero, neg_eq_zero] at hd
    rcases (dom.cepsD_eq_zero_iff hW hθ hD hμ' (by simp; exact dom.η_pos.le) hq hζ).mp hd
      with h | h <;> rw [h] at hz <;> linarith

/-- **Blueprint (3.4).** `e^{L + L₋} = Q` on the strip. -/
theorem cexp_canonL_add_canonLMinus {ζ : ℂ} (hζ : |ζ.re| ≤ 2 * dom.c₀) :
    cexp (dom.canonL ρW μ q ζ + dom.canonLMinus ρW μ q ζ) = cepsQ D θ ρW μ q ζ := by
  rw [canonLMinus, add_sub_cancel, Complex.exp_log (dom.cepsQ_ne_zero hW hθ hD hμ hq hζ)]

theorem continuousAt_canonL {ζ : ℂ} (hζ : ζ.re < dom.c₀) :
    ContinuousAt (dom.canonL ρW μ q) ζ := by
  have hc0 := dom.c₀_pos
  have hc1 := dom.c₀_le_small
  have h1 := dom.differentiableAt_lineCauchy_logF hW hθ hD le_rfl (by linarith) hμ hq
    (ζ := ζ) hζ.ne
  have h2 : DifferentiableAt ℂ (fun ζ : ℂ => Complex.log (((1 : ℝ) : ℂ) - ζ)) ζ :=
    ((differentiableAt_const _).sub differentiableAt_id).clog (by left; simp; linarith)
  have h : DifferentiableAt ℂ (fun ζ => cepsCanonL D θ ρW 1 dom.c₀ μ q ζ) ζ :=
    (h1.const_mul _).sub h2
  exact h.continuousAt

/-- **C-5, descending factor.** `1 - A₋(ζ) = (ζ - β₋) e^{L₋(ζ)}` for `|Re ζ| < c₀`. -/
theorem one_sub_desc_eq (hq0 : 0 ≤ q.re) {ζ : ℂ} (hζ : |ζ.re| < dom.c₀) :
    1 - descTransform (driftStep ρW μ) (cexp (-q)) ζ =
      (ζ - cepsRootMinus D θ ρW μ q) * cexp (dom.canonLMinus ρW μ q ζ) := by
  have := hW.isProbabilityMeasure
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  set βp := cepsRootPlus D θ ρW μ q with hβp
  set βm := cepsRootMinus D θ ρW μ q with hβm
  -- the identity off `β₊`, in the form `1 - A₋ = (ζ - β₋) Q e^{-L}`
  set f : ℂ → ℂ := fun ζ => 1 - descTransform (driftStep ρW μ) (cexp (-q)) ζ -
    (ζ - βm) * cepsQ D θ ρW μ q ζ * cexp (-dom.canonL ρW μ q ζ) with hf
  have hzero : ∀ z : ℂ, |z.re| < dom.c₀ → z ≠ βp → f z = 0 := by
    intro z hz hzp
    have hzre : z.re < dom.c₀ := (le_abs_self _).trans_lt hz
    have hA := dom.one_sub_asc_eq_canonL hW hθ hD hμ hq0 hq hzre
    have hWH := dom.wienerHopf_cepsD hW hθ hD hμ hq0 (ζ := z) (by linarith)
    have hd := dom.neg_cepsD_eq_mul_cepsQ hW hθ hD hμ hq z
    rw [hA] at hWH
    have hβz : βp - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzp)
    have hE : cexp (dom.canonL ρW μ q z) * cexp (-dom.canonL ρW μ q z) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have key : (βp - z) * (1 - descTransform (driftStep ρW μ) (cexp (-q)) z -
        (z - βm) * cepsQ D θ ρW μ q z * cexp (-dom.canonL ρW μ q z)) = 0 := by
      linear_combination cexp (-dom.canonL ρW μ q z) * hWH - cexp (-dom.canonL ρW μ q z) * hd +
        -(βp - z) * (1 - descTransform (driftStep ρW μ) (cexp (-q)) z) * hE
    simp only [hf]
    exact (mul_eq_zero.mp key).resolve_left hβz
  have hf0 : f ζ = 0 := by
    by_cases hζp : ζ = βp
    · -- continuity at `β₊`
      have hbp := dom.norm_rootPlus_le hW hθ hD hμ' hq
      have hρ : ‖βp‖ < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
      have hcont : ContinuousAt f βp := by
        have h1 : ContinuousAt (fun ζ => descTransform (driftStep ρW μ) (cexp (-q)) ζ) βp := by
          have hre : -(θ / 2) < βp.re := by
            have := abs_re_le_norm βp; have := neg_abs_le βp.re; linarith
          exact ((dom.differentiableOn_desc hW hθ hD hμ (norm_cexp_neg_le_one hq0) βp
            hre).differentiableAt
            ((isOpen_lt continuous_const continuous_re).mem_nhds hre)).continuousAt
        have h2 : ContinuousAt (cepsQ D θ ρW μ q) βp := by
          have hev : cepsQ D θ ρW μ q =ᶠ[𝓝 βp] cepsQuotA D θ ρW μ q := by
            filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hρ)] with w hw
            exact dom.cepsQ_eq_quotA hW hθ hD hμ hq (mem_ball_zero_iff.mp hw)
          have hr0 := dom.ρA_lt_r0 hθ hD
          exact ((dom.differentiableOn_cepsQuotA hW hθ hD hμ' hq βp
            (mem_ball_zero_iff.mpr (by linarith))).differentiableAt
            (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by linarith)))).continuousAt.congr
              hev.symm
        have h3 := dom.continuousAt_canonL hW hθ hD hμ hq (ζ := βp)
          (by have := re_le_norm βp; linarith)
        exact (continuousAt_const.sub h1).sub
          (((continuousAt_id.sub continuousAt_const).mul h2).mul h3.neg.cexp)
      have hev : f =ᶠ[𝓝[≠] βp] fun _ => 0 := by
        have hU : {w : ℂ | |w.re| < dom.c₀} ∈ 𝓝 βp :=
          (isOpen_lt (continuous_abs.comp continuous_re) continuous_const).mem_nhds
            (by show |βp.re| < dom.c₀; have := abs_re_le_norm βp; linarith)
        filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with w hw hwne
        exact hzero w hw hwne
      rw [hζp]
      exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
        (tendsto_const_nhds.congr' hev.symm)
    · exact hzero ζ hζ hζp
  have hQne := dom.cepsQ_ne_zero hW hθ hD hμ hq (ζ := ζ) (by linarith)
  have hLminus : cexp (dom.canonLMinus ρW μ q ζ) =
      cepsQ D θ ρW μ q ζ * cexp (-dom.canonL ρW μ q ζ) := by
    rw [canonLMinus, sub_eq_add_neg, Complex.exp_add, Complex.exp_log hQne]
  rw [hLminus]
  simp only [hf] at hf0
  linear_combination hf0

end

/-- **C-5 (lemma).** The frozen statement `CepsWHIdent` holds for every class step law. -/
theorem cepsWHIdent (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D) :
    CepsWHIdent dom ρW := fun _μ hμ _q hq0 hq =>
  ⟨fun _ζ hζ => dom.one_sub_asc_eq_canonL hW hθ hD hμ hq0 hq hζ,
    fun _ζ hζ => dom.one_sub_desc_eq hW hθ hD hμ hq hq0 hζ⟩

end CepsCanonDomain

end PGM
