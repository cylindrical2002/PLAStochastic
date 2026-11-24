import PLAStochastic.Index.CEPS.StripError.ExitIdentity

/-!
# WP9, S-3: the exit-transform error

Solving the two exact exit equations of `StripError.ExitIdentity` at the roots `s = β∓`
gives `x = 1 - u_{β₋}` with `(x - x̂) Δ = B₊(η) E₂(β₊) + E₁(β₋)`. Both remainders carry the
vanishing factor `|η|`, and `|η| ≤ (8 K / c_s) |Δ|` from `|Δ| ≥ (c_s/4) min(1, |r₊| l)` and
`|η| ≤ 2K |r₊|`; hence `|x - x̂| ≤ C e^{-c₀ l/4}` uniformly, including near merging roots.
Substituting back gives the class-uniform exit error
`|u_t - û_t| + |ℓ_t - ℓ̂_t| ≤ K e^{-c₀ l/4}` for imaginary marks `t` (`strip_exit_error_WH`,
`strip_exit_error`), for every non-merged point `r₊ ≠ 0` of the closed discount half-disc.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Complex Metric
open WienerHopf

namespace CepsCanonDomain

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v)

/-- `|η| ≤ stripEtaDelta · |Δ|`. -/
def stripEtaDelta : ℝ := 8 * cepsChartK D / dom.normalSectorConst

/-- Bound for `e^{L(z) - L(w)}` on the root disc. -/
def stripBplus : ℝ := Real.exp (2 * dom.normalLogBound)

/-- Bound for `e^{L₋(z) - L₋(w)}` on the root disc. -/
def stripBminus : ℝ := v / (cepsVarLo D / 4) * Real.exp (2 * dom.normalLogBound)

def stripXConst : ℝ := (2 * dom.stripBplus + 1) * dom.stripRewardConst * dom.stripEtaDelta

def stripYConst : ℝ := dom.stripBminus * dom.stripXConst + 2 * dom.stripRewardConst * (dom.c₀ / 2)

/-- The class constant of the exit error. -/
def stripExitConst : ℝ :=
  dom.stripBplus * dom.stripYConst + dom.stripRewardConst * (dom.c₀ / 2) +
    (dom.stripBminus * dom.stripXConst + 2 * dom.stripRewardConst * (dom.c₀ / 2))

end CepsCanonDomain

/-- Pure algebra of the reduced system. -/
theorem strip_exit_algebra {x xh ℓp yh Λ Bp Bm E Δ e1 e2 : ℂ}
    (hΔ : Δ = 1 - E * (Bp * Bm)) (hΔ0 : Δ ≠ 0) (hxh : xh = Λ / Δ) (hyh : yh = E * Bm * xh)
    (hx : x = Λ + Bp * ℓp + e1) (hℓ : ℓp = E * Bm * x + e2) :
    (x - xh) * Δ = Bp * e2 + e1 ∧ ℓp - yh = E * Bm * (x - xh) + e2 := by
  constructor
  · rw [hxh, sub_mul, div_mul_cancel₀ _ hΔ0, hΔ]
    rw [hℓ] at hx
    linear_combination hx
  · rw [hℓ, hyh]
    ring

variable {ρ : Measure ℝ} {fρ : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρ fρ D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem norm_canonL_le_logBound {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {z : ℂ} (hz : ‖z‖ ≤ dom.c₀ / 2) : ‖dom.canonL ρ μ q z‖ ≤ dom.normalLogBound := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  exact dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ' (ofReal_im μ) hq hz

theorem norm_cexp_le_exp_norm (z : ℂ) : ‖cexp z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (re_le_norm z)

include hW hθ hD in
theorem norm_cexp_canonL_sub_le {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {z w : ℂ} (hz : ‖z‖ ≤ dom.c₀ / 2) (hw : ‖w‖ ≤ dom.c₀ / 2) :
    ‖cexp (dom.canonL ρ μ q z - dom.canonL ρ μ q w)‖ ≤ dom.stripBplus := by
  refine (norm_cexp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
  have h1 := norm_canonL_le_logBound dom hW hθ hD hμ hq hz
  have h2 := norm_canonL_le_logBound dom hW hθ hD hμ hq hw
  calc _ ≤ ‖dom.canonL ρ μ q z‖ + ‖dom.canonL ρ μ q w‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

theorem c₀_half_lt_ρA {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : dom.c₀ / 2 < dom.ρA := by
  have := dom.c₀_le; have := dom.c₀_pos; have := dom.ρA_pos; linarith

include hW hθ hD in
theorem norm_cexp_canonLMinus_sub_le {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {z w : ℂ} (hz : ‖z‖ ≤ dom.c₀ / 2) (hw : ‖w‖ ≤ dom.c₀ / 2) :
    ‖cexp (dom.canonLMinus ρ μ q z - dom.canonLMinus ρ μ q w)‖ ≤ dom.stripBminus := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hρ := c₀_half_lt_ρA dom
  have hQzlo := cepsQ_norm_ge_on_rootZone dom hW hθ hD hμ' hq (lt_of_le_of_lt hz hρ)
  have hQwlo := cepsQ_norm_ge_on_rootZone dom hW hθ hD hμ' hq (lt_of_le_of_lt hw hρ)
  have hQzhi := cepsQ_norm_le_on_rootZone dom hW hθ hD hμ' hq (lt_of_le_of_lt hz hρ)
  have hvl := cepsVarLo_pos hD
  have hQz : cepsQ D θ ρ μ q z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hQw : cepsQ D θ ρ μ q w ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : cexp (dom.canonLMinus ρ μ q z - dom.canonLMinus ρ μ q w) =
      cepsQ D θ ρ μ q z / cepsQ D θ ρ μ q w *
        cexp (dom.canonL ρ μ q w - dom.canonL ρ μ q z) := by
    unfold CepsCanonDomain.canonLMinus
    rw [show Complex.log (cepsQ D θ ρ μ q z) - dom.canonL ρ μ q z -
        (Complex.log (cepsQ D θ ρ μ q w) - dom.canonL ρ μ q w) =
        (Complex.log (cepsQ D θ ρ μ q z) - Complex.log (cepsQ D θ ρ μ q w)) +
          (dom.canonL ρ μ q w - dom.canonL ρ μ q z) by ring,
      Complex.exp_add, Complex.exp_sub, Complex.exp_log hQz, Complex.exp_log hQw]
  rw [he, norm_mul, norm_div]
  have hB := norm_cexp_canonL_sub_le dom hW hθ hD hμ hq hw hz
  unfold CepsCanonDomain.stripBminus
  unfold CepsCanonDomain.stripBplus at hB
  have hQwpos : 0 < ‖cepsQ D θ ρ μ q w‖ := by linarith
  calc _ ≤ v / (cepsVarLo D / 4) * Real.exp (2 * dom.normalLogBound) :=
        mul_le_mul (div_le_div₀ (by have := CepsCanonDomain.v_pos hW hθ hD; linarith)
          hQzhi (by positivity) hQwlo) hB (norm_nonneg _)
          (by have := CepsCanonDomain.v_pos hW hθ hD; positivity)

include hW hθ hD in
theorem strip_eta_le_delta {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    (hq0 : 0 ≤ q.re) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    ‖cepsRootPlus D θ ρ μ q - cepsRootMinus D θ ρ μ q‖ ≤
      dom.stripEtaDelta * ‖(cepsWHNormalData D θ ρ μ q).delta (dom.canonL ρ) μ q l‖ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hη := cepsRoots_difference_norm_le hW hθ hD dom hμ' hq
  have hΔ := cepsNormal_actual_delta_lower_bound dom hW hθ hD hμ hq hq0 hl
  have hr := dom.norm_cepsRootR_le hW hθ hD hμ' hq
  have hr1 := dom.rmax_one
  have hcs := cepsNormal_sectorConst_pos dom hW hθ hD
  have hK := cepsChartK_pos hD
  obtain ⟨hl0, hlb, -⟩ := cepsNormal_width_properties dom hW hθ hD hl
  have hl1 : 1 ≤ l := by
    have := cepsNormal_budget_nonneg dom hθ hD
    have h1 := (le_max_left (dom.normalDerivativeBudget + 1)
      (2 * dom.normalPiRootBound / dom.normalSectorConst)).trans hl
    linarith
  set R := ‖cepsRootR D θ ρ μ q‖ with hR
  have hmin : R ≤ min 1 (R * l) := le_min (hr.trans hr1) (by nlinarith [norm_nonneg (cepsRootR D θ ρ μ q)])
  unfold CepsCanonDomain.stripEtaDelta
  calc _ ≤ 2 * cepsChartK D * R := hη
    _ ≤ 2 * cepsChartK D * min 1 (R * l) := by gcongr
    _ = 8 * cepsChartK D / dom.normalSectorConst *
        (dom.normalSectorConst / 4 * min 1 (R * l)) := by field_simp; ring
    _ ≤ _ := by gcongr

/-! ## The exit error for the root-zone normal data `cepsWHNormalData` -/

include hW hθ hD in
theorem strip_exit_error_WH (ν : ProbabilityMeasure ℝ) (β a : ℝ) {μ : ℝ}
    (hlink : (ν : Measure ℝ).map (fun x => a * x - β) = driftStep ρ μ)
    (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount)
    (hr : cepsRootR D θ ρ μ q ≠ 0) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l)
    {t : ℂ} (ht : t.re = 0) (htn : ‖t‖ ≤ dom.c₀ / 2 / 2) :
    ‖cepsStripExit ν β a l 0 (Iio 0) (-t) q -
        (cepsWHNormalData D θ ρ μ q).upperExit (dom.canonL ρ) μ q t l‖ +
      ‖cepsStripExit ν β a l 0 (Ioi l) (-t) q -
        (cepsWHNormalData D θ ρ μ q).lowerExit (dom.canonL ρ) μ q t l‖ ≤
      dom.stripExitConst * Real.exp (-(dom.c₀ / 2 / 2) * l) := by
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  have hq0' : ‖q‖ ≤ dom.q₀ := hq.trans (min_le_left _ _)
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  obtain ⟨hl0, -, -⟩ := cepsNormal_width_properties dom hW hθ hD hl
  have hc0 := dom.c₀_pos
  set A := cepsWHNormalData D θ ρ μ q with hAdef
  set L := dom.canonL ρ with hLdef
  set βp := cepsRootPlus D θ ρ μ q with hβp
  set βm := cepsRootMinus D θ ρ μ q with hβm
  have hAp : A.βp = βp := rfl
  have hAm : A.βm = βm := rfl
  have hβpn : ‖βp‖ ≤ dom.c₀ / 4 := dom.norm_rootPlus_le hW hθ hD hμ' hq0'
  have hβmn : ‖βm‖ ≤ dom.c₀ / 4 := dom.norm_rootMinus_le hW hθ hD hμ' hq0'
  have hβpn' : ‖βp‖ ≤ dom.c₀ / 2 / 2 := by linarith
  have hβmn' : ‖βm‖ ≤ dom.c₀ / 2 / 2 := by linarith
  have hβpn2 : ‖βp‖ ≤ dom.c₀ / 2 := by linarith
  have hβmn2 : ‖βm‖ ≤ dom.c₀ / 2 := by linarith
  have htn2 : ‖t‖ ≤ dom.c₀ / 2 := by linarith
  obtain ⟨hsp, hsm⟩ := cepsRoots_re_signs dom hW hθ hD hμ0 hq0 hq0'
  -- the four exit equations
  have hIm := strip_upper_identity dom hW hθ hD ν β a hlink hμ hq0 hq hl0.le (s := βm) hsm hβmn'
  have hIIp := strip_lower_identity dom hW hθ hD ν β a hlink hμ hq0 hq hl0.le (s := βp) hsp hβpn'
  have hIt := strip_upper_identity dom hW hθ hD ν β a hlink hμ hq0 hq hl0.le (s := t)
    (by rw [ht]) htn
  have hIIt := strip_lower_identity dom hW hθ hD ν β a hlink hμ hq0 hq hl0.le (s := t)
    (by rw [ht]) htn
  -- the normal quantities
  have hρ := c₀_half_lt_ρA dom
  have hQp : A.Q A.βp ≠ 0 := by
    have h := cepsQ_norm_ge_on_rootZone dom hW hθ hD hμ' hq0' (lt_of_le_of_lt hβpn2 hρ)
    have hv := cepsVarLo_pos hD
    have h' : 0 < ‖A.Q A.βp‖ := lt_of_lt_of_le (by positivity) h
    exact norm_pos_iff.mp h'
  have hQm : A.Q A.βm ≠ 0 := by
    have h := cepsQ_norm_ge_on_rootZone dom hW hθ hD hμ' hq0' (lt_of_le_of_lt hβmn2 hρ)
    have hv := cepsVarLo_pos hD
    have h' : 0 < ‖A.Q A.βm‖ := lt_of_lt_of_le (by positivity) h
    exact norm_pos_iff.mp h'
  set Bp := A.overshootPlus L μ q A.eta with hBpdef
  set Bm := A.overshootMinus L μ q A.eta with hBmdef
  set E := A.decay l with hEdef
  set Δ := A.delta L μ q l with hΔdef
  have hBp : Bp = cexp (L μ q βm - L μ q βp) := by
    rw [hBpdef]
    unfold CepsNormalData.overshootPlus CepsNormalData.eta
    rw [hAp, hAm, sub_sub_cancel]
  have hBm : Bm = cexp (dom.canonLMinus ρ μ q βp - dom.canonLMinus ρ μ q βm) := by
    rw [hBmdef]
    unfold CepsNormalData.overshootMinus CepsNormalData.eta CepsNormalData.factorMinus
    rw [hAp, hAm, add_sub_cancel]
    rfl
  have hE : E = cexp ((βm - βp) * (l : ℂ)) := by
    rw [hEdef]
    unfold CepsNormalData.decay CepsNormalData.eta
    rw [hAp, hAm]
    congr 1
    ring
  have hΔeq : Δ = 1 - E * (Bp * Bm) := by
    rw [hΔdef]
    unfold CepsNormalData.delta
    rw [CepsNormalData.pi_eq_overshoots A L μ q hQp hQm]
  -- the denominator is nonzero away from merging
  have hηΔ := strip_eta_le_delta dom hW hθ hD hμ0 hq0' hq0 hl
  have hΔlow := cepsNormal_actual_delta_lower_bound dom hW hθ hD hμ0 hq0' hq0 hl
  have hΔ0 : Δ ≠ 0 := by
    intro h0
    have hcs := cepsNormal_sectorConst_pos dom hW hθ hD
    have hrpos : 0 < ‖cepsRootR D θ ρ μ q‖ := norm_pos_iff.mpr hr
    have hpos : 0 < dom.normalSectorConst / 4 * min 1 (‖cepsRootR D θ ρ μ q‖ * l) :=
      mul_pos (by positivity) (lt_min one_pos (mul_pos hrpos hl0))
    have : ‖Δ‖ = 0 := by rw [h0, norm_zero]
    rw [hΔdef] at this
    linarith
  -- the actual reduced unknowns
  set x := 1 - cepsStripExit ν β a l 0 (Iio 0) (-βm) q with hxdef
  set ℓp := cepsStripExit ν β a l 0 (Ioi l) (-βp) q with hℓpdef
  set e1 := stripUpperErr dom ν β a ρ μ q l βm with he1def
  set e2 := stripLowerErr dom ν β a ρ μ q l βp with he2def
  have hx : x = (βp - βm) * cexp (L μ q βm) + Bp * ℓp + e1 := by
    rw [hxdef, hIm, hBp]
    ring
  have hℓ : ℓp = E * Bm * x + e2 := by
    rw [hE, hBm]
    exact hIIp
  set xh := A.passageX L μ q l with hxhdef
  set yh := A.passageY L μ q l with hyhdef
  have hxh : xh = (βp - βm) * cexp (L μ q βm) / Δ := by
    rw [hxhdef]
    unfold CepsNormalData.passageX CepsNormalData.eta
    rw [hAp, hAm]
  have hyh : yh = E * Bm * xh := by
    rw [hyhdef]
    unfold CepsNormalData.passageY
    rfl
  obtain ⟨halg1, halg2⟩ := strip_exit_algebra hΔeq hΔ0 hxh hyh hx hℓ
  -- the two exit errors
  have hupN : A.upperExit L μ q t l =
      1 - (βp - t) * cexp (L μ q t) - cexp (L μ q t - L μ q βp) * yh := by
    unfold CepsNormalData.upperExit CepsNormalData.overshootPlus
    rw [hAp, sub_sub_cancel]
  have hlowN : A.lowerExit L μ q t l =
      cexp ((βm - t) * (l : ℂ)) * cexp (dom.canonLMinus ρ μ q t - dom.canonLMinus ρ μ q βm) *
        xh := by
    unfold CepsNormalData.lowerExit CepsNormalData.overshootMinus CepsNormalData.factorMinus
    rw [hAm, add_sub_cancel]
    rfl
  have hU : cepsStripExit ν β a l 0 (Iio 0) (-t) q - A.upperExit L μ q t l =
      -(cexp (L μ q t - L μ q βp) * (ℓp - yh)) - stripUpperErr dom ν β a ρ μ q l t := by
    rw [hupN, hIt]
    ring
  have hL : cepsStripExit ν β a l 0 (Ioi l) (-t) q - A.lowerExit L μ q t l =
      cexp ((βm - t) * (l : ℂ)) *
          cexp (dom.canonLMinus ρ μ q t - dom.canonLMinus ρ μ q βm) * (x - xh) +
        stripLowerErr dom ν β a ρ μ q l t := by
    rw [hlowN, hIIt]
    ring
  -- the bounds
  set ε := Real.exp (-(dom.c₀ / 2 / 2) * l) with hεdef
  have hε : 0 < ε := Real.exp_pos _
  have hR6 := dom.stripRewardConst_nonneg
  have hBpn : ‖Bp‖ ≤ dom.stripBplus := by
    rw [hBp]
    exact norm_cexp_canonL_sub_le dom hW hθ hD hμ0 hq0' hβmn2 hβpn2
  have hBmn : ‖Bm‖ ≤ dom.stripBminus := by
    rw [hBm]
    exact norm_cexp_canonLMinus_sub_le dom hW hθ hD hμ0 hq0' hβpn2 hβmn2
  have hEn : ‖E‖ ≤ 1 := by
    rw [hE]
    refine norm_cexp_mul_ofReal_le_one_of_re_nonpos ?_ hl0.le
    simp only [sub_re]
    linarith
  have hηn : ‖βp - βm‖ ≤ dom.c₀ / 2 := by
    calc _ ≤ ‖βp‖ + ‖βm‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have he1 : ‖e1‖ ≤ dom.stripRewardConst * ‖βp - βm‖ * ε := by
    have h := norm_stripUpperErr_le dom hW hθ hD ν β a hμ hq0 hq hl0.le (s := βm) hβmn'
    rw [show -βm + cepsRootPlus D θ ρ μ q = βp - βm by rw [← hβp]; ring] at h
    exact h
  have he2 : ‖e2‖ ≤ 2 * (dom.stripRewardConst * ‖βp - βm‖ * ε) :=
    norm_stripLowerErr_le dom hW hθ hD ν β a hμ hq0 hq hl0.le hsp hβpn'
  have hBplus0 : 0 ≤ dom.stripBplus := (Real.exp_pos _).le
  have hBminus0 : 0 ≤ dom.stripBminus := le_trans (norm_nonneg _) hBmn
  have hX : ‖x - xh‖ ≤ dom.stripXConst * ε := by
    have hΔpos : 0 < ‖Δ‖ := norm_pos_iff.mpr hΔ0
    have h1 : ‖x - xh‖ * ‖Δ‖ ≤ (2 * dom.stripBplus + 1) * dom.stripRewardConst *
        ‖βp - βm‖ * ε := by
      rw [← norm_mul, halg1]
      calc _ ≤ ‖Bp * e2‖ + ‖e1‖ := norm_add_le _ _
        _ = ‖Bp‖ * ‖e2‖ + ‖e1‖ := by rw [norm_mul]
        _ ≤ dom.stripBplus * (2 * (dom.stripRewardConst * ‖βp - βm‖ * ε)) +
            dom.stripRewardConst * ‖βp - βm‖ * ε :=
          add_le_add (mul_le_mul hBpn he2 (norm_nonneg _) hBplus0) he1
        _ = _ := by ring
    have h2 : ‖βp - βm‖ ≤ dom.stripEtaDelta * ‖Δ‖ := hηΔ
    have hK0 : 0 ≤ (2 * dom.stripBplus + 1) * dom.stripRewardConst := by positivity
    calc ‖x - xh‖ = ‖x - xh‖ * ‖Δ‖ / ‖Δ‖ := by field_simp
      _ ≤ (2 * dom.stripBplus + 1) * dom.stripRewardConst * ‖βp - βm‖ * ε / ‖Δ‖ := by gcongr
      _ ≤ (2 * dom.stripBplus + 1) * dom.stripRewardConst * (dom.stripEtaDelta * ‖Δ‖) * ε /
          ‖Δ‖ := by gcongr
      _ = dom.stripXConst * ε := by
        unfold CepsCanonDomain.stripXConst
        field_simp
  have hX0 : 0 ≤ dom.stripXConst * ε := le_trans (norm_nonneg _) hX
  have hY : ‖ℓp - yh‖ ≤ dom.stripYConst * ε := by
    rw [halg2]
    calc _ ≤ ‖E * Bm * (x - xh)‖ + ‖e2‖ := norm_add_le _ _
      _ = ‖E‖ * ‖Bm‖ * ‖x - xh‖ + ‖e2‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * dom.stripBminus * (dom.stripXConst * ε) +
          2 * (dom.stripRewardConst * (dom.c₀ / 2) * ε) := by
        refine add_le_add (mul_le_mul (mul_le_mul hEn hBmn (norm_nonneg _) zero_le_one) hX
          (norm_nonneg _) (by positivity)) (he2.trans ?_)
        gcongr
      _ = dom.stripYConst * ε := by unfold CepsCanonDomain.stripYConst; ring
  have hY0 : 0 ≤ dom.stripYConst * ε := le_trans (norm_nonneg _) hY
  have hupper : ‖cepsStripExit ν β a l 0 (Iio 0) (-t) q - A.upperExit L μ q t l‖ ≤
      (dom.stripBplus * dom.stripYConst + dom.stripRewardConst * (dom.c₀ / 2)) * ε := by
    rw [hU]
    have hB := norm_cexp_canonL_sub_le dom hW hθ hD hμ0 hq0' htn2 hβpn2
    have he := norm_stripUpperErr_le dom hW hθ hD ν β a hμ hq0 hq hl0.le htn
    have htb : ‖-t + βp‖ ≤ dom.c₀ / 2 := by
      calc _ ≤ ‖-t‖ + ‖βp‖ := norm_add_le _ _
        _ = ‖t‖ + ‖βp‖ := by rw [norm_neg]
        _ ≤ _ := by linarith
    calc _ ≤ ‖-(cexp (L μ q t - L μ q βp) * (ℓp - yh))‖ +
          ‖stripUpperErr dom ν β a ρ μ q l t‖ := norm_sub_le _ _
      _ = ‖cexp (L μ q t - L μ q βp)‖ * ‖ℓp - yh‖ + ‖stripUpperErr dom ν β a ρ μ q l t‖ := by
        rw [norm_neg, norm_mul]
      _ ≤ dom.stripBplus * (dom.stripYConst * ε) +
          dom.stripRewardConst * (dom.c₀ / 2) * ε := by
        refine add_le_add (mul_le_mul hB hY (norm_nonneg _) hBplus0) (he.trans ?_)
        gcongr
      _ = _ := by ring
  have hlower : ‖cepsStripExit ν β a l 0 (Ioi l) (-t) q - A.lowerExit L μ q t l‖ ≤
      (dom.stripBminus * dom.stripXConst + 2 * dom.stripRewardConst * (dom.c₀ / 2)) * ε := by
    rw [hL]
    have hB := norm_cexp_canonLMinus_sub_le dom hW hθ hD hμ0 hq0' htn2 hβmn2
    have hexp : ‖cexp ((βm - t) * (l : ℂ))‖ ≤ 1 := by
      refine norm_cexp_mul_ofReal_le_one_of_re_nonpos ?_ hl0.le
      simp only [sub_re, ht]
      linarith
    have he := norm_stripLowerErr_le dom hW hθ hD ν β a hμ hq0 hq hl0.le (s := t)
      (by rw [ht]) htn
    have htb : ‖t - βm‖ ≤ dom.c₀ / 2 := by
      calc _ ≤ ‖t‖ + ‖βm‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    calc _ ≤ ‖cexp ((βm - t) * (l : ℂ)) *
            cexp (dom.canonLMinus ρ μ q t - dom.canonLMinus ρ μ q βm) * (x - xh)‖ +
          ‖stripLowerErr dom ν β a ρ μ q l t‖ := norm_add_le _ _
      _ = ‖cexp ((βm - t) * (l : ℂ))‖ *
            ‖cexp (dom.canonLMinus ρ μ q t - dom.canonLMinus ρ μ q βm)‖ * ‖x - xh‖ +
          ‖stripLowerErr dom ν β a ρ μ q l t‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * dom.stripBminus * (dom.stripXConst * ε) +
          2 * (dom.stripRewardConst * (dom.c₀ / 2) * ε) := by
        refine add_le_add (mul_le_mul (mul_le_mul hexp hB (norm_nonneg _) zero_le_one) hX
          (norm_nonneg _) (by positivity)) (he.trans ?_)
        gcongr
      _ = _ := by ring
  calc _ ≤ (dom.stripBplus * dom.stripYConst + dom.stripRewardConst * (dom.c₀ / 2)) * ε +
        (dom.stripBminus * dom.stripXConst + 2 * dom.stripRewardConst * (dom.c₀ / 2)) * ε :=
      add_le_add hupper hlower
    _ = dom.stripExitConst * ε := by unfold CepsCanonDomain.stripExitConst; ring

end

end PGM
