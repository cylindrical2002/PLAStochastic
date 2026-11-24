import PLAStochastic.Index.CEPS.StripError.Reflect
import PLAStochastic.Index.CEPS.Normal.WidthDerivative

/-!
# WP9: width derivatives of the normal entrance and bridge

At a non-degenerate point (`q ≠ 0` in the closed right discount half-disc) the original
root-zone normal entrance at mark `0`, bridge and lower-end entrance are the explicit X5 quotients,
which coincide with the regular (divided-difference) forms of WP5
(`strip_raw_entrance_eq`, `strip_raw_bridge_eq`, `strip_raw_bottom_eq`). In the width they satisfy

`∂_l ĥ₊ = e^{L(0)}/Q(0) - ĥ₊ (η/Δ - β₊)`, `∂_l Û = -Û (β₋ + η/Δ)`

(`hasDerivAt_strip_entrance0`, `hasDerivAt_strip_bridge`). Since `|η/Δ| ≤ C`, both derivatives
are bounded by class polynomials in `l` uniformly up to zero discount and merging; this is the
normal half of the second width derivative budget of S-4.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Complex Metric
open WienerHopf

variable {ρ : Measure ℝ} {fρ : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρ fρ D θ v) (hθ : 0 < θ) (hD : 0 < D)

/-! ## Non-degeneracy away from zero discount -/

theorem q₀_le_half {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : dom.q₀ ≤ 1 / 2 := by
  have h2 := dom.rmax_one
  have h3 := dom.rmax_pos
  rw [dom.q₀_def]
  nlinarith

include hW hθ hD in
theorem strip_nondeg {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀)
    (hqne : q ≠ 0) :
    let A := cepsWHNormalData D θ ρ μ q
    A.Q 0 ≠ 0 ∧ A.Q A.βp ≠ 0 ∧ A.Q A.βm ≠ 0 ∧ A.βp ≠ 0 ∧ A.βm ≠ 0 ∧ A.eta ≠ 0 ∧
      A.d 0 ≠ 0 ∧ A.d 0 = -A.βp * A.βm * A.Q 0 ∧ A.ψp = A.eta * A.Q A.βp := by
  intro A
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hc0 := dom.c₀_pos
  have hρA : dom.c₀ / 4 < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hQne : ∀ z : ℂ, ‖z‖ ≤ dom.c₀ / 4 → cepsQ D θ ρ μ q z ≠ 0 := fun z hz =>
    CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμc hq (mem_ball_zero_iff.mpr (by linarith))
  have hQ0 : A.Q 0 ≠ 0 := hQne 0 (by simp; positivity)
  have hQp : A.Q A.βp ≠ 0 := hQne _ (dom.norm_rootPlus_le hW hθ hD hμc hq)
  have hQm : A.Q A.βm ≠ 0 := hQne _ (dom.norm_rootMinus_le hW hθ hD hμc hq)
  have hd0 : A.d 0 = 1 - cexp (-q) := cepsD_zero_eq hW (μ : ℂ) q
  have hdne : A.d 0 ≠ 0 := by
    rw [hd0]
    have hqh : ‖q‖ ≤ 1 / 2 := hq.trans (q₀_le_half dom)
    have := cepsBandDisc_norm_exp_sub_one_lower hqh
    have : 0 < ‖q‖ := norm_pos_iff.mpr hqne
    exact norm_pos_iff.mp (by linarith)
  have hfac : A.d 0 = -A.βp * A.βm * A.Q 0 := by
    show cepsD ρ μ q 0 = -cepsRootPlus D θ ρ μ q * cepsRootMinus D θ ρ μ q * cepsQ D θ ρ μ q 0
    rw [CepsC6.cepsD_eq_mul_cepsQ dom hW hθ hD hμc hq 0]
    ring
  have hbp : A.βp ≠ 0 := by
    intro h; apply hdne; rw [hfac, h]; ring
  have hbm : A.βm ≠ 0 := by
    intro h; apply hdne; rw [hfac, h]; ring
  have hη : A.eta ≠ 0 := by
    have hre := cepsRoots_difference_re_ge hW hθ hD dom hμ hq hq0
    have hv := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
    have hr := cepsRootR_ne_zero_of dom hθ hD hW hμ hq0 (Or.inr hqne)
    have hrp : 0 < ‖cepsRootR D θ ρ μ q‖ := norm_pos_iff.mpr hr
    intro h0
    have : (cepsRootPlus D θ ρ μ q - cepsRootMinus D θ ρ μ q).re = 0 := by
      have h0' : cepsRootPlus D θ ρ μ q - cepsRootMinus D θ ρ μ q = 0 := h0
      rw [h0', zero_re]
    have : 0 < ‖cepsRootR D θ ρ μ q‖ / (2 * Real.sqrt v) := by positivity
    linarith
  have hψ : A.ψp = A.eta * A.Q A.βp := by
    show deriv (cepsCgfShift ρ μ) (cepsRootPlus D θ ρ μ q) =
      (cepsRootPlus D θ ρ μ q - cepsRootMinus D θ ρ μ q) *
        cepsQ D θ ρ μ q (cepsRootPlus D θ ρ μ q)
    rw [← CepsC6.cepsQ_rootPlus_mul dom hW hθ hD hμc hq]
    ring
  exact ⟨hQ0, hQp, hQm, hbp, hbm, hη, hdne, hfac, hψ⟩

include hW hθ hD in
theorem strip_delta_ne {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀)
    (hqne : q ≠ 0) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    (cepsWHNormalData D θ ρ μ q).delta (dom.canonL ρ) μ q l ≠ 0 := by
  have hη := (strip_nondeg dom hW hθ hD hμ hq0 hq hqne).2.2.2.2.2.1
  intro h0
  have h := strip_eta_le_delta dom hW hθ hD hμ hq hq0 hl
  rw [show (cepsWHNormalData D θ ρ μ q).delta (dom.canonL ρ) μ q l = 0 from h0, norm_zero,
    mul_zero] at h
  exact hη (norm_le_zero_iff.mp h)

/-! ## Raw and regular forms agree away from zero discount -/

include hW hθ hD in
theorem strip_raw_entrance_eq {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) (hqne : q ≠ 0) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    (cepsWHNormalData D θ ρ μ q).entrance (dom.canonL ρ) μ q 0 l =
      (cepsNormalData D θ ρ μ q).regularEntrance (dom.canonL ρ) μ q l 0 := by
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  obtain ⟨hQ0, -, hQm, hbp, hbm, hη, -, hfac, -⟩ := strip_nondeg dom hW hθ hD hμ hq0 hq hqne
  have hS := cepsNormal_actual_dslope_ne_zero dom hW hθ hD hμ hq hq0 hl
  have hd : (cepsWHNormalData D θ ρ μ q).d 0 = (cepsWHNormalData D θ ρ μ q).Q 0 *
      ((cepsWHNormalData D θ ρ μ q).βp - 0) * (0 - (cepsWHNormalData D θ ρ μ q).βm) := by
    rw [hfac]; ring
  rw [CepsNormalData.entrance_eq_regular _ _ _ _ _ 0 hQm hQ0 hη (by rwa [sub_zero])
    (by rwa [zero_sub, neg_ne_zero]) hS hd]
  exact (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμc hq (dom.canonL ρ) l (t := 0)
    (mem_ball_zero_iff.mpr (by simp; exact dom.ρA_pos))).1

include hW hθ hD in
theorem strip_raw_bridge_eq {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) (hqne : q ≠ 0) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    (cepsWHNormalData D θ ρ μ q).bridge (dom.canonL ρ) μ q l =
      (cepsNormalData D θ ρ μ q).regularBridge (dom.canonL ρ) μ q l := by
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  obtain ⟨-, -, hQm, -, -, hη, -, -, hψ⟩ := strip_nondeg dom hW hθ hD hμ hq0 hq hqne
  have hS := cepsNormal_actual_dslope_ne_zero dom hW hθ hD hμ hq hq0 hl
  rw [CepsNormalData.bridge_eq_regular _ _ _ _ _ hQm hη hS hψ]
  exact (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμc hq (dom.canonL ρ) l (t := 0)
    (mem_ball_zero_iff.mpr (by simp; exact dom.ρA_pos))).2

include hW hθ hD in
theorem strip_raw_bottom_eq {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) (hqne : q ≠ 0) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    (cepsWHNormalData D θ ρ μ q).bottomEntrance (dom.canonL ρ) μ q l =
      (cepsNormalData D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q).regularEntrance
        (dom.canonL (ρ.map Neg.neg)) ((-μ : ℝ) : ℂ) q l 0 := by
  have hμ' : |(-μ)| ≤ dom.μ₀ := by rwa [abs_neg]
  rw [← stripReflect_entrance_eq_bottom dom hW hθ hD hμ hq0 hq]
  exact strip_raw_entrance_eq dom hW.neg hθ hD hμ' hq0 hq hqne hl

/-! ## Width derivatives -/

include hW hθ hD in
theorem hasDerivAt_strip_entrance0 {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) (hqne : q ≠ 0) (l : ℂ)
    (hΔ : (cepsWHNormalData D θ ρ μ q).delta (dom.canonL ρ) μ q l ≠ 0) :
    HasDerivAt (fun l' => (cepsWHNormalData D θ ρ μ q).entrance (dom.canonL ρ) μ q 0 l')
      (cexp (dom.canonL ρ μ q 0) / cepsQ D θ ρ μ q 0 -
        (cepsWHNormalData D θ ρ μ q).entrance (dom.canonL ρ) μ q 0 l *
          ((cepsWHNormalData D θ ρ μ q).eta /
              (cepsWHNormalData D θ ρ μ q).delta (dom.canonL ρ) μ q l -
            (cepsWHNormalData D θ ρ μ q).βp)) l := by
  obtain ⟨hQ0, -, -, hbp, hbm, -, -, hfac, -⟩ := strip_nondeg dom hW hθ hD hμ hq0 hq hqne
  set A := cepsWHNormalData D θ ρ μ q with hAdef
  set L := dom.canonL ρ with hLdef
  set P := A.pi L μ q with hPdef
  set N0 := A.markedN L μ q 0 with hN0def
  have hE := A.hasDerivAt_decay l
  have hY : HasDerivAt (fun l' => cexp ((A.βm - 0) * l'))
      (cexp ((A.βm - 0) * l) * (A.βm - 0)) l := by
    have := ((hasDerivAt_id l).const_mul (A.βm - 0)).cexp
    simpa using this
  have hnum : HasDerivAt (fun l' => A.entranceNumerator L μ q 0 l')
      (-((A.βm - 0) * (A.decay l * (-A.eta)) * P) -
        A.eta * (cexp ((A.βm - 0) * l) * (A.βm - 0)) * N0) l := by
    have h1 := (((hE.const_mul (A.βm - 0)).mul_const P).const_sub (A.βp - 0)).sub
      ((hY.const_mul A.eta).mul_const N0)
    have hfun : (fun l' => A.entranceNumerator L μ q 0 l') = fun l' =>
        (A.βp - 0) - (A.βm - 0) * A.decay l' * P - A.eta * cexp ((A.βm - 0) * l') * N0 := by
      funext l'; rfl
    rw [hfun]
    exact h1
  have hf := (hnum.const_mul (cexp (L μ q 0) / A.d 0)).div (A.hasDerivAt_delta L μ q l) hΔ
  have hfun : (fun l' => A.entrance L μ q 0 l') =
      fun l' => cexp (L μ q 0) / A.d 0 * A.entranceNumerator L μ q 0 l' / A.delta L μ q l' := by
    funext l'
    unfold CepsNormalData.entrance
    ring
  rw [hfun]
  refine hf.congr_deriv ?_
  have hd0 : A.d 0 = -A.βp * A.βm * cepsQ D θ ρ μ q 0 := hfac
  have hQ0' : cepsQ D θ ρ μ q 0 ≠ 0 := hQ0
  have hΔ' : 1 - A.decay l * P ≠ 0 := hΔ
  have hdel : A.delta L μ q l = 1 - A.decay l * P := rfl
  have heta : A.eta = A.βp - A.βm := rfl
  have hnumeq : A.entranceNumerator L μ q 0 l =
      (A.βp - 0) - (A.βm - 0) * A.decay l * P - A.eta * cexp ((A.βm - 0) * l) * N0 := rfl
  have hent : A.entrance L μ q 0 l =
      cexp (L μ q 0) / A.d 0 * A.entranceNumerator L μ q 0 l / A.delta L μ q l := by
    unfold CepsNormalData.entrance; ring
  rw [hent, hnumeq, hdel, heta, hd0]
  field_simp
  ring

theorem hasDerivAt_strip_bridge (μ : ℝ) {q : ℂ} (l : ℂ)
    (hΔ : (cepsWHNormalData D θ ρ μ q).delta (dom.canonL ρ) μ q l ≠ 0) :
    HasDerivAt (fun l' => (cepsWHNormalData D θ ρ μ q).bridge (dom.canonL ρ) μ q l')
      (-(cepsWHNormalData D θ ρ μ q).bridge (dom.canonL ρ) μ q l *
        ((cepsWHNormalData D θ ρ μ q).βm + (cepsWHNormalData D θ ρ μ q).eta /
          (cepsWHNormalData D θ ρ μ q).delta (dom.canonL ρ) μ q l)) l := by
  set A := cepsWHNormalData D θ ρ μ q with hAdef
  set L := dom.canonL ρ with hLdef
  have hh : HasDerivAt (fun l' => A.halfBridge L μ q l')
      (A.ψp * (cexp (-A.βp * l - 2 * L μ q A.βp) * (-A.βp * 1))) l := by
    have := (((hasDerivAt_id' l).const_mul (-A.βp)).sub_const (2 * L μ q A.βp)).cexp.const_mul A.ψp
    exact this
  have hf := hh.div (A.hasDerivAt_delta L μ q l) hΔ
  have hfun : (fun l' => A.bridge L μ q l') = fun l' => A.halfBridge L μ q l' / A.delta L μ q l' := by
    funext l'; rfl
  rw [hfun]
  refine hf.congr_deriv ?_
  have hΔ' : 1 - A.decay l * A.pi L μ q ≠ 0 := hΔ
  have hdel : A.delta L μ q l = 1 - A.decay l * A.pi L μ q := rfl
  have heta : A.eta = A.βp - A.βm := rfl
  have hbr : A.bridge L μ q l = A.halfBridge L μ q l / A.delta L μ q l := rfl
  have hhb : A.halfBridge L μ q l = A.ψp * cexp (-A.βp * l - 2 * L μ q A.βp) := rfl
  rw [hbr, hdel, hhb, heta]
  generalize A.decay l = E at hΔ' ⊢
  generalize A.pi L μ q = P at hΔ' ⊢
  generalize cexp (-A.βp * l - 2 * L μ q A.βp) = B
  field_simp
  ring

end

end PGM
