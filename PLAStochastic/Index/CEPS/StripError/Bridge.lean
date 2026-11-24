import PLAStochastic.Index.CEPS.StripError.NormalWidth
import PLAStochastic.Index.CEPS.Band.ClassicalMain

/-!
# WP9, S-4: the bridge error

For the `Y_μ` walk in `[0, l]` (`β = 1+μ`, `a = 1`) let `h₋`, `h₊`, `U` be the actual bottom-started
and top-started entrances and the bridge (WP8), and `ĥ₋`, `ĥ₊`, `Û` the normal ones. Both sides
satisfy the width Hadamard identity `∂_l h₋ = U h₊` (WP8/X3, X5). With `e = h₋ - ĥ₋`
(exponentially small by S-3 (b) for the bottom-started strip and the reflection identity) and
`g = U h₊ - Û ĥ₊ = e'`, the real secant interpolation gives `|g(l)| ≤ 2ε/δ + Lδ`, where the
Lipschitz budget `L` is X3's actual `Cw⁹` plus the normal width derivatives of `NormalWidth`
(`strip_bridge_gap`). Then `U - Û = (g - Û (h₊ - ĥ₊)) / h₊` with `|h₊| ≥ c/l²` (X7)
(`strip_bridge_error_pt`).
-/

namespace PGM

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open WienerHopf
open scoped NNReal

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

/-- The class constant of the gap `U h₊ - Û ĥ₊`. -/
def stripBridgeGapConst (dom : CepsCanonDomain D θ v) (Dg vlo vhi : ℝ) (Kf : ℝ≥0) : ℝ :=
  2 ^ 8 * max (stripEntranceConst dom Dg vlo vhi) 0 +
    max (cepsBandSecondWidthConst Dg vlo vhi Kf) 0 +
    2 * max dom.normalBridgeBound 0 *
      (Real.exp dom.normalLogBound * 4 / cepsVarLo D +
        8 * max dom.normalEntranceBound 0 * (max dom.stripEtaDelta 0 + dom.c₀ / 4))

variable {ρ : Measure ℝ} {fρ : ℝ → ℝ} (hW : IsStepLaw ρ fρ D θ v)

include hW hθ hD in
theorem norm_strip_entrance0_le {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) (hqne : q ≠ 0) {y : ℝ} (hy : dom.normalCoarseWidth ≤ y) :
    ‖(cepsWHNormalData D θ ρ μ q).entrance (dom.canonL ρ) μ q 0 y‖ ≤
      max dom.normalEntranceBound 0 * (1 + y) ^ 2 := by
  have hyW : dom.normalWidthThreshold ≤ y := (le_max_left _ _).trans hy
  rw [strip_raw_entrance_eq dom hW hθ hD hμ hq0 hq hqne hyW]
  refine (cepsNormalData_canonical_regularEntrance_bound dom hW hθ hD hμ hq hq0 (t := 0)
    (by simp; exact (div_pos dom.c₀_pos (by norm_num)).le) (by simp) hy).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

include hW hθ hD in
theorem norm_strip_bridge_le {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) (hqne : q ≠ 0) {y : ℝ} (hy : dom.normalCoarseWidth ≤ y) (hy1 : 1 ≤ y) :
    ‖(cepsWHNormalData D θ ρ μ q).bridge (dom.canonL ρ) μ q y‖ ≤
      2 * max dom.normalBridgeBound 0 := by
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hyW : dom.normalWidthThreshold ≤ y := (le_max_left _ _).trans hy
  rw [strip_raw_bridge_eq dom hW hθ hD hμ hq0 hq hqne hyW]
  refine (cepsNormalData_canonical_regularBridge_bound dom hW hθ hD hμ hq hq0 hy).trans ?_
  have hr := dom.norm_cepsRootR_le hW hθ hD hμc hq
  have hr1 := dom.rmax_one
  have hyinv : 1 / y ≤ 1 := by rw [div_le_one (by linarith)]; exact hy1
  calc dom.normalBridgeBound * (‖cepsRootR D θ ρ μ q‖ + 1 / y) ≤
      max dom.normalBridgeBound 0 * (‖cepsRootR D θ ρ μ q‖ + 1 / y) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max dom.normalBridgeBound 0 * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add (hr.trans hr1) hyinv) (le_max_right _ _)
    _ = _ := by ring

include hW hθ hD in
theorem norm_eta_div_delta_le {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    ‖(cepsWHNormalData D θ ρ μ q).eta / (cepsWHNormalData D θ ρ μ q).delta (dom.canonL ρ) μ q l‖ ≤
      max dom.stripEtaDelta 0 := by
  have h := strip_eta_le_delta dom hW hθ hD hμ hq hq0 hl
  set Δ := (cepsWHNormalData D θ ρ μ q).delta (dom.canonL ρ) μ q l
  by_cases hΔ : Δ = 0
  · rw [hΔ, div_zero, norm_zero]; exact le_max_right _ _
  · rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hΔ)]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

include hW hθ hD in
/-- The width derivative of the normal product `ĥ₊ Û` along real widths, with its budget. -/
theorem hasDerivAt_strip_normal_product {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) (hqne : q ≠ 0) {y : ℝ} (hy : dom.normalCoarseWidth ≤ y) (hy1 : 1 ≤ y) :
    ∃ φ' : ℂ, HasDerivAt (fun x : ℝ =>
        (cepsWHNormalData D θ ρ μ q).entrance (dom.canonL ρ) μ q 0 x *
          (cepsWHNormalData D θ ρ μ q).bridge (dom.canonL ρ) μ q x) φ' y ∧
      ‖φ'‖ ≤ 2 * max dom.normalBridgeBound 0 *
        (Real.exp dom.normalLogBound * 4 / cepsVarLo D +
          2 * max dom.normalEntranceBound 0 * (1 + y) ^ 2 *
            (max dom.stripEtaDelta 0 + dom.c₀ / 4)) := by
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hyW : dom.normalWidthThreshold ≤ y := (le_max_left _ _).trans hy
  have hΔ := strip_delta_ne dom hW hθ hD hμ hq0 hq hqne hyW
  set A := cepsWHNormalData D θ ρ μ q with hAdef
  set L := dom.canonL ρ with hLdef
  have hE := hasDerivAt_strip_entrance0 dom hW hθ hD hμ hq0 hq hqne (y : ℂ) hΔ
  have hB := hasDerivAt_strip_bridge dom μ (q := q) (y : ℂ) hΔ
  have hP := (hE.mul hB).comp_ofReal
  refine ⟨_, hP, ?_⟩
  have hc0 := dom.c₀_pos
  have hvl := cepsVarLo_pos hD
  have hent := norm_strip_entrance0_le dom hθ hD hW hμ hq0 hq hqne hy
  have hbr := norm_strip_bridge_le dom hθ hD hW hμ hq0 hq hqne hy hy1
  have hed := norm_eta_div_delta_le dom hθ hD hW hμ hq0 hq hyW
  have hbp : ‖A.βp‖ ≤ dom.c₀ / 4 := dom.norm_rootPlus_le hW hθ hD hμc hq
  have hbm : ‖A.βm‖ ≤ dom.c₀ / 4 := dom.norm_rootMinus_le hW hθ hD hμc hq
  have hL0 : ‖cexp (L μ q 0) / cepsQ D θ ρ μ q 0‖ ≤ Real.exp dom.normalLogBound * 4 / cepsVarLo D := by
    have hLb := norm_canonL_le_logBound dom hW hθ hD hμ hq (z := 0) (by simp; positivity)
    have hQ := cepsQ_norm_ge_on_rootZone dom hW hθ hD hμc hq (ζ := 0) (by simp; exact dom.ρA_pos)
    rw [norm_div]
    have hQpos : 0 < ‖cepsQ D θ ρ μ q 0‖ := lt_of_lt_of_le (by positivity) hQ
    rw [div_le_iff₀ hQpos]
    calc ‖cexp (L μ q 0)‖ ≤ Real.exp dom.normalLogBound :=
          (norm_cexp_le_exp_norm _).trans (Real.exp_le_exp.mpr hLb)
      _ = Real.exp dom.normalLogBound * 4 / cepsVarLo D * (cepsVarLo D / 4) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hQ (by positivity)
  set CB := max dom.normalBridgeBound 0
  set CE := max dom.normalEntranceBound 0
  set C3 := max dom.stripEtaDelta 0
  have hCB : 0 ≤ CB := le_max_right _ _
  have hCE : 0 ≤ CE := le_max_right _ _
  have hC3 : 0 ≤ C3 := le_max_right _ _
  set ent := A.entrance L μ q 0 (y : ℂ)
  set br := A.bridge L μ q (y : ℂ)
  set ed := A.eta / A.delta L μ q (y : ℂ)
  have hent' : ‖ent‖ ≤ CE * (1 + y) ^ 2 := hent
  have hbr' : ‖br‖ ≤ 2 * CB := hbr
  have hed' : ‖ed‖ ≤ C3 := hed
  have hk1 : ‖ed - A.βp‖ ≤ C3 + dom.c₀ / 4 :=
    (norm_sub_le _ _).trans (add_le_add hed' hbp)
  have hk2 : ‖A.βm + ed‖ ≤ dom.c₀ / 4 + C3 := (norm_add_le _ _).trans (add_le_add hbm hed')
  have hdE : ‖cexp (L μ q 0) / cepsQ D θ ρ μ q 0 - ent * (ed - A.βp)‖ ≤
      Real.exp dom.normalLogBound * 4 / cepsVarLo D + CE * (1 + y) ^ 2 * (C3 + dom.c₀ / 4) := by
    refine (norm_sub_le _ _).trans (add_le_add hL0 ?_)
    rw [norm_mul]
    exact mul_le_mul hent' hk1 (norm_nonneg _) (by positivity)
  have hdB : ‖-br * (A.βm + ed)‖ ≤ 2 * CB * (dom.c₀ / 4 + C3) := by
    rw [norm_mul, norm_neg]
    exact mul_le_mul hbr' hk2 (norm_nonneg _) (by positivity)
  calc ‖(cexp (L μ q 0) / cepsQ D θ ρ μ q 0 - ent * (ed - A.βp)) * br + ent * (-br * (A.βm + ed))‖
      ≤ ‖cexp (L μ q 0) / cepsQ D θ ρ μ q 0 - ent * (ed - A.βp)‖ * ‖br‖ +
        ‖ent‖ * ‖-br * (A.βm + ed)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
    _ ≤ (Real.exp dom.normalLogBound * 4 / cepsVarLo D + CE * (1 + y) ^ 2 * (C3 + dom.c₀ / 4)) *
          (2 * CB) + CE * (1 + y) ^ 2 * (2 * CB * (dom.c₀ / 4 + C3)) := by
          gcongr
    _ = _ := by ring

theorem exp_neg_eighth_eq (c l : ℝ) :
    Real.exp (-(c / 8) * l) = Real.exp (-(c / 16) * l) * Real.exp (-(c / 16) * l) := by
  rw [← Real.exp_add]; congr 1; ring

include hθ hD in
/-- **The width-derivative gap is exponentially small** (away from zero discount). -/
theorem strip_bridge_gap {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw Dg θg vlo vhi ν) {f : ℝ → ℝ}
    (hf : CepsGapDensity ν f Dg) {Kf : ℝ≥0} (hLip : LipschitzWith Kf f) {fW : ℝ → ℝ}
    (hW : IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v) {μ : ℝ}
    (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount / 2)
    (hqne : q ≠ 0) {l : ℝ} (hl : max dom.stripEntranceWidth 4 ≤ l) :
    ‖cepsBridgeSeries ν f (1 + μ) 1 q l * cepsTopSurv ν (1 + μ) 1 q l -
        (cepsWHNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) μ q).entrance
          (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ q 0 l *
        (cepsWHNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) μ q).bridge
          (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ q l‖ ≤
      stripBridgeGapConst dom Dg vlo vhi Kf * (1 + l) ^ 9 * Real.exp (-(dom.c₀ / 16) * l) := by
  set ρ := (ν : Measure ℝ).map fun x => 1 - x with hρdef
  set A := cepsWHNormalData D θ ρ μ q with hAdef
  set L := dom.canonL ρ with hLdef
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  have hq0' : ‖q‖ ≤ dom.q₀ := by
    have : dom.renewalDiscount ≤ dom.q₀ := min_le_left _ _
    have := dom.renewalDiscount_pos hD
    linarith
  have hlE : dom.stripEntranceWidth ≤ l := (le_max_left _ _).trans hl
  have hl4 : 4 ≤ l := (le_max_right _ _).trans hl
  have hc0 := dom.c₀_pos
  have hκ := krKappa_pos hDg hvlo hvhi
  have hEW : ∀ x : ℝ, dom.stripEntranceWidth ≤ x → dom.normalWidthThreshold ≤ x := fun x hx =>
    (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hEC : ∀ x : ℝ, dom.stripEntranceWidth ≤ x → dom.normalCoarseWidth ≤ x := fun x hx =>
    (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  obtain ⟨hQ0, -, hQm, -, -, -, hd0, -, hψ⟩ := strip_nondeg dom hW hθ hD hμ0 hq0 hq0' hqne
  set δ := Real.exp (-(dom.c₀ / 16) * l) with hδdef
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hqx : ∀ x : ℝ, 4 ≤ x → -(krKappa Dg vlo vhi / (64 * x ^ 2)) ≤ q.re := fun x hx => by
    have : 0 ≤ krKappa Dg vlo vhi / (64 * x ^ 2) := by positivity
    linarith
  -- the error and its derivative
  set e : ℝ → ℂ := fun x => cepsBottomSurv ν (1 + μ) 1 q x - A.bottomEntrance L μ q x with hedef
  set Uh : ℝ → ℂ := fun x => cepsBridgeSeries ν f (1 + μ) 1 q x * cepsTopSurv ν (1 + μ) 1 q x
  set φ : ℝ → ℂ := fun x => A.entrance L μ q 0 x * A.bridge L μ q x with hφdef
  have hact : ∀ x : ℝ, 4 ≤ x → HasDerivAt (cepsBottomSurv ν (1 + μ) 1 q) (Uh x) x := fun x hx =>
    (cepsBand_bottomSurv_first_width hDg hθg hvlo hvhi hν hf hLip (w := x) (l := x) hx
      (by linarith) (by linarith) (1 + μ) (a := 1) (by norm_num) (hqx x hx)).1
  have hnor : ∀ x : ℝ, dom.stripEntranceWidth ≤ x →
      HasDerivAt (fun y : ℝ => A.bottomEntrance L μ q y) (φ x) x := by
    intro x hx
    exact (CepsNormalData.hasDerivAt_bottomEntrance A L μ q (x : ℂ) hQ0 hQm hd0
      (strip_delta_ne dom hW hθ hD hμ0 hq0 hq0' hqne (hEW x hx)) hψ).comp_ofReal
  have hd : ∀ x ∈ Icc l (l + δ), HasDerivAt e (Uh x - φ x) x := fun x hx =>
    (hact x (by linarith [hx.1])).sub (hnor x (hlE.trans hx.1))
  -- smallness at both ends
  set Ke := max (stripEntranceConst dom Dg vlo vhi) 0
  have hKe : 0 ≤ Ke := le_max_right _ _
  have hesmall : ∀ x ∈ Icc l (l + 1),
      ‖e x‖ ≤ Ke * 2 ^ 7 * (1 + l) ^ 7 * Real.exp (-(dom.c₀ / 8) * l) := by
    intro x hx
    have hxE : dom.stripEntranceWidth ≤ x := hlE.trans hx.1
    have hb := (ceps_strip_entrance_error_bottom dom hθ hD hDg hθg hvlo hvhi hν hf hW hμ hxE).1
      q hq0 hq
    rw [← strip_raw_bottom_eq dom hW hθ hD hμ0 hq0 hq0' hqne (hEW x hxE)] at hb
    refine hb.trans ?_
    have hx0 : 0 ≤ 1 + x := by linarith [hx.1]
    have h1 : (1 + x) ^ 7 ≤ 2 ^ 7 * (1 + l) ^ 7 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hx0 (by linarith [hx.2]) 7
    have h2 : Real.exp (-(dom.c₀ / 8) * x) ≤ Real.exp (-(dom.c₀ / 8) * l) :=
      Real.exp_le_exp.mpr (by nlinarith [hx.1])
    calc stripEntranceConst dom Dg vlo vhi * (1 + x) ^ 7 * Real.exp (-(dom.c₀ / 8) * x) ≤
        Ke * (2 ^ 7 * (1 + l) ^ 7) * Real.exp (-(dom.c₀ / 8) * l) :=
          mul_le_mul (mul_le_mul (le_max_left _ _) h1 (pow_nonneg hx0 7) hKe) h2
            (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  -- the Lipschitz budget of `g`
  set C2 := cepsBandSecondWidthConst Dg vlo vhi Kf
  have hC2 : 0 ≤ C2 := cepsBandSecondWidthConst_nonneg hDg hvlo hvhi Kf.coe_nonneg
  have hLipA := cepsBand_bottomSurv_deriv_lipschitz hDg hθg hvlo hvhi hν hf hLip (w := l) hl4
    (1 + μ) (a := 1) (by norm_num) (hqx l hl4)
  set LNc := 2 * max dom.normalBridgeBound 0 *
      (Real.exp dom.normalLogBound * 4 / cepsVarLo D +
        8 * max dom.normalEntranceBound 0 * (max dom.stripEtaDelta 0 + dom.c₀ / 4)) with hLNc
  have hLNc0 : 0 ≤ LNc := by
    have := cepsVarLo_pos hD
    have : 0 ≤ max dom.normalBridgeBound 0 := le_max_right _ _
    have : 0 ≤ max dom.normalEntranceBound 0 := le_max_right _ _
    have : 0 ≤ max dom.stripEtaDelta 0 := le_max_right _ _
    positivity
  have hφd : ∀ y : ℝ, dom.stripEntranceWidth ≤ y → HasDerivAt φ (deriv φ y) y ∧
      ‖deriv φ y‖ ≤ 2 * max dom.normalBridgeBound 0 *
        (Real.exp dom.normalLogBound * 4 / cepsVarLo D +
          2 * max dom.normalEntranceBound 0 * (1 + y) ^ 2 *
            (max dom.stripEtaDelta 0 + dom.c₀ / 4)) := by
    intro y hy
    have h2y : 2 ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
    obtain ⟨φ', hφ', hb⟩ := hasDerivAt_strip_normal_product dom hθ hD hW hμ0 hq0 hq0' hqne
      (hEC y hy) (by linarith)
    rw [hφ'.deriv]
    exact ⟨hφ', hb⟩
  have hLN : ∀ y ∈ Icc l (l + 1), ‖deriv φ y‖ ≤ LNc * (1 + l) ^ 2 := by
    intro y hy
    refine ((hφd y (hlE.trans hy.1)).2).trans ?_
    have hy2 : (1 + y) ^ 2 ≤ 4 * (1 + l) ^ 2 := by nlinarith [hy.1, hy.2]
    have hB0 : 0 ≤ max dom.normalBridgeBound 0 := le_max_right _ _
    have hE0 : 0 ≤ max dom.normalEntranceBound 0 := le_max_right _ _
    have h30 : 0 ≤ max dom.stripEtaDelta 0 + dom.c₀ / 4 := by
      have : 0 ≤ max dom.stripEtaDelta 0 := le_max_right _ _
      positivity
    have hvl := cepsVarLo_pos hD
    have hl1 : 1 ≤ (1 + l) ^ 2 := one_le_pow₀ (by linarith)
    rw [hLNc]
    calc 2 * max dom.normalBridgeBound 0 *
          (Real.exp dom.normalLogBound * 4 / cepsVarLo D +
            2 * max dom.normalEntranceBound 0 * (1 + y) ^ 2 *
              (max dom.stripEtaDelta 0 + dom.c₀ / 4)) ≤
        2 * max dom.normalBridgeBound 0 *
          (Real.exp dom.normalLogBound * 4 / cepsVarLo D * (1 + l) ^ 2 +
            2 * max dom.normalEntranceBound 0 * (4 * (1 + l) ^ 2) *
              (max dom.stripEtaDelta 0 + dom.c₀ / 4)) := by
          gcongr
          exact le_mul_of_one_le_right (by positivity) hl1
      _ = _ := by ring
  have hgL : ∀ x ∈ Icc l (l + δ), ‖(Uh x - φ x) - (Uh l - φ l)‖ ≤
      (C2 * l ^ 9 + LNc * (1 + l) ^ 2) * (x - l) := by
    intro x hx
    have hxl : x - l = dist x l := by rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
    have hA : ‖Uh x - Uh l‖ ≤ C2 * l ^ 9 * (x - l) := by
      have h1 := (hact x (by linarith [hx.1])).deriv
      have h2 := (hact l hl4).deriv
      have hmem : ∀ y ∈ Icc l (l + δ), y ∈ Icc (l / 2) (2 * l) := fun y hy =>
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have := hLipA.dist_le_mul x (hmem x hx) l (hmem l ⟨le_rfl, by linarith⟩)
      rw [h1, h2, dist_eq_norm, ← hxl] at this
      exact this
    have hN : ‖φ x - φ l‖ ≤ LNc * (1 + l) ^ 2 * (x - l) := by
      have hderiv : ∀ y ∈ Icc l x, HasDerivWithinAt φ (deriv φ y) (Icc l x) y := fun y hy =>
        (hφd y (hlE.trans hy.1)).1.hasDerivWithinAt
      have hbd : ∀ y ∈ Ico l x, ‖deriv φ y‖ ≤ LNc * (1 + l) ^ 2 := fun y hy =>
        hLN y ⟨hy.1, by linarith [hy.2, hx.2]⟩
      exact norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbd x ⟨hx.1, le_rfl⟩
    calc ‖(Uh x - φ x) - (Uh l - φ l)‖ = ‖(Uh x - Uh l) - (φ x - φ l)‖ := by ring_nf
      _ ≤ ‖Uh x - Uh l‖ + ‖φ x - φ l‖ := norm_sub_le _ _
      _ ≤ C2 * l ^ 9 * (x - l) + LNc * (1 + l) ^ 2 * (x - l) := add_le_add hA hN
      _ = _ := by ring
  have hsec := norm_le_of_real_secant hδ0 hd hgL (hesmall l ⟨le_rfl, by linarith⟩)
    (hesmall (l + δ) ⟨by linarith, by linarith⟩)
  -- the final arithmetic
  have hl0 : 0 ≤ l := by linarith
  have hp9 : l ^ 9 ≤ (1 + l) ^ 9 := pow_le_pow_left₀ hl0 (by linarith) 9
  have hp7 : (1 + l) ^ 7 ≤ (1 + l) ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hp2 : (1 + l) ^ 2 ≤ (1 + l) ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hgoal : Uh l - φ l = cepsBridgeSeries ν f (1 + μ) 1 q l * cepsTopSurv ν (1 + μ) 1 q l -
      A.entrance L μ q 0 l * A.bridge L μ q l := rfl
  rw [← hgoal]
  refine hsec.trans ?_
  have hEdiv : 2 * (Ke * 2 ^ 7 * (1 + l) ^ 7 * Real.exp (-(dom.c₀ / 8) * l)) / δ =
      2 ^ 8 * Ke * (1 + l) ^ 7 * δ := by
    rw [exp_neg_eighth_eq, ← hδdef]
    field_simp
  rw [hEdiv]
  unfold stripBridgeGapConst
  have hC2m : C2 ≤ max (cepsBandSecondWidthConst Dg vlo vhi Kf) 0 := le_max_left _ _
  calc 2 ^ 8 * Ke * (1 + l) ^ 7 * δ + (C2 * l ^ 9 + LNc * (1 + l) ^ 2) * δ ≤
      2 ^ 8 * Ke * (1 + l) ^ 9 * δ +
        (max (cepsBandSecondWidthConst Dg vlo vhi Kf) 0 * (1 + l) ^ 9 + LNc * (1 + l) ^ 9) * δ := by
        gcongr
    _ = _ := by rw [hLNc]; ring

/-- The class constant of the bridge error (with the X7 entrance lower bound `ch / l²`). -/
def stripBridgeConst (dom : CepsCanonDomain D θ v) (Dg vlo vhi : ℝ) (Kf : ℝ≥0) (ch : ℝ) : ℝ :=
  (stripBridgeGapConst dom Dg vlo vhi Kf +
    2 * max dom.normalBridgeBound 0 * max (stripEntranceConst dom Dg vlo vhi) 0) / ch

include hθ hD in
/-- **S-4, bridge error at a non-zero discount.** -/
theorem strip_bridge_error_pt {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw Dg θg vlo vhi ν)
    {f : ℝ → ℝ} (hf : CepsGapDensity ν f Dg) {Kf : ℝ≥0} (hLip : LipschitzWith Kf f)
    {fW : ℝ → ℝ} (hW : IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v) {μ : ℝ}
    (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount / 2)
    (hqne : q ≠ 0) {l : ℝ} (hl : max dom.stripEntranceWidth 4 ≤ l) {ch : ℝ} (hch0 : 0 < ch)
    (hch : ch / l ^ 2 ≤ ‖cepsStripEntrance ν 0 μ q l‖) :
    ‖cepsBridge ν f μ q l - (cepsNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) μ q).regularBridge
        (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ q l‖ ≤
      stripBridgeConst dom Dg vlo vhi Kf ch * (1 + l) ^ 11 * Real.exp (-(dom.c₀ / 16) * l) := by
  set ρ := (ν : Measure ℝ).map fun x => 1 - x with hρdef
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  have hq0' : ‖q‖ ≤ dom.q₀ := by
    have : dom.renewalDiscount ≤ dom.q₀ := min_le_left _ _
    have := dom.renewalDiscount_pos hD
    linarith
  have hlE : dom.stripEntranceWidth ≤ l := (le_max_left _ _).trans hl
  have hl4 : 4 ≤ l := (le_max_right _ _).trans hl
  have hlW : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans ((le_max_left _ _).trans hlE)
  have hlC : dom.normalCoarseWidth ≤ l := (le_max_right _ _).trans ((le_max_right _ _).trans hlE)
  have hc0 := dom.c₀_pos
  have hgap := strip_bridge_gap dom hθ hD hDg hθg hvlo hvhi hν hf hLip hW hμ hq0 hq hqne hl
  rw [cepsBridgeSeries_eq_bridge, cepsTopSurv_eq_stripEntrance,
    strip_raw_entrance_eq dom hW hθ hD hμ0 hq0 hq0' hqne hlW,
    strip_raw_bridge_eq dom hW hθ hD hμ0 hq0 hq0' hqne hlW] at hgap
  have htop := (ceps_strip_entrance_error_top dom hθ hD hDg hθg hvlo hvhi hν hf hW hμ hlE).1
    q hq0 hq
  have hbr := norm_strip_bridge_le dom hθ hD hW hμ0 hq0 hq0' hqne hlC (by linarith)
  rw [strip_raw_bridge_eq dom hW hθ hD hμ0 hq0 hq0' hqne hlW] at hbr
  set hp := cepsStripEntrance ν 0 μ q l
  set np := (cepsNormalData D θ ρ μ q).regularEntrance (dom.canonL ρ) μ q l 0
  set U := cepsBridge ν f μ q l
  set nU := (cepsNormalData D θ ρ μ q).regularBridge (dom.canonL ρ) μ q l
  have hl0 : 0 < l := by linarith
  have hhp : 0 < ‖hp‖ := lt_of_lt_of_le (by positivity) hch
  set Ke := max (stripEntranceConst dom Dg vlo vhi) 0
  set CB := max dom.normalBridgeBound 0
  have hCB : 0 ≤ CB := le_max_right _ _
  have hKe : 0 ≤ Ke := le_max_right _ _
  set E := Real.exp (-(dom.c₀ / 16) * l) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have htop' : ‖hp - np‖ ≤ Ke * (1 + l) ^ 7 * E := by
    refine htop.trans ?_
    rw [exp_neg_eighth_eq, ← hEdef]
    calc stripEntranceConst dom Dg vlo vhi * (1 + l) ^ 7 * (E * E) ≤ Ke * (1 + l) ^ 7 * (E * 1) := by
          gcongr
          · exact le_max_left _ _
      _ = _ := by ring
  have hid : (U - nU) * hp = (U * hp - np * nU) - nU * (hp - np) := by ring
  have hnum : ‖(U - nU) * hp‖ ≤
      (stripBridgeGapConst dom Dg vlo vhi Kf + 2 * CB * Ke) * (1 + l) ^ 9 * E := by
    rw [hid]
    have hp7 : (1 + l) ^ 7 ≤ (1 + l) ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc ‖(U * hp - np * nU) - nU * (hp - np)‖ ≤ ‖U * hp - np * nU‖ + ‖nU‖ * ‖hp - np‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ stripBridgeGapConst dom Dg vlo vhi Kf * (1 + l) ^ 9 * E +
          2 * CB * (Ke * (1 + l) ^ 7 * E) := add_le_add hgap (mul_le_mul hbr htop' (norm_nonneg _)
            (by positivity))
      _ ≤ stripBridgeGapConst dom Dg vlo vhi Kf * (1 + l) ^ 9 * E +
          2 * CB * (Ke * (1 + l) ^ 9 * E) := by gcongr
      _ = _ := by ring
  rw [norm_mul] at hnum
  have hG0 : 0 ≤ stripBridgeGapConst dom Dg vlo vhi Kf := by
    have := cepsVarLo_pos hD
    have : 0 ≤ max dom.normalBridgeBound 0 := le_max_right _ _
    have : 0 ≤ max dom.normalEntranceBound 0 := le_max_right _ _
    have : 0 ≤ max dom.stripEtaDelta 0 := le_max_right _ _
    have : 0 ≤ max (cepsBandSecondWidthConst Dg vlo vhi Kf) 0 := le_max_right _ _
    unfold stripBridgeGapConst
    positivity
  set G' := stripBridgeGapConst dom Dg vlo vhi Kf + 2 * CB * Ke with hG'def
  have hG'0 : 0 ≤ G' := by positivity
  have h1 : ‖U - nU‖ * (ch / l ^ 2) ≤ G' * (1 + l) ^ 9 * E :=
    (mul_le_mul_of_nonneg_left hch (norm_nonneg _)).trans hnum
  have hl2 : l ^ 2 ≤ (1 + l) ^ 2 := by nlinarith
  have hpos : 0 < ch / l ^ 2 := by positivity
  have h2 : ‖U - nU‖ ≤ G' * (1 + l) ^ 9 * E / (ch / l ^ 2) := (le_div_iff₀ hpos).mpr h1
  refine h2.trans ?_
  have hK : stripBridgeConst dom Dg vlo vhi Kf ch = G' / ch := rfl
  rw [hK, div_div_eq_mul_div]
  rw [div_le_iff₀ hch0]
  calc G' * (1 + l) ^ 9 * E * l ^ 2 ≤ G' * (1 + l) ^ 9 * E * (1 + l) ^ 2 := by gcongr
    _ = G' / ch * (1 + l) ^ 11 * E * ch := by field_simp

end

end PGM
