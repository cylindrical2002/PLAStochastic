import PLAStochastic.Index.CEPS.StripError.Translate
import PLAStochastic.Index.CEPS.Normal.ActualMain

/-!
# WP9: the exact exit equations with the W-6 remainders

Generic band walk `V = kWalk 0 β a` in `[0, l]`, `Z = -V` with step law
`ν ∘ (a · - β)⁻¹ = driftStep ρ μ`, `ρ` in the step class. With the up-exit `u_s` (`V < 0`) and
the down-exit `ℓ_s` (`V > l`), both marked by `e^{sZ} = e^{-sV}`
(`cepsStripExit ν β a l 0 E (-s) q`):

* `strip_upper_identity` (`Re s ≤ 0`):
  `u_s = 1 - (β₊ - s) e^{L(s)} - e^{L(s) - L(β₊)} ℓ_{β₊} - E₁(s)`,
  `‖E₁(s)‖ ≤ K₆ ‖β₊ - s‖ e^{-c₀ l/4}`;
* `strip_lower_identity` (`Re s ≥ 0`):
  `ℓ_s = e^{(β₋ - s) l} e^{L₋(s) - L₋(β₋)} (1 - u_{β₋}) + E₂(s)`,
  `‖E₂(s)‖ ≤ 2 K₆ ‖s - β₋‖ e^{-c₀ l/4}`.

These are the two-first-passage decompositions with the absolute marks of `StripError.Pass`,
the translation of `StripError.Translate`, the exact identification C-5 for the passage at `0`,
and the W-6 reward asymptotics with the vanishing factor for the passages from the exit points.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Complex
open WienerHopf

variable {ρ : Measure ℝ} {fρ : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρ fρ D θ v) (hθ : 0 < θ) (hD : 0 < D)

/-- The up-exit remainder `E₁(s)`. -/
def stripUpperErr (ν : ProbabilityMeasure ℝ) (β a : ℝ) (ρ : Measure ℝ) (μ : ℝ) (q : ℂ) (l : ℝ)
    (s : ℂ) : ℂ :=
  stripPass ν (Icc 0 l) (Ioi l) β a 0 (dom.passageRemainder ρ μ q (-s)) q

/-- The down-exit remainder `E₂(s)`. -/
def stripLowerErr (ν : ProbabilityMeasure ℝ) (β a : ℝ) (ρ : Measure ℝ) (μ : ℝ) (q : ℂ) (l : ℝ)
    (s : ℂ) : ℂ :=
  cexp (-s * (l : ℂ)) * dom.descendingPassageRemainder ρ μ q s l -
    stripPass ν (Icc 0 l) (Ioi l) (-β) (-a) l
      (fun x => cexp (-s * (l : ℂ)) * dom.descendingPassageRemainder ρ μ q s x) q

theorem norm_cexp_neg_mul_ofReal_le_one {s : ℂ} (hs : 0 ≤ s.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖cexp (-s * (x : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  refine Real.exp_le_one_iff.mpr ?_
  simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero]
  nlinarith

include hW in
theorem isProbabilityMeasure_driftStep (μ : ℝ) : IsProbabilityMeasure (driftStep ρ μ) := by
  have := hW.isProbabilityMeasure
  unfold driftStep
  exact Measure.isProbabilityMeasure_map (by fun_prop)

include hW in
theorem measurable_passageRemainder (μ : ℝ) (q a : ℂ) :
    Measurable (dom.passageRemainder ρ μ q a) := by
  have := isProbabilityMeasure_driftStep hW μ
  unfold CepsCanonDomain.passageRemainder
  exact (measurable_passageTransform _ _ _).sub (measurable_const.mul
    (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)))

include hW in
theorem measurable_descendingPassageRemainder (μ : ℝ) (q a : ℂ) :
    Measurable (dom.descendingPassageRemainder ρ μ q a) := by
  have := isProbabilityMeasure_driftStep hW μ
  have hN : IsProbabilityMeasure ((driftStep ρ μ).map Neg.neg) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold CepsCanonDomain.descendingPassageRemainder
  have hm : Measurable (descendingPassageTransform (driftStep ρ μ) (cexp (-q)) a) := by
    have he : descendingPassageTransform (driftStep ρ μ) (cexp (-q)) a =
        passageTransform ((driftStep ρ μ).map Neg.neg) (cexp (-q)) a :=
      funext fun x => descendingPassageTransform_eq_reflected _ _ x
    rw [he]
    exact measurable_passageTransform _ _ _
  exact hm.sub (measurable_const.mul
    (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)))

/-- The nonnegative part of the W-6 remainder constant. -/
def CepsCanonDomain.stripRewardConst (dom : CepsCanonDomain D θ v) : ℝ := max dom.rewardBound 0

theorem CepsCanonDomain.stripRewardConst_nonneg : 0 ≤ dom.stripRewardConst :=
  le_max_right _ _

theorem exp_neg_c_le_of_le {c x l : ℝ} (hc : 0 ≤ c) (hx : l ≤ x) :
    Real.exp (-c * x) ≤ Real.exp (-c * l) :=
  Real.exp_le_exp.mpr (by nlinarith)

include hW hθ hD in
theorem norm_passageRemainder_le' {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.renewalDiscount) {a : ℂ} (ha : ‖a‖ ≤ dom.c₀ / 2 / 2) {l x : ℝ} (hl : 0 ≤ l)
    (hx : l ≤ x) :
    ‖dom.passageRemainder ρ μ q a x‖ ≤
      dom.stripRewardConst * ‖a + cepsRootPlus D θ ρ μ q‖ * Real.exp (-(dom.c₀ / 2 / 2) * l) := by
  have h := dom.actual_passage_normal_bound_all_marks hW hθ hD hμ hq0 hq ha (hl.trans hx)
  refine h.trans ?_
  have hc : 0 ≤ dom.c₀ / 2 / 2 := by have := dom.c₀_pos; positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    (exp_neg_c_le_of_le hc hx) (Real.exp_pos _).le
    (mul_nonneg dom.stripRewardConst_nonneg (norm_nonneg _))

include hW hθ hD in
theorem norm_descendingPassageRemainder_le' {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount) {a : ℂ} (ha : ‖a‖ ≤ dom.c₀ / 2 / 2)
    {l x : ℝ} (hl : 0 ≤ l) (hx : l ≤ x) :
    ‖dom.descendingPassageRemainder ρ μ q a x‖ ≤
      dom.stripRewardConst * ‖a - cepsRootMinus D θ ρ μ q‖ * Real.exp (-(dom.c₀ / 2 / 2) * l) := by
  have h := dom.actual_descending_passage_normal_bound hW hθ hD hμ hq0 hq ha (hl.trans hx)
  refine h.trans ?_
  have hc : 0 ≤ dom.c₀ / 2 / 2 := by have := dom.c₀_pos; positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    (exp_neg_c_le_of_le hc hx) (Real.exp_pos _).le
    (mul_nonneg dom.stripRewardConst_nonneg (norm_nonneg _))

include hW hθ hD in
theorem norm_stripUpperErr_le (ν : ProbabilityMeasure ℝ) (β a : ℝ) {μ : ℝ}
    (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount)
    {l : ℝ} (hl : 0 ≤ l) {s : ℂ} (hsn : ‖s‖ ≤ dom.c₀ / 2 / 2) :
    ‖stripUpperErr dom ν β a ρ μ q l s‖ ≤
      dom.stripRewardConst * ‖-s + cepsRootPlus D θ ρ μ q‖ *
        Real.exp (-(dom.c₀ / 2 / 2) * l) := by
  unfold stripUpperErr
  have hR : 0 ≤ dom.stripRewardConst * ‖-s + cepsRootPlus D θ ρ μ q‖ *
      Real.exp (-(dom.c₀ / 2 / 2) * l) :=
    mul_nonneg (mul_nonneg dom.stripRewardConst_nonneg (norm_nonneg _)) (Real.exp_pos _).le
  exact norm_stripPass_le ν measurableSet_Icc measurableSet_Ioi (disjoint_Icc_Ioi l) β a 0 hR
    (fun x hx => norm_passageRemainder_le' dom hW hθ hD hμ hq0 hq (by rwa [norm_neg]) hl
      (le_of_lt hx)) hq0

include hW hθ hD in
theorem norm_stripLowerErr_le (ν : ProbabilityMeasure ℝ) (β a : ℝ) {μ : ℝ}
    (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount)
    {l : ℝ} (hl : 0 ≤ l) {s : ℂ} (hs : 0 ≤ s.re) (hsn : ‖s‖ ≤ dom.c₀ / 2 / 2) :
    ‖stripLowerErr dom ν β a ρ μ q l s‖ ≤
      2 * (dom.stripRewardConst * ‖s - cepsRootMinus D θ ρ μ q‖ *
        Real.exp (-(dom.c₀ / 2 / 2) * l)) := by
  unfold stripLowerErr
  set M := dom.stripRewardConst * ‖s - cepsRootMinus D θ ρ μ q‖ *
    Real.exp (-(dom.c₀ / 2 / 2) * l) with hMdef
  have hM : 0 ≤ M :=
    mul_nonneg (mul_nonneg dom.stripRewardConst_nonneg (norm_nonneg _)) (Real.exp_pos _).le
  have hpt : ∀ x : ℝ, l ≤ x →
      ‖cexp (-s * (l : ℂ)) * dom.descendingPassageRemainder ρ μ q s x‖ ≤ M := by
    intro x hx
    rw [norm_mul]
    calc _ ≤ 1 * M := mul_le_mul (norm_cexp_neg_mul_ofReal_le_one hs hl)
          (norm_descendingPassageRemainder_le' dom hW hθ hD hμ hq0 hq hsn hl hx)
          (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  have h2 := norm_stripPass_le ν measurableSet_Icc measurableSet_Ioi (disjoint_Icc_Ioi l) (-β) (-a)
    l hM (fun x hx => hpt x (le_of_lt hx)) hq0
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ M + M := add_le_add (hpt l le_rfl) h2
    _ = 2 * M := by ring

theorem norm_cexp_mul_ofReal_le_one_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) {x : ℝ} (hx : 0 ≤ x) :
    ‖cexp (z * (x : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  refine Real.exp_le_one_iff.mpr ?_
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  nlinarith

include hW hθ hD in
/-- **The up-exit equation (I)** with the W-6 remainder of the passages from the high exit. -/
theorem strip_upper_identity (ν : ProbabilityMeasure ℝ) (β a : ℝ) {μ : ℝ}
    (hlink : (ν : Measure ℝ).map (fun x => a * x - β) = driftStep ρ μ)
    (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount)
    {l : ℝ} (hl : 0 ≤ l) {s : ℂ} (hs : s.re ≤ 0) (hsn : ‖s‖ ≤ dom.c₀ / 2 / 2) :
    cepsStripExit ν β a l 0 (Iio 0) (-s) q =
      1 - (cepsRootPlus D θ ρ μ q - s) * cexp (dom.canonL ρ μ q s) -
        cexp (dom.canonL ρ μ q s - dom.canonL ρ μ q (cepsRootPlus D θ ρ μ q)) *
          cepsStripExit ν β a l 0 (Ioi l) (-cepsRootPlus D θ ρ μ q) q -
        stripUpperErr dom ν β a ρ μ q l s := by
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  have hq0' : ‖q‖ ≤ dom.q₀ := hq.trans (min_le_left _ _)
  have hsign := (cepsRoots_re_signs dom hW hθ hD hμ0 hq0 hq0').1
  set βp := cepsRootPlus D θ ρ μ q with hβp
  set C := cexp (dom.canonL ρ μ q s - dom.canonL ρ μ q βp) with hCdef
  set φ : ℝ → ℂ := fun v => cexp (-s * (v : ℂ)) with hφdef
  have hφm : Measurable φ :=
    Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)
  have hφ : ∀ v ∈ Iio (0 : ℝ), ‖φ v‖ ≤ 1 := by
    intro v hv
    simp only [hφdef]
    rw [Complex.norm_exp]
    refine Real.exp_le_one_iff.mpr ?_
    simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero]
    have : v < 0 := hv
    nlinarith
  have hdec := stripPass_below_decomp ν β a (l := l) (y := 0) ⟨le_rfl, hl⟩ hφm hφ hq0
  have hT := stripPass_below_eq_passageTransform ν β a (x := 0) le_rfl (t := s) hs hq0
  rw [hlink, passageTransform_zero_eq_asc, neg_neg] at hT
  have hC5 := ((dom.cepsWHIdent hW hθ hD) μ hμ0 q hq0 hq0').1 s
    (by linarith [dom.c₀_pos])
  have hU : stripPass ν (Icc 0 l) (Iio 0) β a 0 φ q = cepsStripExit ν β a l 0 (Iio 0) (-s) q := by
    rw [cepsStripExit_zero_eq_stripPass]
  have hP : ∀ x ∈ Ioi l, stripPass ν (Ici 0) (Iio 0) β a x φ q =
      C * cexp (-βp * (x : ℂ)) + dom.passageRemainder ρ μ q (-s) x := by
    intro x hx
    have hx0 : 0 ≤ x := hl.trans (le_of_lt hx)
    rw [stripPass_below_eq_passageTransform ν β a hx0 hs hq0, hlink]
    unfold CepsCanonDomain.passageRemainder
    rw [neg_neg]
    ring
  have hφ1m : Measurable fun x : ℝ => C * cexp (-βp * (x : ℂ)) :=
    measurable_const.mul (Complex.measurable_exp.comp (measurable_const.mul
      Complex.measurable_ofReal))
  have hφ1 : ∀ x ∈ Ioi l, ‖C * cexp (-βp * (x : ℂ))‖ ≤ ‖C‖ := by
    intro x hx
    rw [norm_mul]
    have hx0 : 0 ≤ x := hl.trans (le_of_lt hx)
    calc _ ≤ ‖C‖ * 1 := mul_le_mul_of_nonneg_left
          (norm_cexp_neg_mul_ofReal_le_one hsign hx0) (norm_nonneg _)
      _ = ‖C‖ := mul_one _
  have hφ2 : ∀ x ∈ Ioi l, ‖dom.passageRemainder ρ μ q (-s) x‖ ≤
      dom.stripRewardConst * ‖-s + βp‖ * Real.exp (-(dom.c₀ / 2 / 2) * l) := fun x hx =>
    norm_passageRemainder_le' dom hW hθ hD hμ hq0 hq (by rwa [norm_neg]) hl (le_of_lt hx)
  have hHigh : stripPass ν (Icc 0 l) (Ioi l) β a 0
      (fun x => stripPass ν (Ici 0) (Iio 0) β a x φ q) q =
      C * cepsStripExit ν β a l 0 (Ioi l) (-βp) q + stripUpperErr dom ν β a ρ μ q l s := by
    rw [stripPass_congr ν (Icc 0 l) (Ioi l) β a 0 hP q,
      stripPass_add ν measurableSet_Icc measurableSet_Ioi (disjoint_Icc_Ioi l) β a 0 hφ1m
        (measurable_passageRemainder dom hW μ q (-s)) hφ1 hφ2 hq0,
      stripPass_const_mul, cepsStripExit_zero_eq_stripPass]
    rfl
  rw [hdec, hU, hHigh] at hT
  linear_combination hT - hC5

include hW hθ hD in
/-- **The down-exit equation (II)** with the W-6 remainders of the downcrossings. -/
theorem strip_lower_identity (ν : ProbabilityMeasure ℝ) (β a : ℝ) {μ : ℝ}
    (hlink : (ν : Measure ℝ).map (fun x => a * x - β) = driftStep ρ μ)
    (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount)
    {l : ℝ} (hl : 0 ≤ l) {s : ℂ} (hs : 0 ≤ s.re) (hsn : ‖s‖ ≤ dom.c₀ / 2 / 2) :
    cepsStripExit ν β a l 0 (Ioi l) (-s) q =
      cexp ((cepsRootMinus D θ ρ μ q - s) * (l : ℂ)) *
          cexp (dom.canonLMinus ρ μ q s - dom.canonLMinus ρ μ q (cepsRootMinus D θ ρ μ q)) *
          (1 - cepsStripExit ν β a l 0 (Iio 0) (-cepsRootMinus D θ ρ μ q) q) +
        stripLowerErr dom ν β a ρ μ q l s := by
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  have hq0' : ‖q‖ ≤ dom.q₀ := hq.trans (min_le_left _ _)
  have hsign := (cepsRoots_re_signs dom hW hθ hD hμ0 hq0 hq0').2
  set βm := cepsRootMinus D θ ρ μ q with hβm
  set Cm := cexp (dom.canonLMinus ρ μ q s - dom.canonLMinus ρ μ q βm) with hCmdef
  set E := cexp (-s * (l : ℂ)) with hEdef
  set φ : ℝ → ℂ := fun v => cexp (-s * ((l - v : ℝ) : ℂ)) with hφdef
  have hφm : Measurable φ :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_const.sub measurable_id)))
  have hφ : ∀ v ∈ Iio (0 : ℝ), ‖φ v‖ ≤ 1 := by
    intro v hv
    have : v < 0 := hv
    exact norm_cexp_neg_mul_ofReal_le_one hs (by linarith)
  have hdec := stripPass_below_decomp ν (-β) (-a) (l := l) (y := l) ⟨hl, le_rfl⟩ hφm hφ hq0
  have hT := stripPass_reflected_eq_descending ν β a l (x := l) hl (t := s) hs hq0
  rw [hlink] at hT
  have hD' : ∀ x : ℝ, descendingPassageTransform (driftStep ρ μ) (cexp (-q)) s x =
      Cm * cexp (βm * (x : ℂ)) + dom.descendingPassageRemainder ρ μ q s x := by
    intro x
    unfold CepsCanonDomain.descendingPassageRemainder
    ring
  have hLow : stripPass ν (Icc 0 l) (Iio 0) (-β) (-a) l φ q =
      cepsStripExit ν β a l 0 (Ioi l) (-s) q := by
    have h := cepsStripExit_reflect_low ν β a l 0 (-s) q
    rw [cepsStripExit_eq_stripPass, sub_zero, neg_neg] at h
    rw [← h]
    refine stripPass_congr ν (Icc 0 l) (Iio 0) (-β) (-a) l (fun v _ => ?_) q
    simp only [hφdef]
    congr 1
    push_cast
    ring
  have hExp : stripPass ν (Icc 0 l) (Ioi l) (-β) (-a) l (fun x => cexp (βm * (x : ℂ))) q =
      cexp (βm * (l : ℂ)) * cepsStripExit ν β a l 0 (Iio 0) (-βm) q := by
    have h := cepsStripExit_reflect_high ν β a l 0 (-βm) q
    rw [cepsStripExit_eq_stripPass, sub_zero, neg_neg] at h
    rw [← h, ← stripPass_const_mul]
    refine stripPass_congr ν (Icc 0 l) (Ioi l) (-β) (-a) l (fun x _ => ?_) q
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hP : ∀ x ∈ Ioi l, stripPass ν (Ici 0) (Iio 0) (-β) (-a) x φ q =
      E * Cm * cexp (βm * (x : ℂ)) + E * dom.descendingPassageRemainder ρ μ q s x := by
    intro x hx
    have hx0 : 0 ≤ x := hl.trans (le_of_lt hx)
    rw [stripPass_reflected_eq_descending ν β a l hx0 hs hq0, hlink, hD']
    ring
  have hφ1m : Measurable fun x : ℝ => E * Cm * cexp (βm * (x : ℂ)) :=
    measurable_const.mul (Complex.measurable_exp.comp (measurable_const.mul
      Complex.measurable_ofReal))
  have hφ1 : ∀ x ∈ Ioi l, ‖E * Cm * cexp (βm * (x : ℂ))‖ ≤ ‖E * Cm‖ := by
    intro x hx
    rw [norm_mul]
    have hx0 : 0 ≤ x := hl.trans (le_of_lt hx)
    calc _ ≤ ‖E * Cm‖ * 1 := mul_le_mul_of_nonneg_left
          (norm_cexp_mul_ofReal_le_one_of_re_nonpos hsign hx0) (norm_nonneg _)
      _ = ‖E * Cm‖ := mul_one _
  have hφ2m : Measurable fun x : ℝ => E * dom.descendingPassageRemainder ρ μ q s x :=
    measurable_const.mul (measurable_descendingPassageRemainder dom hW μ q s)
  have hφ2 : ∀ x ∈ Ioi l, ‖E * dom.descendingPassageRemainder ρ μ q s x‖ ≤
      dom.stripRewardConst * ‖s - βm‖ * Real.exp (-(dom.c₀ / 2 / 2) * l) := by
    intro x hx
    rw [norm_mul]
    calc _ ≤ 1 * (dom.stripRewardConst * ‖s - βm‖ * Real.exp (-(dom.c₀ / 2 / 2) * l)) :=
          mul_le_mul (norm_cexp_neg_mul_ofReal_le_one hs hl)
            (norm_descendingPassageRemainder_le' dom hW hθ hD hμ hq0 hq hsn hl (le_of_lt hx))
            (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hHigh : stripPass ν (Icc 0 l) (Ioi l) (-β) (-a) l
      (fun x => stripPass ν (Ici 0) (Iio 0) (-β) (-a) x φ q) q =
      E * Cm * (cexp (βm * (l : ℂ)) * cepsStripExit ν β a l 0 (Iio 0) (-βm) q) +
        stripPass ν (Icc 0 l) (Ioi l) (-β) (-a) l
          (fun x => E * dom.descendingPassageRemainder ρ μ q s x) q := by
    rw [stripPass_congr ν (Icc 0 l) (Ioi l) (-β) (-a) l hP q,
      stripPass_add ν measurableSet_Icc measurableSet_Ioi (disjoint_Icc_Ioi l) (-β) (-a) l hφ1m
        hφ2m hφ1 hφ2 hq0, stripPass_const_mul, hExp]
  rw [hdec, hLow, hHigh, hD'] at hT
  have hEE : cexp ((βm - s) * (l : ℂ)) = E * cexp (βm * (l : ℂ)) := by
    rw [hEdef, ← Complex.exp_add]
    congr 1
    ring
  unfold stripLowerErr
  rw [hEE]
  linear_combination hT

end

end PGM
