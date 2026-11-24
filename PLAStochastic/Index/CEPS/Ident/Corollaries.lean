import PLAStochastic.Index.CEPS.Ident.CorollariesQ

/-!
# CEPS C-6: ladder corollaries of the Wiener–Hopf identification

Blueprint §3.3 (3.6)–(3.7) and §4.2 C-6. The only premise beyond the class setting is the
identification `hI : CepsWHIdent dom ρW` (C-5, frozen in `Ident.Statement`). For a class step
law, real `|μ| ≤ μ₀` and `0 ≤ Re q`, `‖q‖ ≤ q₀`, with `A₊ = ascTransform (driftStep ρW μ) e^{-q}`,
`A₋ = descTransform …`, `β± = cepsRootPlus/Minus`, `L = dom.canonL`, `L₋ = dom.canonLMinus`,
`Q = cepsQ`:

* (3.4) `CepsC6.cexp_canonL_add_canonLMinus`: `e^{L + L₋} = Q` on `|Re ζ| ≤ 2 c₀` (no premise);
* residues: `hasDerivAt_ascTransform_rootPlus` (`A₊'(β₊) = e^{L(β₊)}`) and
  `hasDerivAt_descTransform_rootMinus` (`A₋'(β₋) = -e^{L₋(β₋)}`);
* overshoot transforms `cepsOvershootPlus` (`B₊(s) = (1 - A₊(β₊ - s))/(s A₊'(β₊))`) and
  `cepsOvershootMinus` (`B₋(s) = (1 - A₋(β₋ + s))/(-s A₋'(β₋))`):
  `cepsOvershootPlus_eq` (`B₊(s) = e^{L(β₊-s) - L(β₊)}`), `cepsOvershootMinus_eq`
  (`B₋(s) = e^{L₋(β₋+s) - L₋(β₋)}`);
* `c±`: `one_sub_ascTransform_zero` (`1 - A₊(0) = β₊ e^{ℓ}`), `one_sub_descTransform_zero`
  (`1 - A₋(0) = -β₋ e^{L₋(0)}`), `CepsC6.cexp_canonEll_mul_cexp_canonLMinus_zero`
  (`e^{ℓ} e^{L₋(0)} = Q(0)`), `CepsC6.cepsQ_zero_mul` (`Q(0)(-β₊β₋) = 1 - e^{-q}`);
* (3.7): `cepsOvershoot_mul_eq` (`Π = B₊(η)B₋(η) = ψ'(β₊)/(-ψ'(β₋)) e^{2L(β₋) - 2L(β₊)}`) and
  `cepsLadderN_eq` (`N_t = e^{L(β₋) - L(t)} B₋(t - β₋) = Q(t)/Q(β₋) e^{2L(β₋) - 2L(t)}`);
* the line bound `ladderLineConst_le_norm` (`c ≤ ‖1 - A₊(ζ)‖` on `Re ζ ≤ c₀/2 ≤ |Re ζ|`, in
  particular on both lines `Re ζ = ±c₀/2`), with the class constant `ladderLineConst dom > 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

/-- `B₊(s) = (1 - A₊(β₊ - s))/(s A₊'(β₊))`: the Laplace transform of the stationary ascending
overshoot (under the `β₊` tilt for real `q > 0`). -/
def cepsOvershootPlus (D θ : ℝ) (ρW : Measure ℝ) (μ : ℝ) (q s : ℂ) : ℂ :=
  (1 - ascTransform (driftStep ρW μ) (cexp (-q)) (cepsRootPlus D θ ρW μ q - s)) /
    (s * deriv (fun ζ => ascTransform (driftStep ρW μ) (cexp (-q)) ζ) (cepsRootPlus D θ ρW μ q))

/-- `B₋(s) = (1 - A₋(β₋ + s))/(-s A₋'(β₋))`: the descending counterpart. -/
def cepsOvershootMinus (D θ : ℝ) (ρW : Measure ℝ) (μ : ℝ) (q s : ℂ) : ℂ :=
  (1 - descTransform (driftStep ρW μ) (cexp (-q)) (cepsRootMinus D θ ρW μ q + s)) /
    (-s * deriv (fun ζ => descTransform (driftStep ρW μ) (cexp (-q)) ζ)
      (cepsRootMinus D θ ρW μ q))

namespace CepsC6

/-- If `1 - A = (· - b) E` on an open neighbourhood of `b` and `E` is differentiable at `b`, then
`A'(b) = -E(b)`. -/
theorem hasDerivAt_of_one_sub_eq {A E : ℂ → ℂ} {b : ℂ} {U : Set ℂ} (hU : IsOpen U) (hb : b ∈ U)
    (h : ∀ z ∈ U, 1 - A z = (z - b) * E z) (hE : DifferentiableAt ℂ E b) :
    HasDerivAt A (-E b) b := by
  have h2 : HasDerivAt (fun z => 1 - (z - b) * E z)
      (-(1 * E b + (b - b) * deriv E b)) b :=
    (((hasDerivAt_id' b).sub_const b).mul hE.hasDerivAt).const_sub 1
  have he : A =ᶠ[𝓝 b] fun z => 1 - (z - b) * E z := by
    filter_upwards [hU.mem_nhds hb] with z hz
    rw [← h z hz]; ring
  exact (h2.congr_of_eventuallyEq he).congr_deriv (by simp)

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

/-- `e^{L₋} = Q e^{-L}` wherever `Q ≠ 0`. -/
theorem cexp_canonLMinus_eq (dom : CepsCanonDomain D θ v) {μ q ζ : ℂ}
    (hQ : cepsQ D θ ρW μ q ζ ≠ 0) :
    cexp (dom.canonLMinus ρW μ q ζ) = cepsQ D θ ρW μ q ζ * cexp (-dom.canonL ρW μ q ζ) := by
  rw [CepsCanonDomain.canonLMinus, sub_eq_add_neg, Complex.exp_add, Complex.exp_log hQ]

variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- **(3.4).** `e^{L + L₋} = Q` on the strip `|Re ζ| ≤ 2 c₀`. -/
theorem cexp_canonL_add_canonLMinus {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {ζ : ℂ} (hζ : |ζ.re| ≤ 2 * dom.c₀) :
    cexp (dom.canonL ρW μ q ζ + dom.canonLMinus ρW μ q ζ) = cepsQ D θ ρW μ q ζ := by
  rw [CepsCanonDomain.canonLMinus, add_sub_cancel, Complex.exp_log
    (cepsQ_ne_zero dom hW hθ hD hμ hq hζ)]

/-- `e^{ℓ} e^{L₋(0)} = Q(0)`. -/
theorem cexp_canonEll_mul_cexp_canonLMinus_zero {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ}
    (hq : ‖q‖ ≤ dom.q₀) :
    cexp (dom.canonEll ρW μ q) * cexp (dom.canonLMinus ρW μ q 0) = cepsQ D θ ρW μ q 0 := by
  rw [← Complex.exp_add, CepsCanonDomain.canonEll]
  exact cexp_canonL_add_canonLMinus dom hW hθ hD hμ hq (by simp [dom.c₀_pos.le])

/-- `Q(0) (-β₊ β₋) = 1 - e^{-q}`. -/
theorem cepsQ_zero_mul {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) :
    cepsQ D θ ρW μ q 0 * (-(cepsRootPlus D θ ρW μ q * cepsRootMinus D θ ρW μ q)) =
      1 - cexp (-q) := by
  have h := cepsD_eq_mul_cepsQ dom hW hθ hD hμ hq 0
  rw [cepsD, stepTransform_zero hW, mul_zero, Complex.exp_zero, mul_one, mul_one] at h
  rw [h]; ring

end CepsC6

namespace CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
  (hI : CepsWHIdent dom ρW)
include hW hθ hD hI

/-- `A₊(β₊) = 1`. -/
theorem ascTransform_rootPlus {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) :
    ascTransform (driftStep ρW μ) (cexp (-q)) (cepsRootPlus D θ ρW μ q) = 1 := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hb := mem_ball_zero_iff.mp (CepsC6.rootPlus_mem_ball dom hW hθ hD hμ' hq)
  have h := (hI μ hμ q hq0 hq).1 _ (lt_of_le_of_lt (re_le_norm _) hb)
  rw [sub_self, zero_mul, sub_eq_zero] at h
  exact h.symm

/-- **Residue.** `A₊'(β₊) = e^{L(β₊)}`. -/
theorem hasDerivAt_ascTransform_rootPlus {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) :
    HasDerivAt (fun ζ => ascTransform (driftStep ρW μ) (cexp (-q)) ζ)
      (cexp (dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q))) (cepsRootPlus D θ ρW μ q) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hb := mem_ball_zero_iff.mp (CepsC6.rootPlus_mem_ball dom hW hθ hD hμ' hq)
  have hbre : (cepsRootPlus D θ ρW μ q).re < dom.c₀ := lt_of_le_of_lt (re_le_norm _) hb
  have hE : DifferentiableAt ℂ (fun z => -cexp (dom.canonL ρW μ q z)) (cepsRootPlus D θ ρW μ q) :=
    (CepsC6.differentiableAt_canonL dom hW hθ hD hμ hq hbre).cexp.neg
  have h := CepsC6.hasDerivAt_of_one_sub_eq (A := fun ζ => ascTransform (driftStep ρW μ)
    (cexp (-q)) ζ) (isOpen_lt continuous_re continuous_const) hbre
    (fun z hz => by rw [(hI μ hμ q hq0 hq).1 z hz]; ring) hE
  simpa only [neg_neg] using h

/-- `A₋(β₋) = 1`. -/
theorem descTransform_rootMinus {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) :
    descTransform (driftStep ρW μ) (cexp (-q)) (cepsRootMinus D θ ρW μ q) = 1 := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hb := mem_ball_zero_iff.mp (CepsC6.rootMinus_mem_ball dom hW hθ hD hμ' hq)
  have h := (hI μ hμ q hq0 hq).2 _ (lt_of_le_of_lt (abs_re_le_norm _) hb)
  rw [sub_self, zero_mul, sub_eq_zero] at h
  exact h.symm

/-- **Residue.** `A₋'(β₋) = -e^{L₋(β₋)}`. -/
theorem hasDerivAt_descTransform_rootMinus {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) :
    HasDerivAt (fun ζ => descTransform (driftStep ρW μ) (cexp (-q)) ζ)
      (-cexp (dom.canonLMinus ρW μ q (cepsRootMinus D θ ρW μ q))) (cepsRootMinus D θ ρW μ q) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hbB := CepsC6.rootMinus_mem_ball dom hW hθ hD hμ' hq
  have hb := mem_ball_zero_iff.mp hbB
  have hbre : (cepsRootMinus D θ ρW μ q).re < dom.c₀ := lt_of_le_of_lt (re_le_norm _) hb
  have hsub := CepsC6.ball_c₀_subset dom
  have hE : DifferentiableAt ℂ (fun z => cepsQ D θ ρW μ q z * cexp (-dom.canonL ρW μ q z))
      (cepsRootMinus D θ ρW μ q) :=
    (CepsC6.differentiableAt_cepsQ dom hW hθ hD hμ' hq (hsub hbB)).mul
      (CepsC6.differentiableAt_canonL dom hW hθ hD hμ hq hbre).neg.cexp
  have h := CepsC6.hasDerivAt_of_one_sub_eq (A := fun ζ => descTransform (driftStep ρW μ)
    (cexp (-q)) ζ) isOpen_ball hbB (fun z hz => by
      have hz' := mem_ball_zero_iff.mp hz
      rw [(hI μ hμ q hq0 hq).2 z (lt_of_le_of_lt (abs_re_le_norm _) hz'),
        CepsC6.cexp_canonLMinus_eq dom
          (CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq (hsub hz))]) hE
  rwa [CepsC6.cexp_canonLMinus_eq dom
    (CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq (hsub hbB))]

/-- **Ascending overshoot transform.** `B₊(s) = e^{L(β₊ - s) - L(β₊)}`. -/
theorem cepsOvershootPlus_eq {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) {s : ℂ} (hs : s ≠ 0) (hsc : (cepsRootPlus D θ ρW μ q - s).re < dom.c₀) :
    cepsOvershootPlus D θ ρW μ q s =
      cexp (dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q - s) -
        dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q)) := by
  rw [cepsOvershootPlus, (hasDerivAt_ascTransform_rootPlus dom hW hθ hD hI hμ hq0 hq).deriv,
    (hI μ hμ q hq0 hq).1 _ hsc, sub_sub_cancel, Complex.exp_sub, mul_div_mul_left _ _ hs]

/-- **Descending overshoot transform.** `B₋(s) = e^{L₋(β₋ + s) - L₋(β₋)}`. -/
theorem cepsOvershootMinus_eq {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) {s : ℂ} (hs : s ≠ 0)
    (hsc : |(cepsRootMinus D θ ρW μ q + s).re| < dom.c₀) :
    cepsOvershootMinus D θ ρW μ q s =
      cexp (dom.canonLMinus ρW μ q (cepsRootMinus D θ ρW μ q + s) -
        dom.canonLMinus ρW μ q (cepsRootMinus D θ ρW μ q)) := by
  rw [cepsOvershootMinus, (hasDerivAt_descTransform_rootMinus dom hW hθ hD hI hμ hq0 hq).deriv,
    (hI μ hμ q hq0 hq).2 _ hsc, add_sub_cancel_left, neg_mul_neg, Complex.exp_sub,
    mul_div_mul_left _ _ hs]

omit hW hθ hD in
/-- `c₊`: `1 - A₊(0) = β₊ e^{ℓ}`. -/
theorem one_sub_ascTransform_zero {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) :
    1 - ascTransform (driftStep ρW μ) (cexp (-q)) 0 =
      cepsRootPlus D θ ρW μ q * cexp (dom.canonEll ρW μ q) := by
  rw [(hI μ hμ q hq0 hq).1 0 (by simp [dom.c₀_pos]), sub_zero, canonEll]

omit hW hθ hD in
/-- `c₋`: `1 - A₋(0) = -β₋ e^{L₋(0)}`. -/
theorem one_sub_descTransform_zero {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) :
    1 - descTransform (driftStep ρW μ) (cexp (-q)) 0 =
      -cepsRootMinus D θ ρW μ q * cexp (dom.canonLMinus ρW μ q 0) := by
  rw [(hI μ hμ q hq0 hq).2 0 (by simp [dom.c₀_pos]), zero_sub]

/-- **(3.7), root product.** For `η = β₊ - β₋ ≠ 0`,
`Π = B₊(η) B₋(η) = ψ_μ'(β₊)/(-ψ_μ'(β₋)) · e^{2L(β₋) - 2L(β₊)}`. -/
theorem cepsOvershoot_mul_eq {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀)
    (hη : cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q ≠ 0) :
    cepsOvershootPlus D θ ρW μ q (cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q) *
        cepsOvershootMinus D θ ρW μ q (cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q) =
      deriv (cepsCgfShift ρW μ) (cepsRootPlus D θ ρW μ q) /
          (-deriv (cepsCgfShift ρW μ) (cepsRootMinus D θ ρW μ q)) *
        cexp (2 * dom.canonL ρW μ q (cepsRootMinus D θ ρW μ q) -
          2 * dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q)) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hc0 := dom.c₀_pos
  have hbp := CepsC6.rootPlus_mem_ball dom hW hθ hD hμ' hq
  have hbm := CepsC6.rootMinus_mem_ball dom hW hθ hD hμ' hq
  have hsub := CepsC6.ball_c₀_subset dom
  have hQp := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq (hsub hbp)
  have hQm := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq (hsub hbm)
  have hp := CepsC6.cepsQ_rootPlus_mul dom hW hθ hD hμ' hq
  have hm := CepsC6.cepsQ_rootMinus_mul dom hW hθ hD hμ' hq
  have hB1 := cepsOvershootPlus_eq dom hW hθ hD hI hμ hq0 hq hη (by
    rw [sub_sub_cancel]
    exact lt_of_le_of_lt (re_le_norm _) (mem_ball_zero_iff.mp hbm))
  have hB2 := cepsOvershootMinus_eq dom hW hθ hD hI hμ hq0 hq hη (by
    rw [add_sub_cancel]
    exact lt_of_le_of_lt (abs_re_le_norm _) (mem_ball_zero_iff.mp hbp))
  rw [sub_sub_cancel] at hB1
  rw [add_sub_cancel] at hB2
  rw [hB1, hB2, ← Complex.exp_add]
  set Lp := dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q)
  set Lm := dom.canonL ρW μ q (cepsRootMinus D θ ρW μ q)
  set Qp := cepsQ D θ ρW μ q (cepsRootPlus D θ ρW μ q)
  set Qm := cepsQ D θ ρW μ q (cepsRootMinus D θ ρW μ q)
  have e : Lm - Lp + (dom.canonLMinus ρW μ q (cepsRootPlus D θ ρW μ q) -
      dom.canonLMinus ρW μ q (cepsRootMinus D θ ρW μ q)) =
        (2 * Lm - 2 * Lp) + (Complex.log Qp - Complex.log Qm) := by
    simp only [canonLMinus, Lp, Lm, Qp, Qm]; ring
  rw [e, Complex.exp_add, Complex.exp_sub (Complex.log Qp), Complex.exp_log hQp,
    Complex.exp_log hQm, ← hp, ← hm]
  change cexp (2 * Lm - 2 * Lp) * (Qp / Qm) =
    (Qp * _ / (Qm * _)) * cexp (2 * Lm - 2 * Lp)
  rw [mul_div_mul_right _ _ hη]
  ring

/-- **(3.7), the factor `N_t`.** For `t ≠ β₋` with `|Re t| < c₀`,
`N_t = e^{L(β₋) - L(t)} B₋(t - β₋) = Q(t)/Q(β₋) · e^{2L(β₋) - 2L(t)}`. -/
theorem cepsLadderN_eq {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) {t : ℂ} (ht : t ≠ cepsRootMinus D θ ρW μ q) (htc : |t.re| < dom.c₀) :
    cexp (dom.canonL ρW μ q (cepsRootMinus D θ ρW μ q) - dom.canonL ρW μ q t) *
        cepsOvershootMinus D θ ρW μ q (t - cepsRootMinus D θ ρW μ q) =
      cepsQ D θ ρW μ q t / cepsQ D θ ρW μ q (cepsRootMinus D θ ρW μ q) *
        cexp (2 * dom.canonL ρW μ q (cepsRootMinus D θ ρW μ q) - 2 * dom.canonL ρW μ q t) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hc0 := dom.c₀_pos
  have hbm := CepsC6.rootMinus_mem_ball dom hW hθ hD hμ' hq
  have hsub := CepsC6.ball_c₀_subset dom
  have hQm := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq (hsub hbm)
  have hQt := CepsC6.cepsQ_ne_zero dom hW hθ hD hμ hq (z := t) (by linarith)
  have hB := cepsOvershootMinus_eq dom hW hθ hD hI hμ hq0 hq (sub_ne_zero.mpr ht)
    (by rw [add_sub_cancel]; exact htc)
  rw [add_sub_cancel] at hB
  rw [hB, ← Complex.exp_add]
  set Lm := dom.canonL ρW μ q (cepsRootMinus D θ ρW μ q)
  set Lt := dom.canonL ρW μ q t
  set Qt := cepsQ D θ ρW μ q t
  set Qm := cepsQ D θ ρW μ q (cepsRootMinus D θ ρW μ q)
  have e : Lm - Lt + (dom.canonLMinus ρW μ q t -
      dom.canonLMinus ρW μ q (cepsRootMinus D θ ρW μ q)) =
        (2 * Lm - 2 * Lt) + (Complex.log Qt - Complex.log Qm) := by
    simp only [canonLMinus, Lt, Lm, Qt, Qm]; ring
  rw [e, Complex.exp_add, Complex.exp_sub (Complex.log Qt), Complex.exp_log hQt,
    Complex.exp_log hQm]
  ring

omit hW hθ hD hI in
/-- The class constant of the line bound: `e^{-C_L(2D²/θ + 3/(2c₀))} · (c₀/4)/(2 + c₀/4)`. -/
def ladderLineConst (dom : CepsCanonDomain D θ v) : ℝ :=
  Real.exp (-(dom.CL * (2 * D ^ 2 / θ + 3 / (2 * dom.c₀)))) * (dom.c₀ / 4 / (2 + dom.c₀ / 4))

omit hW hθ hD hI in
theorem ladderLineConst_pos : 0 < dom.ladderLineConst := by
  have := dom.c₀_pos
  unfold ladderLineConst
  positivity

/-- **Line bound (input of W-5).** `c ≤ ‖1 - A₊(ζ)‖` for `Re ζ ≤ c₀/2 ≤ |Re ζ|`, with
`c = ladderLineConst dom` depending only on the class domain. -/
theorem ladderLineConst_le_norm {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) {ζ : ℂ} (hζ1 : ζ.re ≤ dom.c₀ / 2) (hζ2 : dom.c₀ / 2 ≤ |ζ.re|) :
    dom.ladderLineConst ≤ ‖1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ‖ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hμi : (μ : ℂ).im = 0 := ofReal_im μ
  have hc0 := dom.c₀_pos
  have hcle := dom.c₀_le
  have hρ1 := dom.ρA_one
  have hbn := dom.norm_rootPlus_le hW hθ hD hμ' hq
  set bp := cepsRootPlus D θ ρW μ q with hbpdef
  set C := dom.CL * (2 * D ^ 2 / θ + 3 / (2 * dom.c₀)) with hC
  have hΛ : ‖dom.canonL ρW μ q ζ + Complex.log (((1 : ℝ) : ℂ) - ζ)‖ ≤ C :=
    dom.norm_cepsCanonL_add_log_le hW hθ hD (γ := 1) (by norm_num) le_rfl (c := dom.c₀) le_rfl
      (by linarith) hμ' hμi hq hζ1
  set Λ := dom.canonL ρW μ q ζ + Complex.log (((1 : ℝ) : ℂ) - ζ) with hΛdef
  have h1z : (((1 : ℝ) : ℂ) - ζ) ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have hL : dom.canonL ρW μ q ζ = Λ - Complex.log (((1 : ℝ) : ℂ) - ζ) := by rw [hΛdef]; ring
  have hexp : ‖cexp (dom.canonL ρW μ q ζ)‖ = ‖cexp Λ‖ / ‖((1 : ℝ) : ℂ) - ζ‖ := by
    rw [hL, Complex.exp_sub, Complex.exp_log h1z, norm_div]
  have hΛre : Real.exp (-C) ≤ ‖cexp Λ‖ := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by linarith [neg_abs_le Λ.re, abs_re_le_norm Λ])
  -- `‖β₊ - ζ‖ ≥ c₀/4`
  set x := ‖bp - ζ‖ with hx
  have hx1 : dom.c₀ / 4 ≤ x := by
    have h1 : |(bp - ζ).re| ≤ x := abs_re_le_norm _
    have h2 : |bp.re| ≤ dom.c₀ / 4 := (abs_re_le_norm bp).trans hbn
    rw [sub_re] at h1
    have := abs_sub_abs_le_abs_sub ζ.re bp.re
    rw [abs_sub_comm] at this
    linarith
  have hy0 : 0 < ‖((1 : ℝ) : ℂ) - ζ‖ := norm_pos_iff.mpr h1z
  have hy : ‖((1 : ℝ) : ℂ) - ζ‖ ≤ 2 + x := by
    calc ‖((1 : ℝ) : ℂ) - ζ‖ = ‖(((1 : ℝ) : ℂ) - bp) + (bp - ζ)‖ := by ring_nf
      _ ≤ ‖((1 : ℝ) : ℂ) - bp‖ + x := norm_add_le _ _
      _ ≤ (1 + dom.c₀ / 4) + x := by
          gcongr
          calc ‖((1 : ℝ) : ℂ) - bp‖ ≤ ‖((1 : ℝ) : ℂ)‖ + ‖bp‖ := norm_sub_le _ _
            _ ≤ 1 + dom.c₀ / 4 := by simp only [ofReal_one, norm_one]; linarith
      _ ≤ 2 + x := by linarith
  rw [(hI μ hμ q hq0 hq).1 ζ (by linarith), norm_mul, hexp]
  unfold ladderLineConst
  rw [← hC]
  have hx0 : 0 < x := by linarith
  have hfrac : dom.c₀ / 4 / (2 + dom.c₀ / 4) ≤ x / ‖((1 : ℝ) : ℂ) - ζ‖ := by
    calc dom.c₀ / 4 / (2 + dom.c₀ / 4) ≤ x / (2 + x) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      _ ≤ x / ‖((1 : ℝ) : ℂ) - ζ‖ := div_le_div_of_nonneg_left hx0.le hy0 hy
  calc Real.exp (-C) * (dom.c₀ / 4 / (2 + dom.c₀ / 4))
      ≤ ‖cexp Λ‖ * (x / ‖((1 : ℝ) : ℂ) - ζ‖) :=
        mul_le_mul hΛre hfrac (by positivity) (norm_nonneg _)
    _ = x * (‖cexp Λ‖ / ‖((1 : ℝ) : ℂ) - ζ‖) := by ring

/-- The line bound on the two lines `Re ζ = ±c₀/2`. -/
theorem ladderLineConst_le_norm_of_abs_re_eq {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) {ζ : ℂ} (hζ : |ζ.re| = dom.c₀ / 2) :
    dom.ladderLineConst ≤ ‖1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ‖ :=
  ladderLineConst_le_norm dom hW hθ hD hI hμ hq0 hq (le_of_abs_le hζ.le) hζ.ge

end CepsCanonDomain

end PGM
