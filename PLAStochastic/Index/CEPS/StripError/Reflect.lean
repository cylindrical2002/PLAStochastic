import PLAStochastic.Index.CEPS.StripError.EntranceTop
import PLAStochastic.Index.CEPS.Reward.CanonicalReflection

/-!
# WP9: the reflected normal entrance is the lower-end normal entrance

For the reflected step law `ρN = ρ ∘ neg⁻¹` at drift `-μ` the root-zone data satisfy the
dictionary `β₊' = -β₋`, `β₋' = -β₊`, `Q'(-ζ) = Q(ζ)`, `e^{L'(-ζ)} = e^{L₋(ζ)}`
(`stripReflect_dictionary`, from the W-6 reflection identities). Consequently `Π' = Π`, the marked
factor at mark zero is the reflected factor, and the reflected top-started normal entrance at mark
`0` is exactly the X5 lower-end entrance `bottomEntrance` of the original data
(`stripReflect_entrance_eq_bottom`). This identifies the bottom-started actual entrance error of
`EntranceTop` with the normal object entering the width Hadamard identity (S-4).
-/

namespace PGM

noncomputable section

open MeasureTheory Set Complex Metric
open WienerHopf

variable {ρ : Measure ℝ} {fρ : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρ fρ D θ v) (hθ : 0 < θ) (hD : 0 < D)

theorem stripMap_neg_map_neg (ρ : Measure ℝ) : (ρ.map Neg.neg).map Neg.neg = ρ := by
  rw [Measure.map_map measurable_neg measurable_neg]
  have : (Neg.neg ∘ Neg.neg : ℝ → ℝ) = id := by funext x; simp
  rw [this, Measure.map_id]

include hW hθ hD in
theorem stripReflect_rootMinus {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) :
    cepsRootMinus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q = -cepsRootPlus D θ ρ μ q := by
  have hμ' : |(-μ)| ≤ dom.μ₀ := by simpa only [abs_neg] using hμ
  have h := dom.rootPlus_reflected_eq_neg_rootMinus hW.neg hθ hD hμ' hq0 hq
  rw [stripMap_neg_map_neg, neg_neg] at h
  rw [h, neg_neg]

include hW hθ hD in
/-- **Reflection dictionary** for the root-zone data. -/
theorem stripReflect_dictionary {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) {ζ : ℂ} (hζ : ‖ζ‖ ≤ dom.c₀ / 4) :
    cepsQ D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q (-ζ) = cepsQ D θ ρ μ q ζ ∧
      cexp (dom.canonL (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q (-ζ)) = cexp (dom.canonLMinus ρ μ q ζ) := by
  have hμ' : |(-μ)| ≤ dom.μ₀ := by simpa only [abs_neg] using hμ
  have hc0 := dom.c₀_pos
  have hre : |(-ζ).re| < dom.c₀ := by
    have := abs_re_le_norm (-ζ); rw [norm_neg] at this; linarith
  have hre' : |ζ.re| < dom.c₀ := by have := abs_re_le_norm ζ; linarith
  have hL' : cexp (dom.canonL (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q (-ζ)) =
      cexp (dom.canonLMinus ρ μ q ζ) := by
    have := dom.exp_canonL_reflected hW hθ hD hμ hq0 hq hre
    rwa [neg_neg] at this
  have hLm : cexp (dom.canonL ρ μ q ζ) =
      cexp (dom.canonLMinus (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q (-ζ)) := by
    have := dom.exp_canonL_reflected hW.neg hθ hD hμ' hq0 hq hre'
    rwa [stripMap_neg_map_neg, neg_neg] at this
  have hsum := CepsC6.cexp_canonL_add_canonLMinus dom hW hθ hD hμ hq (ζ := ζ) (by linarith)
  have hsum' := CepsC6.cexp_canonL_add_canonLMinus dom hW.neg hθ hD hμ' hq (ζ := -ζ)
    (by linarith)
  refine ⟨?_, hL'⟩
  rw [← hsum, ← hsum', Complex.exp_add, Complex.exp_add, hL', ← hLm, mul_comm]

theorem cexp_two_mul_sub (x y : ℂ) : cexp (2 * x - 2 * y) = cexp x ^ 2 / cexp y ^ 2 := by
  rw [Complex.exp_sub, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  norm_num

include hW hθ hD in
/-- **The reflected entrance at mark zero is the lower-end entrance.** -/
theorem stripReflect_entrance_eq_bottom {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) (l : ℂ) :
    (cepsWHNormalData D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q).entrance
        (dom.canonL (ρ.map Neg.neg)) ((-μ : ℝ) : ℂ) q 0 l =
      (cepsWHNormalData D θ ρ μ q).bottomEntrance (dom.canonL ρ) μ q l := by
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hc0 := dom.c₀_pos
  have hρA : dom.c₀ / 4 < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  set βp := cepsRootPlus D θ ρ μ q
  set βm := cepsRootMinus D θ ρ μ q
  have hbp : ‖βp‖ ≤ dom.c₀ / 4 := dom.norm_rootPlus_le hW hθ hD hμc hq
  have hbm : ‖βm‖ ≤ dom.c₀ / 4 := dom.norm_rootMinus_le hW hθ hD hμc hq
  have h0 : ‖(0 : ℂ)‖ ≤ dom.c₀ / 4 := by simp; positivity
  have hp' : cepsRootPlus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q = -βm :=
    dom.rootPlus_reflected_eq_neg_rootMinus hW hθ hD hμ hq0 hq
  have hm' : cepsRootMinus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q = -βp :=
    stripReflect_rootMinus dom hW hθ hD hμ hq0 hq
  obtain ⟨hQ0, hL0⟩ := stripReflect_dictionary dom hW hθ hD hμ hq0 hq h0
  obtain ⟨hQp, hLp⟩ := stripReflect_dictionary dom hW hθ hD hμ hq0 hq hbp
  obtain ⟨hQm, hLm⟩ := stripReflect_dictionary dom hW hθ hD hμ hq0 hq hbm
  rw [neg_zero] at hQ0 hL0
  have hQne : ∀ z : ℂ, ‖z‖ ≤ dom.c₀ / 4 → cepsQ D θ ρ μ q z ≠ 0 := fun z hz =>
    CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμc hq (mem_ball_zero_iff.mpr (by linarith))
  have hQ0n := hQne 0 h0
  have hQpn := hQne βp hbp
  have hQmn := hQne βm hbm
  -- the factor `e^{L₋}` in terms of `Q` and `e^{L}`
  have hEm : ∀ z : ℂ, cepsQ D θ ρ μ q z ≠ 0 →
      cexp (dom.canonLMinus ρ μ q z) = cepsQ D θ ρ μ q z / cexp (dom.canonL ρ μ q z) := by
    intro z hz
    rw [CepsC6.cexp_canonLMinus_eq dom hz, Complex.exp_neg, div_eq_mul_inv]
  have hd : cepsD (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q 0 = cepsD ρ μ q 0 := by
    rw [cepsD_zero_eq hW.neg, cepsD_zero_eq hW]
  -- the reflected `Π` and `N₀`
  have hpi : (cepsWHNormalData D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q).pi
      (dom.canonL (ρ.map Neg.neg)) ((-μ : ℝ) : ℂ) q =
      (cepsWHNormalData D θ ρ μ q).pi (dom.canonL ρ) μ q := by
    unfold CepsNormalData.pi
    show cepsQ D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q
          (cepsRootPlus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q) /
        cepsQ D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q
          (cepsRootMinus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q) *
        cexp (2 * dom.canonL (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q
            (cepsRootMinus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q) -
          2 * dom.canonL (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q
            (cepsRootPlus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q)) =
      cepsQ D θ ρ μ q βp / cepsQ D θ ρ μ q βm *
        cexp (2 * dom.canonL ρ μ q βm - 2 * dom.canonL ρ μ q βp)
    rw [hp', hm', hQm, hQp, cexp_two_mul_sub, cexp_two_mul_sub, hLp, hLm, hEm βp hQpn,
      hEm βm hQmn]
    have h1 := Complex.exp_ne_zero (dom.canonL ρ μ q βp)
    have h2 := Complex.exp_ne_zero (dom.canonL ρ μ q βm)
    field_simp
  have hN : (cepsWHNormalData D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q).markedN
      (dom.canonL (ρ.map Neg.neg)) ((-μ : ℝ) : ℂ) q 0 =
      (cepsWHNormalData D θ ρ μ q).reflectedN (dom.canonL ρ) μ q := by
    unfold CepsNormalData.markedN CepsNormalData.reflectedN
    show cepsQ D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q 0 /
        cepsQ D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q
          (cepsRootMinus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q) *
        cexp (2 * dom.canonL (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q
            (cepsRootMinus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q) -
          2 * dom.canonL (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q 0) =
      cepsQ D θ ρ μ q βp / cepsQ D θ ρ μ q 0 *
        cexp (2 * dom.canonL ρ μ q 0 - 2 * dom.canonL ρ μ q βp)
    rw [hm', hQ0, hQp, cexp_two_mul_sub, cexp_two_mul_sub, hLp, hL0, hEm βp hQpn, hEm 0 hQ0n]
    have h1 := Complex.exp_ne_zero (dom.canonL ρ μ q βp)
    have h2 := Complex.exp_ne_zero (dom.canonL ρ μ q 0)
    field_simp
  have hpre : cexp (dom.canonL (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q 0) =
      cexp ((cepsWHNormalData D θ ρ μ q).factorMinus (dom.canonL ρ) μ q 0) := hL0
  unfold CepsNormalData.entrance CepsNormalData.bottomEntrance CepsNormalData.entranceNumerator
    CepsNormalData.bottomNumerator CepsNormalData.delta CepsNormalData.decay
    CepsNormalData.eta
  rw [hpi, hN, hpre]
  change cexp _ / cepsD (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q 0 *
      ((cepsRootPlus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q - 0) -
        (cepsRootMinus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q - 0) *
          cexp (-(cepsRootPlus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q -
            cepsRootMinus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q) * l) * _ -
        (cepsRootPlus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q -
            cepsRootMinus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q) *
          cexp ((cepsRootMinus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q - 0) * l) * _) /
      (1 - cexp (-(cepsRootPlus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q -
            cepsRootMinus D θ (ρ.map Neg.neg) ((-μ : ℝ) : ℂ) q) * l) * _) =
    cexp _ / cepsD ρ μ q 0 * (-βm + βp * cexp (-(βp - βm) * l) * _ -
        (βp - βm) * cexp (-βp * l) * _) / (1 - cexp (-(βp - βm) * l) * _)
  rw [hp', hm', hd]
  have e1 : -βm - -βp = βp - βm := by ring
  rw [e1]
  ring_nf

end

end PGM
