import PLAStochastic.Index.CEPS.Total.DrawupBounds
import PLAStochastic.Index.CEPS.Reward.CanonicalReflection

/-!
# WP10: the bottom-started normal exits as the reflected top-started system

The bottom-started `Y_μ` strip is the top-started strip of the reflected step law `-W` at drift
`-μ` with mark `-t` (WP8 `cepsStripExit_reflect_*`). Its normal exits are the X5 top-started
exits `upperExit`, `lowerExit` of the reflected data. Under the reflection dictionary
`β₊' = -β₋`, `β₋' = -β₊`, `Q'(-ζ) = Q(ζ)`, `e^{L'(-ζ)} = e^{L₋(ζ)}` they are exactly the
bottom-started exits `botLowerExit`, `botUpperExit` of the original data
(`reflected_exits_eq`). The dictionary holds for the actual Morse data and canonical factor
(`reflected_normal_dictionary`, from the W-6 reflection identities).
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf

namespace PGM.CepsNormalData

/-- **Reflection of the normal exit system.** -/
theorem reflected_exits_eq (a a' : CepsNormalData) (L L' : ℂ → ℂ → ℂ → ℂ) (μ μ' q t l : ℂ)
    (h1 : a'.βp = -a.βm) (h2 : a'.βm = -a.βp)
    (hQ : ∀ ζ ∈ ({t, a.βp, a.βm} : Set ℂ), a'.Q (-ζ) = a.Q ζ)
    (hL : ∀ ζ ∈ ({t, a.βp, a.βm} : Set ℂ), exp (L' μ' q (-ζ)) = exp (a.factorMinus L μ q ζ))
    (hQne : ∀ ζ ∈ ({t, a.βp, a.βm} : Set ℂ), a.Q ζ ≠ 0) :
    a'.upperExit L' μ' q (-t) l = a.botLowerExit L μ q t l ∧
      a'.lowerExit L' μ' q (-t) l = a.botUpperExit L μ q t l := by
  have mt : t ∈ ({t, a.βp, a.βm} : Set ℂ) := by simp
  have mp : a.βp ∈ ({t, a.βp, a.βm} : Set ℂ) := by simp
  have mm : a.βm ∈ ({t, a.βp, a.βm} : Set ℂ) := by simp
  -- exponentials of the reflected factors
  have eL : ∀ ζ ∈ ({t, a.βp, a.βm} : Set ℂ), exp (L' μ' q (-ζ)) = a.Q ζ / exp (L μ q ζ) :=
    fun ζ hζ => by rw [hL ζ hζ, exp_factorMinus a L μ q (hQne ζ hζ)]
  have eF : ∀ ζ ∈ ({t, a.βp, a.βm} : Set ℂ),
      exp (a'.factorMinus L' μ' q (-ζ)) = exp (L μ q ζ) := fun ζ hζ => by
    have hQ' : a'.Q (-ζ) ≠ 0 := by rw [hQ ζ hζ]; exact hQne ζ hζ
    rw [exp_factorMinus a' L' μ' q hQ', eL ζ hζ, hQ ζ hζ]
    field_simp [hQne ζ hζ]
  have heta : a'.eta = a.eta := by rw [eta, eta, h1, h2]; ring
  have hdecay : a'.decay l = a.decay l := by rw [decay, decay, heta]
  have hQp' : a'.Q a'.βp = a.Q a.βm := by rw [h1]; exact hQ _ mm
  have hQm' : a'.Q a'.βm = a.Q a.βp := by rw [h2]; exact hQ _ mp
  have hLp' : exp (L' μ' q a'.βp) = a.Q a.βm / exp (L μ q a.βm) := by rw [h1]; exact eL _ mm
  have hLm' : exp (L' μ' q a'.βm) = a.Q a.βp / exp (L μ q a.βp) := by rw [h2]; exact eL _ mp
  have hFp' : exp (a'.factorMinus L' μ' q a'.βp) = exp (L μ q a.βm) := by rw [h1]; exact eF _ mm
  have hFm' : exp (a'.factorMinus L' μ' q a'.βm) = exp (L μ q a.βp) := by rw [h2]; exact eF _ mp
  have hQpn := hQne _ mp
  have hQmn := hQne _ mm
  have hpi : a'.pi L' μ' q = a.pi L μ q := by
    unfold pi
    have e2 : ∀ x y : ℂ, exp (2 * x - 2 * y) = exp x ^ 2 / exp y ^ 2 := fun x y => by
      rw [exp_sub, ← exp_nat_mul, ← exp_nat_mul]; norm_num
    rw [e2, e2, hQp', hQm', hLp', hLm']
    field_simp
  have hdelta : a'.delta L' μ' q l = a.delta L μ q l := by
    rw [delta, delta, hdecay, hpi]
  have hBp' : a'.overshootPlus L' μ' q (a'.βp - -t) = a.overshootMinus L μ q (t - a.βm) := by
    rw [overshootPlus, overshootMinus, show a'.βp - (a'.βp - -t) = -t by ring,
      show a.βm + (t - a.βm) = t by ring, exp_sub, exp_sub, eL _ mt, hLp', exp_factorMinus a L μ q
      (hQne _ mt), exp_factorMinus a L μ q hQmn]
  have hBm' : a'.overshootMinus L' μ' q a'.eta = a.overshootPlus L μ q a.eta := by
    rw [overshootMinus, overshootPlus, show a'.βm + a'.eta = a'.βp by rw [eta]; ring,
      show a.βp - a.eta = a.βm by rw [eta]; ring, exp_sub, exp_sub, hFp', hFm']
  have hBmt' : a'.overshootMinus L' μ' q (-t - a'.βm) = a.overshootPlus L μ q (a.βp - t) := by
    rw [overshootMinus, overshootPlus, show a'.βm + (-t - a'.βm) = -t by ring,
      show a.βp - (a.βp - t) = t by ring, exp_sub, exp_sub, eF _ mt, hFm']
  have hX : a'.passageX L' μ' q l = a.ladderGap L μ q a.βp / a.delta L μ q l := by
    rw [passageX, heta, hLm', hdelta, ladderGap, exp_factorMinus a L μ q hQpn, eta]
  constructor
  · rw [upperExit, passageY, hBp', hBm', hdecay, hX, botLowerExit,
      show a'.βp - -t = t - a.βm by rw [h1]; ring, eL _ mt, ladderGap_eq a L μ q (hQne _ mt)]
    ring
  · rw [lowerExit, hBmt', hX, botUpperExit, show a'.βm - -t = -(a.βp - t) by rw [h2]; ring]
    ring

end PGM.CepsNormalData

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

theorem map_neg_map_neg (ρ : Measure ℝ) : (ρ.map Neg.neg).map Neg.neg = ρ := by
  rw [Measure.map_map measurable_neg measurable_neg]
  have : (Neg.neg ∘ Neg.neg : ℝ → ℝ) = id := by funext x; simp
  rw [this, Measure.map_id]

include hW hθ hD in
/-- The reflected lower root. -/
theorem rootMinus_reflected_eq_neg_rootPlus {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) :
    cepsRootMinus D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q = -cepsRootPlus D θ ρW μ q := by
  have hμ' : |(-μ)| ≤ dom.μ₀ := by simpa only [abs_neg] using hμ
  have h := dom.rootPlus_reflected_eq_neg_rootMinus hW.neg hθ hD hμ' hq0 hq
  rw [map_neg_map_neg, neg_neg] at h
  rw [h, neg_neg]

include hW hθ hD in
/-- **Reflection dictionary** for the actual Morse data and canonical factor. -/
theorem reflected_normal_dictionary {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) {ζ : ℂ} (hζ : ‖ζ‖ ≤ dom.c₀ / 4) :
    (cepsNormalData D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q).Q (-ζ) =
        (cepsNormalData D θ ρW μ q).Q ζ ∧
      exp (dom.canonL (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q (-ζ)) =
        exp ((cepsNormalData D θ ρW μ q).factorMinus (dom.canonL ρW) μ q ζ) := by
  have hμ' : |(-μ)| ≤ dom.μ₀ := by simpa only [abs_neg] using hμ
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ
  have hμc' : ‖((-μ : ℝ) : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ'
  have hc0 := dom.c₀_pos
  have hρA : dom.c₀ / 4 < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hζA : ζ ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by linarith)
  have hζA' : -ζ ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by rw [norm_neg]; linarith)
  have hre : |(-ζ).re| < dom.c₀ := by
    have := abs_re_le_norm (-ζ); rw [norm_neg] at this; linarith
  have hre' : |ζ.re| < dom.c₀ := by have := abs_re_le_norm ζ; linarith
  have hre2 : |ζ.re| ≤ 2 * dom.c₀ := by linarith
  have hre2' : |(-ζ).re| ≤ 2 * dom.c₀ := by linarith
  -- `e^{L'(-ζ)} = e^{L₋(ζ)}`
  have hL' : exp (dom.canonL (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q (-ζ)) =
      exp (dom.canonLMinus ρW μ q ζ) := by
    have := dom.exp_canonL_reflected hW hθ hD hμ hq0 hq hre
    rwa [neg_neg] at this
  -- `e^{L(ζ)} = e^{L'₋(-ζ)}`
  have hLm : exp (dom.canonL ρW μ q ζ) =
      exp (dom.canonLMinus (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q (-ζ)) := by
    have := dom.exp_canonL_reflected hW.neg hθ hD hμ' hq0 hq hre'
    rwa [map_neg_map_neg, neg_neg] at this
  have hQ : cepsQ D θ ρW μ q ζ = cepsQuotA D θ ρW μ q ζ :=
    CepsC6.cepsQ_eq_cepsQuotA dom hW hθ hD hμc hq hζA
  have hQ' : cepsQ D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q (-ζ) =
      cepsQuotA D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q (-ζ) :=
    CepsC6.cepsQ_eq_cepsQuotA dom hW.neg hθ hD hμc' hq hζA'
  have hsum := CepsC6.cexp_canonL_add_canonLMinus dom hW hθ hD hμ hq hre2
  have hsum' := CepsC6.cexp_canonL_add_canonLMinus dom hW.neg hθ hD hμ' hq hre2'
  have hQne : cepsQ D θ ρW μ q ζ ≠ 0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμc hq hζA
  constructor
  · show cepsQuotA D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q (-ζ) = cepsQuotA D θ ρW μ q ζ
    rw [← hQ, ← hQ', ← hsum', ← hsum, exp_add, exp_add, hL', ← hLm, mul_comm]
  · rw [hL', CepsC6.cexp_canonLMinus_eq dom hQne, CepsNormalData.exp_factorMinus _ _ _ _
      (show (cepsNormalData D θ ρW μ q).Q ζ ≠ 0 by
        show cepsQuotA D θ ρW μ q ζ ≠ 0; rw [← hQ]; exact hQne)]
    show cepsQ D θ ρW μ q ζ * cexp (-dom.canonL ρW μ q ζ) =
      cepsQuotA D θ ρW μ q ζ / cexp (dom.canonL ρW μ q ζ)
    rw [hQ, exp_neg, div_eq_mul_inv]

include hW hθ hD in
/-- The reflected top-started exits are the bottom-started exits of the original data. -/
theorem reflected_exits_actual {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) {t : ℂ} (ht : ‖t‖ ≤ dom.c₀ / 4) (l : ℂ) :
    (cepsNormalData D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q).upperExit
        (dom.canonL (ρW.map Neg.neg)) ((-μ : ℝ) : ℂ) q (-t) l =
      (cepsNormalData D θ ρW μ q).botLowerExit (dom.canonL ρW) μ q t l ∧
    (cepsNormalData D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q).lowerExit
        (dom.canonL (ρW.map Neg.neg)) ((-μ : ℝ) : ℂ) q (-t) l =
      (cepsNormalData D θ ρW μ q).botUpperExit (dom.canonL ρW) μ q t l := by
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ
  have hbp := dom.norm_rootPlus_le hW hθ hD hμc hq
  have hbm := dom.norm_rootMinus_le hW hθ hD hμc hq
  have hpts : ∀ ζ ∈ ({t, (cepsNormalData D θ ρW μ q).βp, (cepsNormalData D θ ρW μ q).βm} :
      Set ℂ), ‖ζ‖ ≤ dom.c₀ / 4 := by
    intro ζ hζ
    rcases hζ with h | h | h
    · rw [h]; exact ht
    · rw [Set.mem_singleton_iff.mp h] at *; exact hbp
    · rw [Set.mem_singleton_iff.mp h]; exact hbm
  have hc0 := dom.c₀_pos
  have hρA : dom.c₀ / 4 < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  refine CepsNormalData.reflected_exits_eq _ _ _ _ _ _ q t l ?_ ?_ ?_ ?_ ?_
  · exact dom.rootPlus_reflected_eq_neg_rootMinus hW hθ hD hμ hq0 hq
  · exact rootMinus_reflected_eq_neg_rootPlus dom hW hθ hD hμ hq0 hq
  · exact fun ζ hζ => (reflected_normal_dictionary dom hW hθ hD hμ hq0 hq (hpts ζ hζ)).1
  · exact fun ζ hζ => (reflected_normal_dictionary dom hW hθ hD hμ hq0 hq (hpts ζ hζ)).2
  · intro ζ hζ
    exact dom.cepsQuotA_ne_zero hW hθ hD hμc hq (by have := hpts ζ hζ; linarith)

end PGM
