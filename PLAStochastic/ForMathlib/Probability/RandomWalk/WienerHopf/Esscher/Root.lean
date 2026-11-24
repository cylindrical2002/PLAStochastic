import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Esscher.Moments
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Esscher.Class

/-!
# Esscher identities at a positive real discounted root

A strictly positive real discount and a nonnegative root force the tilted
ascending ladder to have total mass one. Differentiating Wiener--Hopf then
gives the tilted mean times the descending defect.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {β q : ℝ}

omit [IsProbabilityMeasure ρ] in
theorem stepTransform_root (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q) :
    stepTransform ρ (β : ℂ) = cexp (q : ℂ) := by
  simpa only [stepTransform, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
    integral_complex_ofReal] using congrArg (fun r : ℝ => (r : ℂ)) hroot

/-- The tilted ascending ladder is nondefective at a positive discounted root. -/
theorem ascTransform_esscher_root_eq_one
    (hβi : Integrable (fun y => Real.exp (β * y)) ρ) (hβ : 0 ≤ β) (hq : 0 < q)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q) :
    ascTransform (esscherLaw ρ β) 1 0 = 1 := by
  have hsumA := summable_entry_esscher hβi hroot (A := Ioi 0) measurableSet_Ioi (z := 0) (by simp)
  have hsumD := summable_entry_esscher hβi hroot (A := Iic 0) measurableSet_Iic (z := 0) (by simp)
  simp only [add_zero] at hsumA hsumD
  have hw := wienerHopf_of_summable (ρ := ρ) measurableSet_Iic isLadderSet_Iic
    (s := cexp (-q)) (z := (β : ℂ))
    (integrable_cexp_iff_exp_re.mpr (by simpa using hβi))
    (by simpa only [compl_Iic] using hsumA) hsumD
  rw [compl_Iic] at hw
  have hfac : (1 - ascTransform ρ (cexp (-q)) (β : ℂ)) *
      (1 - descTransform ρ (cexp (-q)) (β : ℂ)) = 0 := by
    rw [← hw, stepTransform_root hroot, ← Complex.exp_add]
    simp
  have hlt := norm_descTransform_exp_lt_one (ρ := ρ) (q := (q : ℂ)) (ζ := (β : ℂ))
    (by simpa using hq) (by simpa using hβ)
  have hnD : 1 - descTransform ρ (cexp (-q)) (β : ℂ) ≠ 0 := by
    intro he
    rw [← sub_eq_zero.mp he, norm_one] at hlt
    exact (lt_irrefl 1) hlt
  have hA := (sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hnD)).symm
  have ht := entryTransform_esscher hβi hroot (A := Ioi 0) measurableSet_Ioi (z := 0) (by simp)
  simp only [add_zero] at ht
  exact ht.trans hA

omit [IsProbabilityMeasure ρ] in
theorem esscherLaw_positive_mass (hβi : Integrable (fun y => Real.exp (β * y)) ρ)
    {E : Set ℝ} (hE : 0 < ρ E) : 0 < esscherLaw ρ β E := by
  by_contra hn
  have he : esscherLaw ρ β E = 0 := le_antisymm (not_lt.mp hn) bot_le
  have he' := absolutelyContinuous_tilted hβi he
  rw [he'] at hE
  exact (lt_irrefl 0) hE

omit [IsProbabilityMeasure ρ] in
/-- Step exponential moments of the tilted law, paid by the original strip. -/
theorem integrable_exp_esscher_of_shift
    (hβi : Integrable (fun y => Real.exp (β * y)) ρ) {t : ℝ}
    (ht : Integrable (fun y => Real.exp ((β + t) * y)) ρ) :
    Integrable (fun y => Real.exp (t * y)) (esscherLaw ρ β) := by
  apply (integrable_tilted_iff hβi _).mpr
  simpa only [smul_eq_mul, ← Real.exp_add, ← add_mul] using ht

/-- `m₊ (1 - p₋) = ψ'(β)` at the nonnegative real root of `E exp (β Y) = exp q`.
Here `ψ` is the real cumulant generating function of the original step law. -/
theorem esscher_entryMean_mul_one_sub_descMass {a : ℝ} (ha : 0 < a)
    (hpos : Integrable (fun y => Real.exp (a * y)) ρ)
    (hneg : Integrable (fun y => Real.exp (-a * y)) ρ)
    (hl : 0 < ρ (Iio 0)) (hr : 0 < ρ (Ioi 0))
    (hβ : 0 ≤ β) (hβa : β < a) (hq : 0 < q)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q) :
    entryMean (esscherLaw ρ β) (Ioi 0) *
      (1 - expEntryMass (esscherLaw ρ β) (Iic 0) 0) = deriv (cgf id ρ) β := by
  have hβi := integrable_exp_mul_of_le_of_le hneg hpos
    (show -a ≤ β by linarith) hβa.le
  have := isProbabilityMeasure_esscherLaw hβi
  have ht : 0 < (a - β) / 2 := by linarith
  have hp := integrable_exp_esscher_of_shift hβi
    (integrable_exp_mul_of_le_of_le hneg hpos
      (show -a ≤ β + (a - β) / 2 by linarith)
      (show β + (a - β) / 2 ≤ a by linarith))
  have hm := integrable_exp_esscher_of_shift hβi
    (integrable_exp_mul_of_le_of_le hneg hpos
      (show -a ≤ β + -((a - β) / 2) by linarith)
      (show β + -((a - β) / 2) ≤ a by linarith))
  have he := entryMean_mul_one_sub_descMass ht hp hm
    (esscherLaw_positive_mass hβi hl) (esscherLaw_positive_mass hβi hr)
    (ascTransform_esscher_root_eq_one hβi hβ hq hroot)
  have hi : β ∈ interior (integrableExpSet id ρ) :=
    interior_maximal (fun t ht => integrable_exp_mul_of_le_of_le hneg hpos
      ht.1.le ht.2.le) isOpen_Ioo ⟨by linarith, hβa⟩
  exact he.trans (esscherLaw_mean hi)

end PGM.WienerHopf
