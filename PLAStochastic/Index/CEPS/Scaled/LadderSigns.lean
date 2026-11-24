import PLAStochastic.Index.CEPS.Ident.Main

/-! # Signs of the actual roots from their ladder identities

A root cannot lie in the strictly contracting spatial half-plane of its
actual ladder transform. This pays both signs on the closed discount
half-plane, without an additional drift sign assumption.
-/

noncomputable section
open MeasureTheory Set Complex Filter
open PGM.WienerHopf
namespace PGM.WienerHopf

theorem norm_entryTransform_le_expEntryMass {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {A : Set ℝ} (hA : MeasurableSet A) {s z : ℂ} (hs : ‖s‖ ≤ 1)
    (hz : ∀ y ∈ A, z.re * y ≤ 0) :
    ‖entryTransform ρ A s z‖ ≤ expEntryMass ρ A z.re := by
  have hm : Measurable (fun ω => Real.exp (z.re * entryValue A ω)) :=
    (measurable_const.mul (measurable_entryValue hA)).exp
  have hi : IntegrableOn (fun ω => Real.exp (z.re * entryValue A ω))
      {ω | firstEntry A ω < ⊤} (pathLaw ρ) := by
    refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' (measurableSet_firstEntry_lt_top hA)).mpr
      (Eventually.of_forall fun ω hω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    exact hz _ (entryValue_mem hω)
  rw [entryTransform, expEntryMass]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hi
  refine (ae_restrict_iff' (measurableSet_firstEntry_lt_top hA)).mpr
    (Eventually.of_forall fun ω _ => ?_)
  dsimp only
  rw [norm_mul, norm_pow, norm_cexp_mul_ofReal]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (pow_le_one₀ (norm_nonneg _) hs)

end PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
/-- Both actual spatial root signs, including zero discount. -/
theorem cepsRoots_re_signs {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) :
    0 ≤ (cepsRootPlus D θ ρW μ q).re ∧ (cepsRootMinus D θ ρW μ q).re ≤ 0 := by
  have := hW.isProbabilityMeasure
  have hI := dom.cepsWHIdent hW hθ hD
  have hs := norm_cexp_neg_le_one hq0
  have hmass := dom.driftStep_strip hW hθ hD hμ
  constructor
  · by_contra hp
    have hp0 : (cepsRootPlus D θ ρW μ q).re < 0 := lt_of_not_ge hp
    have hb := norm_entryTransform_le_expEntryMass (ρ := driftStep ρW μ) measurableSet_Ioi hs
      (z := cepsRootPlus D θ ρW μ q)
      (fun y hy => mul_nonpos_of_nonpos_of_nonneg hp0.le hy.le)
    change ‖ascTransform (driftStep ρW μ) (cexp (-q)) (cepsRootPlus D θ ρW μ q)‖ ≤ _ at hb
    rw [dom.ascTransform_rootPlus hW hθ hD hI hμ hq0 hq, norm_one] at hb
    have hg := expEntryMass_Ioi_lt_one (ρ := driftStep ρW μ) (neg_pos.mpr hp0) hmass.2.2.2
    rw [neg_neg] at hg
    linarith
  · by_contra hm
    have hm0 : 0 < (cepsRootMinus D θ ρW μ q).re := lt_of_not_ge hm
    have hb := norm_entryTransform_le_expEntryMass (ρ := driftStep ρW μ) measurableSet_Iic hs
      (z := cepsRootMinus D θ ρW μ q)
      (fun y hy => mul_nonpos_of_nonneg_of_nonpos hm0.le hy)
    change ‖descTransform (driftStep ρW μ) (cexp (-q)) (cepsRootMinus D θ ρW μ q)‖ ≤ _ at hb
    rw [dom.descTransform_rootMinus hW hθ hD hI hμ hq0 hq, norm_one] at hb
    have hg := expEntryMass_Iic_lt_one (ρ := driftStep ρW μ) hm0 hmass.2.2.1
    linarith

end PGM
