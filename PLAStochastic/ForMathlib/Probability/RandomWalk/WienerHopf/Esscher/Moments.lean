import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Esscher.Ladder

/-!
# Differentiating Wiener--Hopf at a nondefective ascending ladder

Ladder exponential moments justify differentiation of the actual first-entry
integral. The identity is first proved for an arbitrary probability step law;
the Esscher root specialization is provided in `Root`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Filter Topology

namespace PGM.WienerHopf

/-- The mean first-entry position, with the finite-entry indicator. -/
def entryMean (ρ : Measure ℝ) (A : Set ℝ) : ℝ :=
  ∫ ω in {ω | firstEntry A ω < ⊤}, entryValue A ω ∂pathLaw ρ

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ]

theorem integrableOn_exp_entry_of_nonpos {A : Set ℝ} (hA : MeasurableSet A)
    {t : ℝ} (ht : ∀ x ∈ A, t * x ≤ 0) :
    IntegrableOn (fun ω => Real.exp (t * entryValue A ω))
      {ω | firstEntry A ω < ⊤} (pathLaw ρ) := by
  refine Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _)
    ((Real.measurable_exp.comp ((measurable_entryValue hA).const_mul t)).aestronglyMeasurable)
    ((ae_restrict_iff' (measurableSet_firstEntry_lt_top hA)).mpr
      (Filter.Eventually.of_forall fun ω hω => ?_))
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
  exact ht _ (entryValue_mem hω)

omit [IsProbabilityMeasure ρ] in
theorem entryValue_mem_interior_integrableExpSet {A : Set ℝ} {a : ℝ} (ha : 0 < a)
    (hpos : IntegrableOn (fun ω => Real.exp (a * entryValue A ω))
      {ω | firstEntry A ω < ⊤} (pathLaw ρ))
    (hneg : IntegrableOn (fun ω => Real.exp (-a * entryValue A ω))
      {ω | firstEntry A ω < ⊤} (pathLaw ρ)) :
    0 ∈ interior (integrableExpSet (entryValue A)
      ((pathLaw ρ).restrict {ω | firstEntry A ω < ⊤})) := by
  exact interior_maximal (fun t ht => integrable_exp_mul_of_le_of_le hneg hpos
    ht.1.le ht.2.le) isOpen_Ioo ⟨by linarith, ha⟩

omit [IsProbabilityMeasure ρ] in
theorem hasDerivAt_entryTransform_one {A : Set ℝ}
    (h : 0 ∈ interior (integrableExpSet (entryValue A)
      ((pathLaw ρ).restrict {ω | firstEntry A ω < ⊤}))) :
    HasDerivAt (fun z => entryTransform ρ A 1 z) (entryMean ρ A : ℂ) 0 := by
  have he := hasDerivAt_complexMGF (X := entryValue A)
    (μ := (pathLaw ρ).restrict {ω | firstEntry A ω < ⊤}) (z := 0) (by simpa using h)
  change HasDerivAt (fun z => ∫ ω in {ω | firstEntry A ω < ⊤},
    cexp (z * entryValue A ω) ∂pathLaw ρ)
    (∫ ω in {ω | firstEntry A ω < ⊤},
      (entryValue A ω : ℂ) * cexp (0 * entryValue A ω) ∂pathLaw ρ) 0 at he
  simpa only [entryTransform, entryMean, one_pow, one_mul,
    zero_mul, Complex.exp_zero, mul_one, integral_complex_ofReal] using he

/-- Finite ascending ladder mean, justified directly by an exponential moment. -/
theorem integrableOn_entryValue_asc {a : ℝ} (ha : 0 < a)
    (hpos : Integrable (fun y => Real.exp (a * y)) ρ) (hl : 0 < ρ (Iio 0)) :
    IntegrableOn (entryValue (Ioi 0)) {ω | firstEntry (Ioi 0) ω < ⊤} (pathLaw ρ) := by
  have he := (expEntryMass_compl_le (ρ := ρ) measurableSet_Iic isLadderSet_Iic
    (fun _ hx => mul_nonpos_of_nonneg_of_nonpos ha.le hx)
    (expEntryMass_Iic_lt_one ha hl) hpos).2.1
  rw [compl_Iic] at he
  have hi := entryValue_mem_interior_integrableExpSet ha he
    (integrableOn_exp_entry_of_nonpos measurableSet_Ioi
      (fun _ hx => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) hx.le))
  simpa only [IntegrableOn, pow_one, zero_mul, Real.exp_zero, mul_one] using
    integrable_pow_mul_exp_of_mem_interior_integrableExpSet hi 1

/-- Differentiated Wiener--Hopf identity for an ascending ladder of total mass one. -/
theorem entryMean_mul_one_sub_descMass {a : ℝ} (ha : 0 < a)
    (hpos : Integrable (fun y => Real.exp (a * y)) ρ)
    (hneg : Integrable (fun y => Real.exp (-a * y)) ρ)
    (hl : 0 < ρ (Iio 0)) (hr : 0 < ρ (Ioi 0))
    (hasc : ascTransform ρ 1 0 = 1) :
    entryMean ρ (Ioi 0) * (1 - expEntryMass ρ (Iic 0) 0) = ∫ y, y ∂ρ := by
  have hgapD := expEntryMass_Iic_lt_one ha hl
  have hgapA := expEntryMass_Ioi_lt_one ha hr
  have heA := (expEntryMass_compl_le (ρ := ρ) measurableSet_Iic isLadderSet_Iic
    (fun _ hx => mul_nonpos_of_nonneg_of_nonpos ha.le hx) hgapD hpos).2.1
  rw [compl_Iic] at heA
  have heD := (expEntryMass_compl_le (ρ := ρ) measurableSet_Ioi isLadderSet_Ioi
    (fun _ hx => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) hx.le) hgapA hneg).2.1
  rw [compl_Ioi] at heD
  have hAi := entryValue_mem_interior_integrableExpSet ha heA
    (integrableOn_exp_entry_of_nonpos measurableSet_Ioi
      (fun _ hx => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) hx.le))
  have hDi := entryValue_mem_interior_integrableExpSet ha
    (integrableOn_exp_entry_of_nonpos measurableSet_Iic
      (fun _ hx => mul_nonpos_of_nonneg_of_nonpos ha.le hx)) heD
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id ρ) := by
    exact interior_maximal (fun t ht => integrable_exp_mul_of_le_of_le hneg hpos
      ht.1.le ht.2.le) isOpen_Ioo ⟨by linarith, ha⟩
  have hstep : HasDerivAt (stepTransform ρ) ((∫ y, y ∂ρ : ℝ) : ℂ) 0 := by
    have he := hasDerivAt_complexMGF (X := id) (μ := ρ) (z := 0) (by simpa using h0)
    change HasDerivAt (stepTransform ρ) (∫ y, (y : ℂ) * cexp (0 * y) ∂ρ) 0 at he
    simp only [zero_mul, Complex.exp_zero, mul_one] at he
    rw [integral_complex_ofReal (f := fun y : ℝ => y)] at he
    exact he
  have hleft := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub hstep
  have hright := ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub
    (hasDerivAt_entryTransform_one hAi)).mul
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hasDerivAt_entryTransform_one hDi))
  have heq : (fun z => 1 - stepTransform ρ z) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => (1 - ascTransform ρ 1 z) * (1 - descTransform ρ 1 z)) := by
    have hb : ∀ᶠ z : ℂ in 𝓝 0, |z.re| < a :=
      (isOpen_lt (Complex.continuous_re.abs) continuous_const).eventually_mem (by simpa)
    filter_upwards [hb] with z hz
    simpa only [one_mul] using wienerHopf_strip_of_pos ha hpos hneg hl hr
      (s := 1) (by simp) hz.le
  have he := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  have hd : descTransform ρ 1 0 = (expEntryMass ρ (Iic 0) 0 : ℂ) :=
    (ofReal_expEntryMass (Iic 0) 0).symm
  simp only [Pi.sub_apply] at he
  change entryTransform ρ (Ioi 0) 1 0 = 1 at hasc
  change entryTransform ρ (Iic 0) 1 0 = (expEntryMass ρ (Iic 0) 0 : ℂ) at hd
  rw [hasc, hd] at he
  apply Complex.ofReal_injective
  push_cast
  linear_combination he

end PGM.WienerHopf
