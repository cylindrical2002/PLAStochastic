import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Esscher.Path

/-!
# Esscher identities for first-entry and ladder transforms

The first-entry identity holds on the half-plane where the tilted transform
is bounded on the entry set. In particular it applies to `β - s` for the
ascending ladder when `Re s ≥ 0`, and to `β + s` for the descending ladder.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Finset

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {β q : ℝ} {A : Set ℝ}

theorem esscher_weight_cexp (β q : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    Real.exp (β * x - q * n) • cexp (z * x) =
      cexp (-q) ^ n * cexp (((β : ℂ) + z) * x) := by
  rw [Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_nat_mul,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem esscher_weight_indicator (β q : ℝ) (z : ℂ) (n : ℕ)
    (E : Set (ℕ → ℝ)) (ω : ℕ → ℝ) :
    Real.exp (β * partialSum n ω - q * n) •
        E.indicator (fun ω => cexp (z * partialSum n ω)) ω =
      cexp (-q) ^ n * E.indicator
        (fun ω => cexp (((β : ℂ) + z) * partialSum n ω)) ω := by
  by_cases hω : ω ∈ E
  · simp only [indicator_of_mem hω]
    exact esscher_weight_cexp β q z n _
  · simp only [indicator_of_notMem hω, smul_zero, mul_zero]

theorem dependsOnPrefix_entryIndicator (A : Set ℝ) (z : ℂ) (n : ℕ) :
    DependsOnPrefix n ({ω | firstEntry A ω = n}.indicator
      (fun ω => cexp (z * partialSum n ω))) :=
  DependsOnPrefix.indicator (dependsOnPrefix_firstEntry_eq A n)
    (fun _ _ he => by rw [partialSum_congr he])

/-- The coefficient identity is valid at every complex spatial argument. -/
theorem entryCoeff_esscher (hβ : Integrable (fun y => Real.exp (β * y)) ρ)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q)
    (hA : MeasurableSet A) (z : ℂ) (n : ℕ) :
    entryCoeff (esscherLaw ρ β) A z n =
      cexp (-q) ^ n * entryCoeff ρ A ((β : ℂ) + z) n := by
  rw [entryCoeff, ← integral_indicator (measurableSet_firstEntry_eq hA n),
    integral_esscher_prefix hβ hroot
      ((by fun_prop : Measurable fun ω => cexp (z * partialSum n ω)).indicator
        (measurableSet_firstEntry_eq hA n)) (dependsOnPrefix_entryIndicator A z n)]
  simp_rw [esscher_weight_indicator]
  rw [integral_const_mul, integral_indicator (measurableSet_firstEntry_eq hA n)]
  rfl

theorem integrableOn_entry_esscher (hβ : Integrable (fun y => Real.exp (β * y)) ρ)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q)
    (hA : MeasurableSet A) {z : ℂ} (hz : ∀ x ∈ A, z.re * x ≤ 0) (n : ℕ) :
    IntegrableOn (fun ω => cexp (((β : ℂ) + z) * partialSum n ω))
      {ω | firstEntry A ω = n} (pathLaw ρ) := by
  have := isProbabilityMeasure_esscherLaw hβ
  have hu := integrableOn_entry_of_bounded (ρ := esscherLaw ρ β) hA hz n
  rw [← integrable_indicator_iff (measurableSet_firstEntry_eq hA n)] at hu ⊢
  have hv := (integrable_esscher_prefix_iff hβ hroot
    ((by fun_prop : Measurable fun ω => cexp (z * partialSum n ω)).indicator
      (measurableSet_firstEntry_eq hA n)) (dependsOnPrefix_entryIndicator A z n)).mp hu
  simp_rw [esscher_weight_indicator] at hv
  exact (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (pow_ne_zero _ (Complex.exp_ne_zero _))) _).mp hv

/-- The same coefficient change of measure controls the absolute series. -/
theorem entryNormCoeff_esscher (hβ : Integrable (fun y => Real.exp (β * y)) ρ)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q)
    (hA : MeasurableSet A) (z : ℂ) (n : ℕ) :
    (∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖
      ∂pathLaw (esscherLaw ρ β)) =
      ‖cexp (-q)‖ ^ n * ∫ ω in {ω | firstEntry A ω = n},
        ‖cexp (((β : ℂ) + z) * partialSum n ω)‖ ∂pathLaw ρ := by
  have he := entryCoeff_esscher hβ hroot hA (z.re : ℂ) n
  have he' :
      ((∫ ω in {ω | firstEntry A ω = n}, Real.exp (z.re * partialSum n ω)
        ∂pathLaw (esscherLaw ρ β) : ℝ) : ℂ) =
      ((Real.exp (-q) ^ n * ∫ ω in {ω | firstEntry A ω = n},
        Real.exp ((β + z.re) * partialSum n ω) ∂pathLaw ρ : ℝ) : ℂ) := by
    push_cast
    rw [ofReal_setIntegral_exp, ofReal_setIntegral_exp]
    simpa only [entryCoeff, Complex.ofReal_add, Complex.ofReal_neg] using he
  simp only [norm_cexp_mul_ofReal]
  simpa only [Complex.norm_exp, Complex.neg_re,
    Complex.ofReal_re, Complex.add_re] using Complex.ofReal_injective he'

theorem summable_entry_esscher (hβ : Integrable (fun y => Real.exp (β * y)) ρ)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q)
    (hA : MeasurableSet A) {z : ℂ} (hz : ∀ x ∈ A, z.re * x ≤ 0) :
    Summable fun n : ℕ => ‖cexp (-q)‖ ^ n *
      ∫ ω in {ω | firstEntry A ω = n},
        ‖cexp (((β : ℂ) + z) * partialSum n ω)‖ ∂pathLaw ρ := by
  have := isProbabilityMeasure_esscherLaw hβ
  have ht := summable_entry_of_bounded (ρ := esscherLaw ρ β) hA
    (s := 1) (by simp) hz
  simp only [norm_one, one_pow, one_mul] at ht
  exact ht.congr fun n => entryNormCoeff_esscher hβ hroot hA z n

/-- First-entry Esscher identity, including convergence and integrability. -/
theorem entryTransform_esscher (hβ : Integrable (fun y => Real.exp (β * y)) ρ)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q)
    (hA : MeasurableSet A) {z : ℂ} (hz : ∀ x ∈ A, z.re * x ≤ 0) :
    entryTransform (esscherLaw ρ β) A 1 z =
      entryTransform ρ A (cexp (-q)) ((β : ℂ) + z) := by
  have := isProbabilityMeasure_esscherLaw hβ
  rw [entryTransform_eq_tsum_of_bounded hA (by simp) hz,
    entryTransform_eq_tsum hA (integrableOn_entry_esscher hβ hroot hA hz)
      (summable_entry_esscher hβ hroot hA hz)]
  apply tsum_congr
  intro n
  simpa only [one_pow, one_mul] using entryCoeff_esscher hβ hroot hA z n

/-- `E_β[exp (-s H₊); σ₊ < ∞] = A₊(β - s)` for `Re s ≥ 0`. -/
theorem ascTransform_esscher (hβ : Integrable (fun y => Real.exp (β * y)) ρ)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ascTransform (esscherLaw ρ β) 1 (-s) =
      ascTransform ρ (cexp (-q)) ((β : ℂ) - s) := by
  exact entryTransform_esscher hβ hroot measurableSet_Ioi (fun x hx => by
    simp only [Complex.neg_re]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hx.le)

/-- `E_β[exp (-s H₋); σ₋ < ∞] = A₋(β + s)` for `Re s ≥ 0`.
The descending entry position is `-H₋`. -/
theorem descTransform_esscher (hβ : Integrable (fun y => Real.exp (β * y)) ρ)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q)
    {s : ℂ} (hs : 0 ≤ s.re) :
    descTransform (esscherLaw ρ β) 1 s =
      descTransform ρ (cexp (-q)) ((β : ℂ) + s) :=
  entryTransform_esscher hβ hroot measurableSet_Iic (fun _ hx =>
    mul_nonpos_of_nonneg_of_nonpos hs hx)

end PGM.WienerHopf
