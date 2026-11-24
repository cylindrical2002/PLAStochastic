import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Factors of finite product measures

For a finite family of σ-finite measures `μ i` on `Fin n`-indexed coordinates:

* `lintegral_fin_pi_prod`: Tonelli for a product of one-coordinate functions,
  `∫⁻ ∏ g i (x i) ∂(pi μ) = ∏ ∫⁻ g i ∂(μ i)`, without any probability assumption.
* `lmarginal_eq_const_mul_of_indep`: integrating out coordinates on which a function does
  not depend multiplies it by the masses of those factors.
* `lintegral_pi_mul_eq_of_indep`: if `f` does not depend on the coordinates in `H` and two
  families agree off `H`, then `(∏_{i ∈ H} μ' i univ) ∫⁻ f ∂(pi μ) =
  (∏_{i ∈ H} μ i univ) ∫⁻ f ∂(pi μ')`. With `μ'` a family of probability measures on `H`
  this replaces the factors in `H` by probability measures at the cost of their masses.
-/

noncomputable section

open MeasureTheory Set Function Finset
open scoped ENNReal

namespace PGM

variable {E : Type*} [MeasurableSpace E]

/-- **Tonelli** for a product of one-coordinate functions on a finite product. -/
theorem lintegral_fin_pi_prod : ∀ {n : ℕ} (μ : Fin n → Measure E) [∀ i, SigmaFinite (μ i)]
    (g : Fin n → E → ℝ≥0∞), (∀ i, Measurable (g i)) →
    ∫⁻ x, ∏ i, g i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, g i y ∂(μ i)
  | 0, μ, _, g, _ => by
    simp
  | n + 1, μ, _, g, hg => by
    have h := (measurePreserving_piFinSuccAbove (fun i => μ i) 0).symm
    rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have hfun : (fun p : E × (Fin n → E) =>
        ∏ i, g i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm p i)) =
        fun p => g 0 p.1 * ∏ j : Fin n, g j.succ (p.2 j) := by
      funext p
      rw [Fin.prod_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
    rw [hfun, lintegral_prod_mul (f := g 0) (g := fun y : Fin n → E => ∏ j, g j.succ (y j))
        (hg 0).aemeasurable
        (Finset.measurable_prod _ fun j _ => (hg j.succ).comp (measurable_pi_apply j)).aemeasurable]
    have := lintegral_fin_pi_prod (fun j : Fin n => μ j.succ) (fun j => g j.succ)
      fun j => hg j.succ
    simp only [Fin.succAbove_zero] at this ⊢
    rw [this, Fin.prod_univ_succ]

variable {n : ℕ}

/-- Integrating out coordinates on which `f` does not depend multiplies `f` by the masses of
the corresponding factors. -/
theorem lmarginal_eq_const_mul_of_indep (μ : Fin n → Measure E) [∀ i, SigmaFinite (μ i)]
    (H : Finset (Fin n)) {f : (Fin n → E) → ℝ≥0∞} (hf : Measurable f)
    (hind : ∀ x : Fin n → E, ∀ i ∈ H, ∀ y : E, f (update x i y) = f x) :
    (∫⋯∫⁻_H, f ∂μ) = fun x => (∏ i ∈ H, μ i univ) * f x := by
  induction H using Finset.induction_on with
  | empty =>
    funext x
    simp
  | insert a s ha ih =>
    funext x
    rw [lmarginal_insert _ hf ha, Finset.prod_insert ha]
    have ih' := ih (fun x i hi y => hind x i (Finset.mem_insert_of_mem hi) y)
    simp_rw [ih', hind x a (Finset.mem_insert_self a s)]
    rw [lintegral_const]
    ring

/-- The marginal over `s` only sees the factors indexed by `s`. -/
theorem lmarginal_congr_measure {μ μ' : Fin n → Measure E} {s : Finset (Fin n)}
    (h : ∀ i ∈ s, μ i = μ' i) (f : (Fin n → E) → ℝ≥0∞) :
    (∫⋯∫⁻_s, f ∂μ) = ∫⋯∫⁻_s, f ∂μ' := by
  have : (fun i : s => μ i) = fun i : s => μ' i := funext fun i => h i i.2
  funext x
  simp only [lmarginal, this]

/-- **Swapping factors** on which the integrand does not depend. -/
theorem lintegral_pi_mul_eq_of_indep (μ μ' : Fin n → Measure E) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (μ' i)] (H : Finset (Fin n)) (hμ : ∀ i ∉ H, μ i = μ' i)
    {f : (Fin n → E) → ℝ≥0∞} (hf : Measurable f)
    (hind : ∀ x y : Fin n → E, (∀ i ∉ H, x i = y i) → f x = f y) :
    (∏ i ∈ H, μ' i univ) * ∫⁻ x, f x ∂(Measure.pi μ) =
      (∏ i ∈ H, μ i univ) * ∫⁻ x, f x ∂(Measure.pi μ') := by
  rcases isEmpty_or_nonempty (Fin n → E) with he | ⟨⟨x₀⟩⟩
  · simp [lintegral_of_isEmpty]
  have hind' : ∀ x : Fin n → E, ∀ i ∈ H, ∀ y : E, f (update x i y) = f x := by
    intro x i hi y
    refine hind _ _ fun j hj => ?_
    have : j ≠ i := fun h => hj (h ▸ hi)
    simp [update_of_ne this]
  have hsplit : ∀ (ν : Fin n → Measure E) [∀ i, SigmaFinite (ν i)],
      ∫⁻ x, f x ∂(Measure.pi ν) =
        (∏ i ∈ H, ν i univ) * (∫⋯∫⁻_Hᶜ, f ∂ν) x₀ := by
    intro ν _
    rw [lintegral_eq_lmarginal_univ x₀, ← Finset.union_compl Hᶜ, compl_compl,
      lmarginal_union ν f hf disjoint_compl_left, lmarginal_eq_const_mul_of_indep ν H hf hind']
    simp only [lmarginal]
    exact lintegral_const_mul _ (hf.comp measurable_updateFinset)
  rw [hsplit μ, hsplit μ',
    lmarginal_congr_measure (fun i hi => hμ i (Finset.mem_compl.mp hi)) f]
  ring

/-- **Replacing factors by probability measures**: if `f` does not depend on the coordinates
in `H` and `μ i = ν` off `H` for a probability measure `ν`, then
`∫⁻ f ∂(pi μ) = (∏_{i ∈ H} μ i univ) ∫⁻ f ∂(pi ν)`. -/
theorem lintegral_pi_eq_mul_of_indep (μ : Fin n → Measure E) [∀ i, SigmaFinite (μ i)]
    (ν : Measure E) [IsProbabilityMeasure ν] (H : Finset (Fin n)) (hμ : ∀ i ∉ H, μ i = ν)
    {f : (Fin n → E) → ℝ≥0∞} (hf : Measurable f)
    (hind : ∀ x y : Fin n → E, (∀ i ∉ H, x i = y i) → f x = f y) :
    ∫⁻ x, f x ∂(Measure.pi μ) = (∏ i ∈ H, μ i univ) * ∫⁻ x, f x ∂(Measure.pi fun _ => ν) := by
  have h := lintegral_pi_mul_eq_of_indep μ (fun _ => ν) H hμ hf hind
  simpa only [measure_univ, Finset.prod_const_one, one_mul] using h

/-- A finite product of laws with densities has the product density. -/
theorem pi_withDensity_fin (μ : Measure E) [SigmaFinite μ] (ρ : Fin n → E → ℝ≥0∞)
    (hρ : ∀ i, Measurable (ρ i)) [∀ i, SigmaFinite (μ.withDensity (ρ i))] :
    Measure.pi (fun i => μ.withDensity (ρ i)) =
      (Measure.pi fun _ : Fin n => μ).withDensity (fun x => ∏ i, ρ i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have : (univ.pi s).indicator (fun x : Fin n → E => ∏ i, ρ i (x i)) =
      fun x => ∏ i, (s i).indicator (ρ i) (x i) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · rw [indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [indicator_of_notMem hx]
      simp only [mem_pi, mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  rw [this, lintegral_fin_pi_prod _ _ fun i => (hρ i).indicator (hs i)]
  exact Finset.prod_congr rfl fun i _ => by
    rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

end PGM
