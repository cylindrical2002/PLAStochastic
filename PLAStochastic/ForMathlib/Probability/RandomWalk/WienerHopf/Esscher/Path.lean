import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Esscher.Measure
import PLAStochastic.ForMathlib.MeasureTheory.Constructions.PiFactor

/-!
# Finite-prefix Esscher change of measure

Only a finite prefix is tilted. No Radon--Nikodym density for the infinite
product law is asserted.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ]

theorem measurePreserving_seqPrefix (n : ℕ) :
    MeasurePreserving (seqPrefix n) (pathLaw ρ) (Measure.pi (fun _ : Fin n => ρ)) := by
  refine ⟨measurable_seqPrefix n, ?_⟩
  exact (Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => ρ) (f := fun i : Fin n => (i : ℕ)) Fin.val_injective).trans
      (Measure.infinitePi_eq_pi _)

theorem partialSum_eq_sum_fin (n : ℕ) (ω : ℕ → ℝ) :
    partialSum n ω = ∑ i : Fin n, ω i := by
  simp only [partialSum, Fin.sum_univ_eq_sum_range]

theorem integral_dependsOnPrefix {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {F : (ℕ → ℝ) → 𝕜} (hF : Measurable F) (hd : DependsOnPrefix n F) :
    (∫ ω, F ω ∂pathLaw ρ) =
      ∫ x : Fin n → ℝ, F (extendPrefix n x) ∂Measure.pi (fun _ : Fin n => ρ) := by
  conv_lhs => enter [2, ω]; rw [hd.eq_comp ω]
  rw [← integral_map (φ := seqPrefix n) (f := fun x => F (extendPrefix n x))
    (measurable_seqPrefix n).aemeasurable
    ((hF.comp (measurable_extendPrefix n)).aestronglyMeasurable),
    (measurePreserving_seqPrefix (ρ := ρ) n).map_eq]

theorem integrable_dependsOnPrefix_iff {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    {F : (ℕ → ℝ) → 𝕜} (hF : Measurable F) (hd : DependsOnPrefix n F) :
    Integrable F (pathLaw ρ) ↔
      Integrable (fun x : Fin n → ℝ => F (extendPrefix n x))
        (Measure.pi (fun _ : Fin n => ρ)) := by
  have he : F = (fun x => F (extendPrefix n x)) ∘ seqPrefix n :=
    funext fun ω => hd.eq_comp ω
  conv_lhs => rw [he]
  exact ((measurePreserving_seqPrefix (ρ := ρ) n).integrable_comp
    ((hF.comp (measurable_extendPrefix n)).aestronglyMeasurable))

theorem esscher_pi_eq_withDensity {β q : ℝ}
    (hβ : Integrable (fun y => Real.exp (β * y)) ρ)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q) (n : ℕ) :
    Measure.pi (fun _ : Fin n => esscherLaw ρ β) =
      (Measure.pi (fun _ : Fin n => ρ)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (β * (∑ i, x i) - q * n))) := by
  have := isProbabilityMeasure_esscherLaw hβ
  have : IsProbabilityMeasure
      (ρ.withDensity (fun y => ENNReal.ofReal (Real.exp (β * y - q)))) := by
    rw [← esscherLaw_eq_withDensity hroot]
    infer_instance
  rw [esscherLaw_eq_withDensity hroot, pi_withDensity_fin ρ _ (by fun_prop)]
  congr 1
  funext x
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 1
  simp [Finset.sum_sub_distrib, ← Finset.mul_sum, nsmul_eq_mul, mul_comm]

/-- The exact finite-prefix density is `exp (β S_n - q n)`. -/
theorem integral_esscher_prefix {𝕜 : Type*} [RCLike 𝕜] {β q : ℝ}
    (hβ : Integrable (fun y => Real.exp (β * y)) ρ)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q) {n : ℕ}
    {F : (ℕ → ℝ) → 𝕜} (hF : Measurable F) (hd : DependsOnPrefix n F) :
    (∫ ω, F ω ∂pathLaw (esscherLaw ρ β)) =
      ∫ ω, Real.exp (β * partialSum n ω - q * n) • F ω ∂pathLaw ρ := by
  have := isProbabilityMeasure_esscherLaw hβ
  rw [integral_dependsOnPrefix hF hd, esscher_pi_eq_withDensity hβ hroot n,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hg : Measurable fun ω => Real.exp (β * partialSum n ω - q * n) • F ω := by fun_prop
  have hgd : DependsOnPrefix n
      (fun ω => Real.exp (β * partialSum n ω - q * n) • F ω) := by
    intro ω ω' he
    dsimp only
    rw [partialSum_congr he, hd ω ω' he]
  rw [integral_dependsOnPrefix hg hgd]
  congr 1
  funext x
  rw [partialSum_eq_sum_fin]
  simp [extendPrefix]

/-- Integrability transfers with the same finite-prefix likelihood ratio. -/
theorem integrable_esscher_prefix_iff {𝕜 : Type*} [RCLike 𝕜] {β q : ℝ}
    (hβ : Integrable (fun y => Real.exp (β * y)) ρ)
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q) {n : ℕ}
    {F : (ℕ → ℝ) → 𝕜} (hF : Measurable F) (hd : DependsOnPrefix n F) :
    Integrable F (pathLaw (esscherLaw ρ β)) ↔
      Integrable (fun ω => Real.exp (β * partialSum n ω - q * n) • F ω) (pathLaw ρ) := by
  have := isProbabilityMeasure_esscherLaw hβ
  have hg : Measurable fun ω => Real.exp (β * partialSum n ω - q * n) • F ω := by fun_prop
  have hgd : DependsOnPrefix n
      (fun ω => Real.exp (β * partialSum n ω - q * n) • F ω) := by
    intro ω ω' he
    dsimp only
    rw [partialSum_congr he, hd ω ω' he]
  rw [integrable_dependsOnPrefix_iff hF hd, esscher_pi_eq_withDensity hβ hroot n,
    integrable_withDensity_iff_integrable_smul₀' (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integrable_dependsOnPrefix_iff hg hgd]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, partialSum_eq_sum_fin]
  simp [extendPrefix]

end PGM.WienerHopf
