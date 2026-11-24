import PLAStochastic.Index.KEP.Additive.GeneralDensity
import PLAStochastic.Index.KEP.CountRoute.ReferenceCount
import PLAStochastic.Index.Algorithm.MeasurableEndpointHeight
import Mathlib.Probability.Independence.InfinitePi

/-!
# Model K endpoint height with constants depending only on the density

`H_K_EP_additive_law`: for every `DensityK f A B fmin fmax Lf`, one pair `ε₀, K` serves every
probability space and every iid sample `X` with marginal `densityLaw f A B`:
`|E H_EP(kKeys X N) - log N / log C_ε| ≤ K` for all `ε ≥ ε₀` and `N ≥ 2`.
The constants are those of `H_K_EP_additive` on the canonical product space
`infinitePi (densityLaw f A B)`.  The height of the sorted keys is a measurable function of
the sample sequence, whose joint law is that product measure by independence, so the
expectation is the same on every sample space.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

universe u

/-- **P-KEP, law form.** For every Model K density, the constants `ε₀, K` of the additive
endpoint height bound depend only on the density: the same pair serves every probability space
and every iid sample with marginal `densityLaw f A B`. -/
theorem H_K_EP_additive_law {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}
    (hf : DensityK f A B fmin fmax Lf) :
    ∃ eps0 K : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ),
      (∀ i, HasLaw (X i) (densityLaw f A B) P) → iIndepFun X P →
      ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n →
        |(∫ omega, (epHeight eps (kKeys X n omega) n : ℝ) ∂P) -
          Real.log n / Real.log (gepC eps)| ≤ K := by
  have := isProbabilityMeasure_densityLaw hf
  have hcoord (i : ℕ) : HasLaw (fun z : ℕ → ℝ => z i) (densityLaw f A B)
      (Measure.infinitePi fun _ : ℕ => densityLaw f A B) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => densityLaw f A B) i).hasLaw
  have hind : iIndepFun (fun (i : ℕ) (z : ℕ → ℝ) => z i)
      (Measure.infinitePi fun _ : ℕ => densityLaw f A B) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => densityLaw f A B) (X := fun _ x => x)
      (fun _ => measurable_id)
  obtain ⟨eps0, K, hK⟩ := H_K_EP_additive hf hcoord hind
  refine ⟨eps0, K, fun {Ω} _ P X hX hXind eps heps n hn => ?_⟩
  have hF : Measurable fun z : ℕ → ℝ =>
      (epHeight eps (kKeys (fun (i : ℕ) (z : ℕ → ℝ) => z i) n z) n : ℝ) :=
    measurable_from_nat.comp
      ((measurable_epHeight eps n).comp (measurable_kKeys (fun i => measurable_pi_apply i) n))
  have hlaw : HasLaw (fun ω i => X i ω) (Measure.infinitePi fun _ : ℕ => densityLaw f A B) P :=
    hXind.hasLaw_infinitePi (μ := fun _ => densityLaw f A B) hX
      (aemeasurable_pi_iff.2 fun i => (hX i).aemeasurable)
  have hP : (∫ omega, (epHeight eps (kKeys X n omega) n : ℝ) ∂P) =
      ∫ z, (epHeight eps (kKeys (fun (i : ℕ) (z : ℕ → ℝ) => z i) n z) n : ℝ)
        ∂(Measure.infinitePi fun _ : ℕ => densityLaw f A B) :=
    hlaw.integral_comp hF.aestronglyMeasurable
  rw [hP]
  exact hK eps heps n hn

end

end PGM
