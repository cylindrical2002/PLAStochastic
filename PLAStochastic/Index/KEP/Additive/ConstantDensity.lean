import PLAStochastic.Index.ModelK.ConstantDensity
import PLAStochastic.Index.GEP.Additive.UnconditionalHeight

/-!
# Additive endpoint height for a constant Model K density

The exact constant-density expectation transfer identifies the actual sorted-sample
height with the endpoint height of iid exponential gaps. The universal denominator
is the same `gepC eps` as in the unconditional Model G theorem. Both parameters
are quantified pointwise: every `n ≥ 2` and every sufficiently large `eps`.
-/

set_option autoImplicit false

namespace PGM

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : ℝ → ℝ} {A B : ℝ}

/-- Constant Model K densities satisfy the full additive endpoint height bound,
with the exact universal compression ratio and no growth restriction on `n`. -/
theorem H_K_EP_const_additive
    (hAB : A < B) (hc : ∀ x ∈ Set.Icc A B, f x = 1 / (B - A))
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P)
    (hind : iIndepFun X P) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |∫ ω, (epHeight eps (kKeys X n ω) n : ℝ) ∂P -
        Real.log n / Real.log (gepC eps)| ≤ K := by
  have hpos : ∀ᵐ ω ∂expSeqMeasure, 0 < expCoord 1 ω :=
    iidSeq_expCoord.ae_pos_of_expMeasure_one (hasLaw_expCoord 0) 1
  obtain ⟨eps0, K, hK⟩ := H_G_EP_additive gapLaw_expCoord_succ hpos (expCoord 0)
  refine ⟨eps0, K, fun eps heps n hn => ?_⟩
  rw [integral_epHeight_kKeys_const hAB hc hX hind eps n]
  exact hK eps heps n hn

end PGM
