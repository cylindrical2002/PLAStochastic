import PLAStochastic.Index.KEP.Poisson.ParentOutput
import PLAStochastic.Index.KEP.ReferenceScale.PhysicalOutputTests

/-!
# Every positive reference layer exceeds any prescribed fixed scale

The true first-layer compression has the quadratic epsilon lower bracket.
The already proved monotone reference spans propagate that bound through
all positive layers, with the epsilon threshold selected before the layer.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

theorem kepReferenceSpan_large_layer_lower (N : ℝ) :
    ∃ E : ℝ, kepReferenceClassicalThreshold ≤ E ∧ 1 ≤ E ∧
      ∀ eps, E ≤ eps → ∀ ell : ℕ, 1 ≤ ell → N ≤ kepReferenceSpan eps ell := by
  obtain ⟨eSpan, _, _, _, hspan⟩ := kepReferenceSpan_budget
  let cb := kepGraphMeanBracket
  have hcb : 0 < cb := zero_lt_one.trans_le kepGraphMeanBracket_ge_one
  let E := max eSpan (max kepReferenceClassicalThreshold (max 1 (N * cb)))
  have hEclass : kepReferenceClassicalThreshold ≤ E := by dsimp [E]; simp
  have hE1 : 1 ≤ E := by dsimp [E]; simp
  refine ⟨E, hEclass, hE1, ?_⟩
  intro eps heps ell hell
  have he := heps
  change max eSpan (max kepReferenceClassicalThreshold (max 1 (N * cb))) ≤ eps at he
  simp only [max_le_iff] at he
  obtain ⟨heSpan, heClass, he1, heN⟩ := he
  have hs := hspan eps heSpan
  have hmono : Monotone (kepReferenceSpan eps) := by
    apply monotone_nat_of_le_succ
    intro j
    have hp := (hs.2.1 j).le
    linarith [hs.2.2.1 j]
  have hfirst : eps ^ 2 / cb ≤ kepReferenceSpan eps 1 := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, kepReferenceSpan_succ_mul_lawC heClass 0,
      hs.1, one_mul]
    exact (kepReference_lawC_bracket heClass 0).1
  have hN : N ≤ eps ^ 2 / cb := by
    rw [le_div_iff₀ hcb]
    exact heN.trans (by nlinarith)
  exact hN.trans (hfirst.trans (hmono hell))

end

end PGM
