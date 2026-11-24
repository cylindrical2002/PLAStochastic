import PLAStochastic.Index.KEP.ReferenceScale.FiniteGraphPolynomialBudget

/-!
# The actual complete finite graph has one total-length polynomial

All layer-uniform constants are chosen before the tolerance and the layer. The
first input norm appears once; the original second spatial kernel is separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_finite_second_graph_polynomial :
    ∃ C κ A eps0 : ℝ, 1 ≤ C ∧ 0 < κ ∧ κ ≤ 1 ∧ 1 ≤ A ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ i r n : ℕ,
        let w := 2 * eps
        let d := (n + 1 : ℕ) - w
        1 ≤ d → ∀ theta c B : ℝ, 0 ≤ theta → 0 < c → 0 ≤ B →
        ∀ φ : ℝ → ℝ, Continuous φ →
          (∀ t, 0 ≤ t → |φ t| ≤ B * Real.exp (theta * t / c)) →
        let f := (kepReferenceDensity heps hj).density
        let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let k := i + r + (n + 1)
        let S := w + (k + 1 : ℕ)
        let J := Real.sqrt (1 + kepReferenceSecondNorm eps j)
        let rate := κ / (2 * w ^ 2)
        let I2 := kepLogSlopeNorm (fun s => kepFixedBridgeRight (kepLogStep f 1)
          (kepLogStepSecond f'' 1) w s n 0 w)
        |kepCertificateSecondGraph f f' f'' eps d i r n φ| ≤
          (1 + C * w) ^ 2 * (B * Real.exp (2 * theta * ((k : ℝ) + w) / c)) *
            (4 * A * S ^ 3 * I2 * Real.exp (-rate * (i + r : ℕ)) +
              684 * A * C ^ 3 * S ^ 5 * J * Real.exp (-rate * (n + 1 + i + r : ℕ))) := by
  obtain ⟨C, κ, A, eps0, hC, hκ, hκ1, hA, he0, hgraph⟩ :=
    kepReference_finite_second_graph_uniform
  refine ⟨C, κ, A, eps0, hC, hκ, hκ1, hA, he0, ?_⟩
  intro eps he heps j hj i r n
  dsimp only
  intro hd theta c B ht hc hB φ hφ hφb
  let w := 2 * eps
  let d := (n + 1 : ℕ) - w
  let k := i + r + (n + 1)
  let S := w + (k + 1 : ℕ)
  let J := Real.sqrt (1 + kepReferenceSecondNorm eps j)
  have hw : 0 ≤ w := by
    have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
    dsimp [w]
    linarith
  have hS : 1 ≤ S := by
    have hh : (0 : ℝ) ≤ (k : ℝ) := by positivity
    dsimp [S]
    push_cast
    linarith
  have hd0 : 0 ≤ d := by change 1 ≤ d at hd; linarith
  have hnL : n + 1 ≤ k + 1 := by dsimp [k]; omega
  have hnL' : ((n + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hnL
  have hnS : (n : ℝ) ≤ S := by dsimp [S]; push_cast at hnL' ⊢; linarith
  have hlen : w + (n + 1 : ℕ) ≤ S := by dsimp [S]; linarith only [hnL']
  have hdS : d ≤ S := by dsimp [d, S]; linarith
  have hext : ((i + r : ℕ) : ℝ) ≤ S := by
    have hh : i + r ≤ k + 1 := by dsimp [k]; omega
    have hh' : ((i + r : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hh
    dsimp [S]
    linarith
  have hwe : w + (i + r : ℕ) ≤ S := by
    have hh : i + r ≤ k + 1 := by dsimp [k]; omega
    have hh' : ((i + r : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hh
    dsimp [S]
    linarith only [hh']
  have hJ : 1 ≤ J := Real.one_le_sqrt.mpr (by linarith [kepReferenceSecondNorm_nonneg eps j])
  have hA0 : 0 ≤ A := by linarith
  have hcoef := kepGraphSecondBudget_polynomial hC hJ hw hS hd0 hdS hA0 n i r hnS hlen hext hwe
  have hsecond : d * A * (w + (n + 1 : ℕ)) ^ 2 ≤ A * S ^ 3 := by
    calc
      _ ≤ S * A * S ^ 2 := by gcongr
      _ = _ := by ring
  have hI := kepLogSlopeNorm_nonneg (fun s => kepFixedBridgeRight
    (kepLogStep (kepReferenceDensity heps hj).density 1)
    (kepLogStepSecond (gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)) 1)
    w s n 0 w)
  have hh := hgraph eps he heps j hj i r n hd theta c B ht hc hB φ hφ hφb
  apply hh.trans
  rw [show 4 * A * (w + (k + 1 : ℕ)) ^ 3 = 4 * (A * S ^ 3) by dsimp [S]; ring]
  gcongr

end

end PGM
