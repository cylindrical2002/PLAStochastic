import PLAStochastic.Index.CEPS.Scaled.KernelFactorsFrequency
import PLAStochastic.Index.CEPS.Scaled.KernelBridgeJets

/-! # Actual cumulant inputs pay all finite bridge and entrance frequency premises -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCumulantJet_variance_pos (hfW : ∀ y, fW y = f (1 - y)) :
    0 < cepsJet f (cepsJetCode (.inl 0)) := by
  have hκ := cepsJet_cumulant_eq hW hθ hD hfW 0
  simp only [zero_add, iteratedDeriv_succ, iteratedDeriv_zero,
    deriv_deriv_cepsCgf_zero hW hθ hD] at hκ
  have he : cepsJet f (cepsJetCode (.inl 0)) = cepsStepVar ρW := by exact_mod_cast hκ.symm
  rw [he]
  exact cepsStepVar_pos hW hθ hD

variable (dom : CepsCanonDomain D θ v)

include hθ hD in
theorem cepsKernelFiniteFactors_cepsJet_frequency_neighborhood :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re → (lam ≠ 0 ∨ z ≠ 0) →
        ∃ B : ℝ, 0 < B ∧
          DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelBridgeJetModel (cepsJet f) N lam x.2 x.1)
            (ball 0 B ×ˢ ball z B) ∧
          DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelEntranceJetModel (cepsJet f) N lam x.2 x.1)
            (ball 0 B ×ˢ ball z B) := by
  obtain ⟨r, hr, he⟩ := cepsScaledSurrogate_finite_slope_jets dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz hne
  have hEq := (he hW hfW hneg hη hf hfS hηc hclose N hN lam hz).1 0 (Nat.zero_le N)
  simp only [complexTaylorSeries, coeff_mk, Nat.factorial_zero, Nat.cast_one, inv_one,
    iteratedDeriv_zero, one_mul] at hEq
  have hR := surrogateRegularScaleRadius_pos dom hW hθ hD N (cepsSobolev m η fW) lam z
  have hD0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hfS hηc le_rfl N (by omega)
    lam hz (mem_ball_self hR)
  have hDM0 : cepsKernelDenominatorJetModel (cepsJet f) N lam z 0 ≠ 0 := by
    rw [← hEq]; exact hD0
  exact cepsKernelFiniteFactors_frequency_neighborhood (cepsJet f)
    (cepsCumulantJet_variance_pos hW hθ hD hfW) N lam hz hne hDM0

end PGM
