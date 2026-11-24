import PLAStochastic.Index.CEPS.Scaled.KernelFactorsActualFrequency
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeJoint
import PLAStochastic.ForMathlib.Analysis.Complex.RightGermEquality

/-! # Exact finite jets of the genuine bridge frequency derivative -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledSurrogateBridge_frequency_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re → (lam ≠ 0 ∨ z ≠ 0) → ∀ j ≤ N,
        coeff j (complexTaylorSeries (fun b => deriv (fun w => cepsScaledSurrogateBridge dom ρW N lam w b) z) 0) =
        coeff j (complexTaylorSeries (fun b => deriv (fun w => cepsKernelBridgeJetModel (cepsJet f) N lam w b) z) 0) := by
  obtain ⟨rJ, hrJ, heJ⟩ := cepsScaledSurrogateBridge_taylorJets_eq_finite_model dom hθ hD
  obtain ⟨rF, hrF, heF⟩ := cepsKernelFiniteFactors_cepsJet_frequency_neighborhood hθ hD dom
  refine ⟨min rJ rF, lt_min hrJ hrF, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz hne
  obtain ⟨BF, hBF, hF, _⟩ := heF hW hfW hneg hη hf hfS hηc
    (hclose.trans (min_le_right _ _)) N hN lam hz hne
  have hRA : 0 < min (dom.jointRootScaleRadius lam z)
      (dom.entranceScaleRadius N (cepsSobolev m η fW) lam z) :=
    lt_min (jointRootScaleRadius_pos dom hW hθ hD lam z)
      (entranceScale_constants dom hW hθ hD N (cepsSobolev m η fW) lam z).1
  obtain ⟨BA, hBA, hA, _⟩ := cepsScaledSurrogateBridge_holomorphic_near_joint
    dom hW hθ hD hfS hηc le_rfl N (by omega) lam hz hne (mem_ball_self hRA)
  let B := min BA BF
  have hB : 0 < B := lt_min hBA hBF
  have hsubA : ball (0 : ℂ) B ×ˢ ball z B ⊆ ball (0 : ℂ) BA ×ˢ ball z BA :=
    fun _ hx => ⟨ball_subset_ball (min_le_left _ _) hx.1, ball_subset_ball (min_le_left _ _) hx.2⟩
  have hsubF : ball (0 : ℂ) B ×ˢ ball z B ⊆ ball (0 : ℂ) BF ×ˢ ball z BF :=
    fun _ hx => ⟨ball_subset_ball (min_le_right _ _) hx.1, ball_subset_ball (min_le_right _ _) hx.2⟩
  apply complexTaylorSeries_frequency_jets_eq_of_right_values hB (hA.mono hsubA) (hF.mono hsubF) N
    (fun w _ hw j hj => heJ hW hfW hneg hη hf hfS hηc
      (hclose.trans (min_le_left _ _)) N hN lam hw j hj) hz

end PGM
