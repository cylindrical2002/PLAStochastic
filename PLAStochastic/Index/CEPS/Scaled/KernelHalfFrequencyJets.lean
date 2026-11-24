import PLAStochastic.Index.CEPS.Scaled.KernelHalfFrequency
import PLAStochastic.Index.CEPS.Scaled.KernelHalfJets
import PLAStochastic.Index.CEPS.Scaled.HalfBridgeJoint
import PLAStochastic.ForMathlib.Analysis.Complex.RightGermEquality

/-! # Exact finite jets of the genuine positive-side half-bridge frequency derivative -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledSurrogateHalfBridge_frequency_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ), 1 ≤ lam → ∀ {z : ℂ}, 0 ≤ z.re → ∀ j ≤ N,
        coeff j (complexTaylorSeries (fun b => deriv (fun w => cepsScaledSurrogateHalfBridge dom ρW N lam w b) z) 0) =
        coeff j (complexTaylorSeries (fun b => deriv (fun w => cepsKernelHalfBridgeJetModel (cepsJet f) N lam w b) z) 0) := by
  obtain ⟨r, hr, heJ⟩ := cepsScaledSurrogateHalfFactors_taylorJets_eq_finite_model dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam hlam z hz
  obtain ⟨BF, hBF, hF, _⟩ := cepsKernelHalfFactors_cepsJet_frequency_neighborhood dom hW hθ hD hfW N lam hlam hz
  have hRA : 0 < min (dom.jointRootScaleRadius lam z)
      (dom.entranceScaleRadius N (cepsSobolev m η fW) lam z) :=
    lt_min (jointRootScaleRadius_pos dom hW hθ hD lam z)
      (entranceScale_constants dom hW hθ hD N (cepsSobolev m η fW) lam z).1
  obtain ⟨BA, hBA, hA, _⟩ := cepsScaledSurrogateHalfBridge_holomorphic_near_joint
    dom hW hθ hD hfS hηc N (by omega) lam hz (Or.inl (by linarith)) (mem_ball_self hRA)
  let B := min BA BF
  have hB : 0 < B := lt_min hBA hBF
  have hsubA : ball (0 : ℂ) B ×ˢ ball z B ⊆ ball (0 : ℂ) BA ×ˢ ball z BA :=
    fun _ hx => ⟨ball_subset_ball (min_le_left _ _) hx.1, ball_subset_ball (min_le_left _ _) hx.2⟩
  have hsubF : ball (0 : ℂ) B ×ˢ ball z B ⊆ ball (0 : ℂ) BF ×ˢ ball z BF :=
    fun _ hx => ⟨ball_subset_ball (min_le_right _ _) hx.1, ball_subset_ball (min_le_right _ _) hx.2⟩
  apply complexTaylorSeries_frequency_jets_eq_of_right_values hB (hA.mono hsubA) (hF.mono hsubF) N
    (fun w _ hw j hj => (heJ hW hfW hneg hη hf hfS hηc hclose N hN lam hw).1 j hj) hz

end PGM
