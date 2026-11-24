import PLAStochastic.Index.CEPS.Scaled.TrueGDriftContinuity
import PLAStochastic.Index.CEPS.Scaled.TrueSlopeError

/-! # Actual real-drift continuity of scaled moving divided differences -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueSlopes_continuousOn_drift {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {U : Set ℝ} (hU : IsOpen U) (b : ℝ) (z : ℂ) {S : ℝ}
    (hS : ‖(b : ℂ)‖ * S < dom.c₀ / 2)
    (hcoords : ∀ lam ∈ U, |b * lam| < dom.μ₀ / 4 ∧
      ‖cepsComplexScaledDiscount lam z b‖ < dom.q₀ / 2 ∧
      0 ≤ (cepsComplexScaledDiscount lam z b).re)
    (hp : ContinuousOn (fun lam => cepsScaledSignedRoot D θ ρW lam z 1 b) U)
    (ha : ContinuousOn (fun lam => cepsScaledSignedRoot D θ ρW lam z (-1) b) U)
    (hpmap : MapsTo (fun lam => cepsScaledSignedRoot D θ ρW lam z 1 b) U (ball 0 S))
    (hamap : MapsTo (fun lam => cepsScaledSignedRoot D θ ρW lam z (-1) b) U (ball 0 S))
    (ht : (b : ℂ) * z ∈ ball (0 : ℂ) S) :
    ContinuousOn (fun lam => cepsScaledTrueDenominator dom ρW lam z b) U ∧
      ContinuousOn (fun lam => cepsScaledTrueEntranceNumerator dom ρW lam z b) U ∧
      ContinuousOn (fun lam => cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)) U ∧
      ContinuousOn (fun lam => cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z (-1) b)) U := by
  have hG := cepsScaledTrueG_continuousOn_joint_drift_spatial dom hW hθ hD hf hm hη hU b z hS hcoords
  have hd : ∀ lam ∈ U, DifferentiableOn ℂ (cepsScaledTrueG dom ρW lam z b) (ball 0 S) :=
    fun lam hlam => cepsScaledTrueG_spatial_differentiableOn_of_curve_bounds dom hW hθ hD b lam z hS
      ((hcoords lam hlam).1.le.trans (by linarith [dom.μ₀_pos]))
      ((hcoords lam hlam).2.1.le.trans (half_le_self dom.q₀_pos.le))
  have hD := cepsNormal_continuousOn_joint_moving_dslope_general
    (G := fun lam ξ => cepsScaledTrueG dom ρW lam z b ξ)
    (a := fun lam => cepsScaledSignedRoot D θ ρW lam z (-1) b)
    hU hG hd ha hamap
  have hN := cepsNormal_continuousOn_joint_moving_second_dslope_general
    (G := fun lam ξ => cepsScaledTrueG dom ρW lam z b ξ)
    (a := fun lam => cepsScaledSignedRoot D θ ρW lam z (-1) b)
    (b := fun lam => cepsScaledSignedRoot D θ ρW lam z 1 b)
    hU hG hd ha hp hamap hpmap
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hD.comp (f := fun lam : ℝ => (lam, cepsScaledSignedRoot D θ ρW lam z 1 b))
      (continuousOn_id.prodMk hp) (fun lam hlam => ⟨hlam, hpmap hlam⟩)
  · exact hN.comp (f := fun lam : ℝ => (lam, (b : ℂ) * z))
      (continuousOn_id.prodMk continuousOn_const) (fun lam hlam => ⟨hlam, ht⟩)
  · exact hG.comp (f := fun lam : ℝ => (lam, cepsScaledSignedRoot D θ ρW lam z 1 b))
      (continuousOn_id.prodMk hp) (fun lam hlam => ⟨hlam, hpmap hlam⟩)
  · exact hG.comp (f := fun lam : ℝ => (lam, cepsScaledSignedRoot D θ ρW lam z (-1) b))
      (continuousOn_id.prodMk ha) (fun lam hlam => ⟨hlam, hamap hlam⟩)

end PGM
