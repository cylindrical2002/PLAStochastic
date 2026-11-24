import PLAStochastic.Index.CEPS.Scaled.SurrogateGDriftContinuity
import PLAStochastic.Index.CEPS.Scaled.TrueSlopeError

/-! # Surrogate real-drift continuity of scaled moving divided differences -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateSlopes_continuousOn_drift {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (N : ℕ) (hN : N + 1 ≤ m)
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
    ContinuousOn (fun lam => cepsScaledSurrogateDenominator dom ρW N lam z b) U ∧
      ContinuousOn (fun lam => dslope (dslope (cepsScaledSurrogateG dom ρW N lam z b)
        (cepsScaledSignedRoot D θ ρW lam z (-1) b))
          (cepsScaledSignedRoot D θ ρW lam z 1 b) ((b : ℂ) * z)) U ∧
      ContinuousOn (fun lam => cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)) U ∧
      ContinuousOn (fun lam => cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z (-1) b)) U := by
  have hG := cepsScaledSurrogateG_continuousOn_joint_drift_spatial dom hW hθ hD hf hη N hN hU b z hS hcoords
  have hd : ∀ lam ∈ U, DifferentiableOn ℂ (cepsScaledSurrogateG dom ρW N lam z b) (ball 0 S) :=
    fun lam hlam => cepsScaledSurrogateG_spatial_differentiableOn_of_curve_bounds dom hW hθ hD hf hη N hN b lam z hS
      ((hcoords lam hlam).1.le.trans (by linarith [dom.μ₀_pos]))
      (hcoords lam hlam).2.1
  have hD := cepsNormal_continuousOn_joint_moving_dslope_general
    (G := fun lam ξ => cepsScaledSurrogateG dom ρW N lam z b ξ)
    (a := fun lam => cepsScaledSignedRoot D θ ρW lam z (-1) b)
    hU hG hd ha hamap
  have hN := cepsNormal_continuousOn_joint_moving_second_dslope_general
    (G := fun lam ξ => cepsScaledSurrogateG dom ρW N lam z b ξ)
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
