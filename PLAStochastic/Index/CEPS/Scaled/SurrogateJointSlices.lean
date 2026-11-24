import PLAStochastic.Index.CEPS.Scaled.QuotientJointContinuity
import PLAStochastic.Index.CEPS.Scaled.JointRootChart

/-! # Joint surrogate spatial continuity and holomorphic parameter slices

Actual chart bounds supply every premise. Only the finite drift Taylor
polynomial is evaluated holomorphically at complex drift.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

set_option maxHeartbeats 800000 in
include hW hθ hD in
theorem cepsScaledSurrogateG_joint_on_root_chart {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {S : ℝ}
    (hp : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSignedRoot D θ ρW lam x.2 1 x.1) (U ×ˢ V))
    (hm : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1) (U ×ˢ V))
    (hbounds : ∀ x ∈ U ×ˢ V,
      ‖x.1 * (lam : ℂ)‖ < dom.μ₀ ∧
      ‖x.1 * cepsScaledRootCoordinate D θ ρW lam x.2 x.1‖ < dom.rmax ∧
      ‖cepsComplexScaledDiscount lam x.2 x.1‖ < dom.q₀ / 2 ∧
      ‖x.1‖ * S < dom.c₀ / 2 ∧
      cepsScaledSignedRoot D θ ρW lam x.2 1 x.1 ∈ ball 0 S ∧
      cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1 ∈ ball 0 S) :
    ContinuousOn (fun x : (ℂ × ℂ) × ℂ => cepsScaledSurrogateG dom ρW N lam x.1.2 x.1.1 x.2)
      ((U ×ˢ V) ×ˢ ball 0 S) ∧
    (∀ z ∈ V, DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateG dom ρW N lam z x.1 x.2)
      (U ×ˢ ball 0 S)) ∧
    (∀ b ∈ U, DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateG dom ρW N lam x.1 b x.2)
      (V ×ˢ ball 0 S)) := by
  have hphys : ∀ x ∈ U ×ˢ V, ∀ ξ ∈ ball (0 : ℂ) S, ‖x.1 * ξ‖ < dom.c₀ / 2 := by
    intro x hx ξ hξ
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hξ).le (norm_nonneg x.1)).trans_lt
      (hbounds x hx).2.2.2.1
  have hphysA : ∀ x ∈ U ×ˢ V, ∀ ξ ∈ ball (0 : ℂ) S, x.1 * ξ ∈ ball (0 : ℂ) dom.ρA := by
    intro x hx ξ hξ
    apply mem_ball_zero_iff.mpr
    have hn := hphys x hx ξ hξ
    have := dom.c₀_le
    have := dom.ρA_pos
    linarith
  have hpmap : MapsTo (fun x : ℂ × ℂ => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 1 x.1)
      (U ×ˢ V) (ball 0 dom.ρA) := fun x hx => hphysA x hx _ (hbounds x hx).2.2.2.2.1
  have hmmap : MapsTo (fun x : ℂ × ℂ => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1)
      (U ×ˢ V) (ball 0 dom.ρA) := fun x hx => hphysA x hx _ (hbounds x hx).2.2.2.2.2
  have hpc := differentiableOn_fst.mul hp
  have hmc := differentiableOn_fst.mul hm
  have hQc := cepsScaledQuotient_continuousOn_joint_on_root_chart dom hW hθ hD lam
    (hU.prod hV) hpc hmc hpmap hmmap
  obtain ⟨hQ₁, hQ₂⟩ := cepsScaledQuotient_holomorphic_slices_on_root_chart dom hW hθ hD lam
    hU hV hpc hmc hpmap hmmap
  have hident : ∀ x ∈ U ×ˢ V, ∀ ξ : ℂ,
      cepsQ D θ ρW (x.1 * lam) (cepsComplexScaledDiscount lam x.2 x.1) ξ =
        cepsScaledQuotient D θ ρW lam x.2 x.1 ξ := fun x hx ξ =>
    (cepsScaledQuotient_eq_actual_of_morse_bounds dom hW hθ hD lam x.2 x.1 ξ
      (hbounds x hx).1.le (hbounds x hx).2.1).symm
  have hQ : ContinuousOn (fun x : (ℂ × ℂ) × ℂ =>
      cepsQ D θ ρW (x.1.1 * lam) (cepsComplexScaledDiscount lam x.1.2 x.1.1) (x.1.1 * x.2))
      ((U ×ˢ V) ×ˢ ball 0 S) := by
    apply (hQc.comp (f := fun x : (ℂ × ℂ) × ℂ => (x.1, x.1.1 * x.2))
      (by fun_prop) (fun x hx => ⟨hx.1, hphysA x.1 hx.1 x.2 hx.2⟩)).congr
    intro x hx
    exact hident x.1 hx.1 (x.1.1 * x.2)
  have hL : DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ =>
      cepsCanonDriftTaylor dom ρW N (x.1.1 * lam)
        (cepsComplexScaledDiscount lam x.1.2 x.1.1) (x.1.1 * x.2))
      ((U ×ˢ V) ×ˢ ball 0 S) := by
    apply (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp
      (f := fun x : (ℂ × ℂ) × ℂ => (x.1.1 * (lam : ℂ),
        (cepsComplexScaledDiscount lam x.1.2 x.1.1, x.1.1 * x.2))) ?_ ?_
    · unfold cepsComplexScaledDiscount
      fun_prop
    · intro x hx
      exact ⟨(re_le_norm _).trans_lt ((hphys x.1 hx.1 x.2 hx.2).trans
        (half_lt_self dom.c₀_pos)), (hbounds x.1 hx.1).2.2.1⟩
  have hE : DifferentiableOn ℂ (fun x : (ℂ × ℂ) × ℂ => exp (-x.2 * (1 + x.1.1 * lam)))
      ((U ×ˢ V) ×ˢ ball 0 S) := by fun_prop
  refine ⟨hE.continuousOn.mul (hQ.mul ((hL.const_mul (-2)).cexp.continuousOn)), ?_, ?_⟩
  · intro z hz
    have hQz : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
        cepsQ D θ ρW (x.1 * lam) (cepsComplexScaledDiscount lam z x.1) (x.1 * x.2))
        (U ×ˢ ball 0 S) := by
      apply ((hQ₁ z hz).comp (f := fun x : ℂ × ℂ => (x.1, x.1 * x.2))
        (by fun_prop) (fun x hx => ⟨hx.1, hphysA (x.1, z) ⟨hx.1, hz⟩ x.2 hx.2⟩)).congr
      intro x hx
      exact hident (x.1, z) ⟨hx.1, hz⟩ (x.1 * x.2)
    have hLz := hL.comp (s := U ×ˢ ball (0 : ℂ) S)
      (f := fun x : ℂ × ℂ => ((x.1, z), x.2)) (by fun_prop)
      (fun x hx => ⟨⟨hx.1, hz⟩, hx.2⟩)
    have hEz := hE.comp (s := U ×ˢ ball (0 : ℂ) S)
      (f := fun x : ℂ × ℂ => ((x.1, z), x.2)) (by fun_prop)
      (fun x hx => ⟨⟨hx.1, hz⟩, hx.2⟩)
    exact hEz.mul (hQz.mul ((hLz.const_mul (-2)).cexp))
  · intro b hb
    have hQb : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
        cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam x.1 b) (b * x.2))
        (V ×ˢ ball 0 S) := by
      apply ((hQ₂ b hb).comp (f := fun x : ℂ × ℂ => (x.1, b * x.2))
        (by fun_prop) (fun x hx => ⟨hx.1, hphysA (b, x.1) ⟨hb, hx.1⟩ x.2 hx.2⟩)).congr
      intro x hx
      exact hident (b, x.1) ⟨hb, hx.1⟩ (b * x.2)
    have hLb := hL.comp (s := V ×ˢ ball (0 : ℂ) S)
      (f := fun x : ℂ × ℂ => ((b, x.1), x.2)) (by fun_prop)
      (fun x hx => ⟨⟨hb, hx.1⟩, hx.2⟩)
    have hEb := hE.comp (s := V ×ˢ ball (0 : ℂ) S)
      (f := fun x : ℂ × ℂ => ((b, x.1), x.2)) (by fun_prop)
      (fun x hx => ⟨⟨hb, hx.1⟩, hx.2⟩)
    exact hEb.mul (hQb.mul ((hLb.const_mul (-2)).cexp))

end PGM
