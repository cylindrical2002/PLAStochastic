import PLAStochastic.Index.CEPS.Normal.ActualQuotient
import PLAStochastic.Index.CEPS.Normal.JointSqrtDescent

/-! # Joint discount/spatial holomorphy of the actual quotient -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

/-- Equality with the original quotient, including the square-root branch cut. -/
theorem cepsMorseQ_sqrt_eq_cepsQ (D θ : ℝ) (ρW : Measure ℝ) (μ q ζ : ℂ) :
    cepsMorseQ D θ ρW μ (Complex.sqrt (q - cepsMorseMin D θ ρW μ)) ζ =
      cepsQ D θ ρW μ q ζ := by
  have hq : cepsMorseMin D θ ρW μ +
      Complex.sqrt (q - cepsMorseMin D θ ρW μ) ^ 2 = q := by
    rw [sqrt_sq_eq]; ring
  unfold cepsMorseQ cepsQ cepsRootPlus cepsRootMinus cepsRootR
  rw [hq]

theorem cepsQ_differentiableOn_joint_q_spatial
    {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
    (hθ : 0 < θ) (hD : 0 < D) {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsQ D θ ρW μ x.1 x.2)
      ({q | ‖q - cepsMorseMin D θ ρW μ‖ < dom.rmax ^ 2} ×ˢ ball 0 dom.ρA) := by
  have hQ := cepsMorseQ_differentiableOn_joint dom hW hθ hD hμ
  have hpSwap : DifferentiableOn ℂ (fun x : ℂ × ℂ => (x.2, x.1))
      (ball 0 dom.ρA ×ˢ ball 0 dom.rmax) := by fun_prop
  have hmapSwap : MapsTo (fun x : ℂ × ℂ => (x.2, x.1))
      (ball 0 dom.ρA ×ˢ ball 0 dom.rmax) (ball 0 dom.rmax ×ˢ ball 0 dom.ρA) :=
    fun _ hx => ⟨hx.2, hx.1⟩
  have hswap : DifferentiableOn ℂ
      (fun x : ℂ × ℂ => cepsMorseQ D θ ρW μ x.2 x.1)
      (ball 0 dom.ρA ×ˢ ball 0 dom.rmax) :=
    hQ.comp (f := fun x : ℂ × ℂ => (x.2, x.1)) hpSwap hmapSwap
  have heven : ∀ z ∈ ball (0 : ℂ) dom.ρA, ∀ r ∈ ball (0 : ℂ) dom.rmax,
      cepsMorseQ D θ ρW μ (-r) z = cepsMorseQ D θ ρW μ r z :=
    fun z _ r hr => cepsMorseQ_neg dom hW hθ hD hμ (mem_ball_zero_iff.mp hr)
  have hdisc := cepsNormal_differentiableOn_joint_comp_sqrt
    (G := fun z r => cepsMorseQ D θ ρW μ r z) isOpen_ball
    dom.rmax_pos hswap heven
  have hp : DifferentiableOn ℂ
      (fun x : ℂ × ℂ => (x.2, x.1 - cepsMorseMin D θ ρW μ))
      ({q | ‖q - cepsMorseMin D θ ρW μ‖ < dom.rmax ^ 2} ×ˢ ball 0 dom.ρA) :=
    differentiableOn_snd.prodMk (differentiableOn_fst.sub_const _)
  have hd : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      cepsMorseQ D θ ρW μ (Complex.sqrt (x.1 - cepsMorseMin D θ ρW μ)) x.2)
      ({q | ‖q - cepsMorseMin D θ ρW μ‖ < dom.rmax ^ 2} ×ˢ ball 0 dom.ρA) :=
    hdisc.comp (f := fun x : ℂ × ℂ => (x.2, x.1 - cepsMorseMin D θ ρW μ))
      hp (fun _ hx => ⟨hx.2, mem_ball_zero_iff.mpr hx.1⟩)
  apply hd.congr
  intro x _
  exact (cepsMorseQ_sqrt_eq_cepsQ D θ ρW μ x.1 x.2).symm

end PGM
