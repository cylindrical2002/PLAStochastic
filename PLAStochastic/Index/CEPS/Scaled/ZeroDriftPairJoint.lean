import PLAStochastic.Index.CEPS.Scaled.ZeroDriftEntranceJoint
import PLAStochastic.Index.CEPS.Scaled.TruePairScaling

/-! # The complete zero-drift pair through the joint scale-frequency origin -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogatePair_zeroDrift_holomorphic_near_joint_origin
    {m : ℕ} {η M : ℝ} (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 1 ≤ m) (N : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (min (dom.zeroDriftKernelScaleRadius 1)
      (dom.surrogateRegularScaleRadius 0 M 0 0))) :
    ∃ ε > 0, DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogatePair dom ρW N 0 x.2 x.1)
      (ball b ε ×ˢ ball 0 (ε ^ 2)) := by
  obtain ⟨ε, hε, hB, hDer⟩ := cepsScaledSurrogateBridge_zeroDrift_holomorphic_near_joint_origin
    dom hW hθ hD hf hη hM hm N hb
  obtain ⟨δ, hδ, hH⟩ := cepsScaledSurrogateEntrance_zeroDrift_holomorphic_near_joint_origin
    dom hW hθ hD hf hη hM hm N hb
  let r := min ε δ
  have hr : 0 < r := lt_min hε hδ
  have hsubε : ball b r ×ˢ ball (0 : ℂ) (r ^ 2) ⊆ ball b ε ×ˢ ball 0 (ε ^ 2) := fun x hx =>
    ⟨ball_subset_ball (min_le_left _ _) hx.1,
      ball_subset_ball (pow_le_pow_left₀ hr.le (min_le_left _ _) 2) hx.2⟩
  have hsubδ : ball b r ×ˢ ball (0 : ℂ) (r ^ 2) ⊆ ball b δ ×ˢ ball 0 (δ ^ 2) := fun x hx =>
    ⟨ball_subset_ball (min_le_right _ _) hx.1,
      ball_subset_ball (pow_le_pow_left₀ hr.le (min_le_right _ _) 2) hx.2⟩
  have hE : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp (x.1 * x.2))
      (ball b r ×ˢ ball 0 (r ^ 2)) := by fun_prop
  have hO : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      -deriv (fun z => cepsScaledSurrogateBridge dom ρW N 0 z x.1) x.2 -
        x.1 * cepsScaledSurrogateBridge dom ρW N 0 x.2 x.1)
      (ball b r ×ˢ ball 0 (r ^ 2)) :=
    (hDer.mono hsubε).neg.sub (differentiableOn_fst.mul (hB.mono hsubε))
  have h : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      exp (x.1 * x.2) * cepsScaledSurrogateEntrance dom ρW N 0 x.2 x.1 ^ 2 *
        (-deriv (fun z => cepsScaledSurrogateBridge dom ρW N 0 z x.1) x.2 -
          x.1 * cepsScaledSurrogateBridge dom ρW N 0 x.2 x.1))
      (ball b r ×ˢ ball 0 (r ^ 2)) :=
    (hE.mul ((hH.mono hsubδ).pow 2)).mul hO
  refine ⟨r, hr, ?_⟩
  simpa only [cepsScaledSurrogatePair, ofReal_zero, mul_zero, add_zero, mul_one,
    div_one, neg_mul, one_mul] using h

include hW hθ hD in
theorem cepsScaledSurrogatePair_zeroDrift_joint_frequency_jets
    {m : ℕ} {η M : ℝ} (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 1 ≤ m) (N : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (min (dom.zeroDriftKernelScaleRadius 1)
      (dom.surrogateRegularScaleRadius 0 M 0 0))) :
    ∃ ε > 0, ∀ k : ℕ, DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      iteratedDeriv k (fun z => cepsScaledSurrogatePair dom ρW N 0 z x.1) x.2)
        (ball b ε ×ˢ ball 0 (ε ^ 2)) := by
  obtain ⟨ε, hε, hP⟩ := cepsScaledSurrogatePair_zeroDrift_holomorphic_near_joint_origin
    dom hW hθ hD hf hη hM hm N hb
  have hs : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogatePair dom ρW N 0 x.1 x.2)
      (ball 0 (ε ^ 2) ×ˢ ball b ε) := hP.comp
    (f := fun x : ℂ × ℂ => (x.2, x.1)) (differentiableOn_snd.prodMk differentiableOn_fst)
      (fun _ hx => ⟨hx.2, hx.1⟩)
  refine ⟨ε, hε, fun k => ?_⟩
  have hd := differentiableOn_iteratedDeriv_fst (isOpen_ball.prod isOpen_ball) hs k
  exact hd.comp (f := fun x : ℂ × ℂ => (x.2, x.1))
    (differentiableOn_snd.prodMk differentiableOn_fst) (fun _ hx => ⟨hx.2, hx.1⟩)

theorem cepsScaledTruePair_zeroDrift_eq_surrogate (N : ℕ) (z : ℂ) (b : ℝ) :
    cepsScaledTruePair dom ρW 0 z b = cepsScaledSurrogatePair dom ρW N 0 z b := by
  have hB : (fun z => cepsScaledTrueBridge dom ρW 0 z b) =
      fun z => cepsScaledSurrogateBridge dom ρW N 0 z b := funext fun z =>
    cepsScaledTrueBridge_eq_surrogate_of_drift_zero dom ρW N 0 z (by simp)
  have hH := cepsScaledTrueEntrance_eq_surrogate_of_drift_zero dom ρW N 0 z (b := b) (by simp)
  unfold cepsScaledTruePair cepsScaledSurrogatePair
  rw [hB, hH, cepsScaledTrueBridge_eq_surrogate_of_drift_zero dom ρW N 0 z (by simp)]

end PGM
