import PLAStochastic.Index.CEPS.Scaled.SurrogateEntranceJoint
import PLAStochastic.Index.CEPS.Scaled.ZeroDriftPairJoint

/-! # Complete surrogate joint holomorphy on every real drift

The joint origin is handled by actual zero-drift even descent. Elsewhere
actual open root charts pay all moving divided differences. The frequency
jets are genuine derivatives of the complete time-operator pair.
-/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.surrogateJointScaleRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M lam : ℝ) (z : ℂ) : ℝ :=
  min (1 / (2 * (1 + |lam|)))
    (if lam = 0 ∧ z = 0 then
      min (dom.zeroDriftKernelScaleRadius 1) (dom.surrogateRegularScaleRadius 0 M 0 0)
    else min (dom.jointRootScaleRadius lam z) (dom.entranceScaleRadius N M lam z))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem surrogateJointScaleRadius_pos (N : ℕ) (M lam : ℝ) (z : ℂ) :
    0 < dom.surrogateJointScaleRadius N M lam z := by
  unfold CepsCanonDomain.surrogateJointScaleRadius
  refine lt_min (by positivity) ?_
  split_ifs
  · exact lt_min (zeroDriftKernelScaleRadius_pos dom hD (by norm_num))
      (surrogateRegularScaleRadius_pos dom hW hθ hD 0 M 0 0)
  · exact lt_min (jointRootScaleRadius_pos dom hW hθ hD lam z)
      (entranceScale_constants dom hW hθ hD N M lam z).1

include hW hθ hD in
theorem cepsScaledSurrogatePair_holomorphic_near_joint_of_nonzero {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (min (dom.jointRootScaleRadius lam z)
      (dom.entranceScaleRadius N M lam z)))
    (hbWidth : b ∈ ball (0 : ℂ) (1 / (2 * (1 + |lam|)))) :
    ∃ ε > 0, DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogatePair dom ρW N lam x.2 x.1)
      (ball b ε ×ˢ ball z ε) := by
  obtain ⟨δ, hδ, hB, hDer⟩ := cepsScaledSurrogateBridge_holomorphic_near_joint
    dom hW hθ hD hf hη hM N hN lam hz hne hb
  obtain ⟨γ, hγ, hH⟩ := cepsScaledSurrogateEntrance_holomorphic_near_joint
    dom hW hθ hD hf hη hM N hN lam hz hne hb
  have hsmall : ‖b * (lam : ℂ)‖ < 1 / 2 := by
    have ht := (lt_div_iff₀ (by positivity : 0 < 2 * (1 + |lam|))).mp
      (mem_ball_zero_iff.mp hbWidth)
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    nlinarith [norm_nonneg b]
  have hwidth : 1 + b * (lam : ℂ) ≠ 0 := by
    intro he
    have hm : b * (lam : ℂ) = -1 := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using he)
    rw [hm, norm_neg, norm_one] at hsmall
    norm_num at hsmall
  have hwcont : Continuous (fun x : ℂ × ℂ => 1 + x.1 * (lam : ℂ)) := by fun_prop
  have he := (hwcont.continuousAt (x := (b, z))).eventually_ne hwidth
  obtain ⟨α, hα, hball⟩ := Metric.eventually_nhds_iff.mp he
  let ε := min δ (min γ α)
  have hε : 0 < ε := lt_min hδ (lt_min hγ hα)
  have hsubδ : ball b ε ×ˢ ball z ε ⊆ ball b δ ×ˢ ball z δ := fun x hx =>
    ⟨ball_subset_ball (min_le_left _ _) hx.1, ball_subset_ball (min_le_left _ _) hx.2⟩
  have hsubγ : ball b ε ×ˢ ball z ε ⊆ ball b γ ×ˢ ball z γ := fun x hx =>
    ⟨ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx.1,
      ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx.2⟩
  have hwne : ∀ x ∈ ball b ε ×ˢ ball z ε, 1 + x.1 * (lam : ℂ) ≠ 0 := by
    intro x hx
    apply hball
    have hh : x ∈ ball (b, z) α := by
      rw [← ball_prod_same]
      exact ⟨ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hx.1,
        ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hx.2⟩
    exact mem_ball.mp hh
  have hw : DifferentiableOn ℂ (fun x : ℂ × ℂ => 1 + x.1 * (lam : ℂ))
      (ball b ε ×ˢ ball z ε) := by fun_prop
  have hE : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp ((x.1 * x.2) * (1 + x.1 * lam)))
      (ball b ε ×ˢ ball z ε) := by fun_prop
  have hO : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      -(1 + x.1 * (lam : ℂ))⁻¹ * deriv (fun w => cepsScaledSurrogateBridge dom ρW N lam w x.1) x.2 -
        x.1 * cepsScaledSurrogateBridge dom ρW N lam x.2 x.1) (ball b ε ×ˢ ball z ε) :=
    (((hw.inv hwne).neg.mul (hDer.mono hsubδ)).sub
      (differentiableOn_fst.mul (hB.mono hsubδ)))
  have h : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      exp ((x.1 * x.2) * (1 + x.1 * lam)) * cepsScaledSurrogateEntrance dom ρW N lam x.2 x.1 ^ 2 *
        (-(1 + x.1 * (lam : ℂ))⁻¹ * deriv (fun w => cepsScaledSurrogateBridge dom ρW N lam w x.1) x.2 -
          x.1 * cepsScaledSurrogateBridge dom ρW N lam x.2 x.1)) (ball b ε ×ˢ ball z ε) :=
    (hE.mul ((hH.mono hsubγ).pow 2)).mul hO
  refine ⟨ε, hε, ?_⟩
  simpa only [cepsScaledSurrogatePair, one_div] using h

include hW hθ hD in
theorem cepsScaledSurrogatePair_holomorphic_near_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateJointScaleRadius N M lam z)) :
    ∃ ε > 0, DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogatePair dom ρW N lam x.2 x.1)
      (ball b ε ×ˢ ball z ε) := by
  have hbW := ball_subset_ball (min_le_left _ _) hb
  have hbS := ball_subset_ball (min_le_right _ _) hb
  by_cases ho : lam = 0 ∧ z = 0
  · obtain ⟨hl, hz0⟩ := ho
    subst lam
    subst z
    simp only [and_self, ite_true] at hbS
    obtain ⟨δ, hδ, hP⟩ := cepsScaledSurrogatePair_zeroDrift_holomorphic_near_joint_origin
      dom hW hθ hD hf hη hM (by omega) N hbS
    let ε := min δ (δ ^ 2)
    have hε : 0 < ε := lt_min hδ (sq_pos_of_pos hδ)
    exact ⟨ε, hε, hP.mono (fun x hx =>
      ⟨ball_subset_ball (min_le_left _ _) hx.1, ball_subset_ball (min_le_right _ _) hx.2⟩)⟩
  · have hne : lam ≠ 0 ∨ z ≠ 0 := by tauto
    simp only [ho, ite_false] at hbS
    exact cepsScaledSurrogatePair_holomorphic_near_joint_of_nonzero dom hW hθ hD hf hη hM N hN
      lam hz hne hbS hbW

include hW hθ hD in
theorem cepsScaledSurrogatePair_joint_frequency_jets {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateJointScaleRadius N M lam z)) :
    ∃ ε > 0, ∀ k : ℕ, DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      iteratedDeriv k (fun w => cepsScaledSurrogatePair dom ρW N lam w x.1) x.2)
      (ball b ε ×ˢ ball z ε) := by
  obtain ⟨ε, hε, hP⟩ := cepsScaledSurrogatePair_holomorphic_near_joint
    dom hW hθ hD hf hη hM N hN lam hz hb
  have hs : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogatePair dom ρW N lam x.1 x.2)
      (ball z ε ×ˢ ball b ε) := hP.comp (f := fun x : ℂ × ℂ => (x.2, x.1))
        (differentiableOn_snd.prodMk differentiableOn_fst) (fun x hx => ⟨hx.2, hx.1⟩)
  refine ⟨ε, hε, fun k => ?_⟩
  exact (differentiableOn_iteratedDeriv_fst (isOpen_ball.prod isOpen_ball) hs k).comp
    (f := fun x : ℂ × ℂ => (x.2, x.1)) (differentiableOn_snd.prodMk differentiableOn_fst)
      (fun x hx => ⟨hx.2, hx.1⟩)

end PGM
