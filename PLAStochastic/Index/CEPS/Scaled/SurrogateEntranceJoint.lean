import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeJoint
import PLAStochastic.Index.CEPS.Scaled.SurrogateEntrance

/-! # Joint scale-frequency holomorphy of the complete surrogate entrance -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

set_option maxHeartbeats 800000 in
include hW hθ hD in
theorem cepsScaledSurrogateEntrance_holomorphic_near_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (min (dom.jointRootScaleRadius lam z)
      (dom.entranceScaleRadius N M lam z))) :
    ∃ ε > 0, DifferentiableOn ℂ
      (fun x : ℂ × ℂ => cepsScaledSurrogateEntrance dom ρW N lam x.2 x.1)
        (ball b ε ×ˢ ball z ε) := by
  obtain ⟨δ, hδ, hroots, hbounds⟩ := cepsScaled_joint_root_chart dom hW hθ hD N M lam hz hne hb
  let S := dom.entranceSpatialScaleRadius lam z
  have hp := hroots 1 (by norm_num)
  have hm := hroots (-1) (by norm_num)
  have hgbounds : ∀ x ∈ ball b δ ×ˢ ball z δ,
      ‖x.1 * (lam : ℂ)‖ < dom.μ₀ ∧
      ‖x.1 * cepsScaledRootCoordinate D θ ρW lam x.2 x.1‖ < dom.rmax ∧
      ‖cepsComplexScaledDiscount lam x.2 x.1‖ < dom.q₀ / 2 ∧ ‖x.1‖ * S < dom.c₀ / 2 ∧
      cepsScaledSignedRoot D θ ρW lam x.2 1 x.1 ∈ ball 0 S ∧
      cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1 ∈ ball 0 S := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hbounds x hx
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨hcG, hG₁, hG₂⟩ := cepsScaledSurrogateG_joint_on_root_chart dom hW hθ hD hf hη N hN lam
    isOpen_ball isOpen_ball hp hm hgbounds
  have hpmap : MapsTo (fun x : ℂ × ℂ => cepsScaledSignedRoot D θ ρW lam x.2 1 x.1)
      (ball b δ ×ˢ ball z δ) (ball 0 S) := fun x hx => (hbounds x hx).2.2.2.2.1
  have hmmap : MapsTo (fun x : ℂ × ℂ => cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1)
      (ball b δ ×ˢ ball z δ) (ball 0 S) := fun x hx => (hbounds x hx).2.2.2.2.2.1
  have htmap : MapsTo (fun x : ℂ × ℂ => x.1 * x.2)
      (ball b δ ×ˢ ball z δ) (ball 0 S) := fun x hx => (hbounds x hx).2.2.2.2.2.2
  have hd : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateDenominator dom ρW N lam x.2 x.1)
      (ball b δ ×ˢ ball z δ) :=
    cepsNormal_differentiableOn_two_parameter_moving_dslope
      (G := fun x ξ => cepsScaledSurrogateG dom ρW N lam x.2 x.1 ξ)
      (a := fun x => cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1)
      (b := fun x => cepsScaledSignedRoot D θ ρW lam x.2 1 x.1)
      isOpen_ball isOpen_ball hcG hG₁ hG₂ hm hp hmmap hpmap
  have hn : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      dslope (dslope (cepsScaledSurrogateG dom ρW N lam x.2 x.1)
        (cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1))
        (cepsScaledSignedRoot D θ ρW lam x.2 1 x.1) (x.1 * x.2))
      (ball b δ ×ˢ ball z δ) :=
    cepsNormal_differentiableOn_two_parameter_moving_second_dslope
      (G := fun x ξ => cepsScaledSurrogateG dom ρW N lam x.2 x.1 ξ)
      (a := fun x => cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1)
      (b := fun x => cepsScaledSignedRoot D θ ρW lam x.2 1 x.1)
      (c := fun x => x.1 * x.2)
      isOpen_ball isOpen_ball hcG hG₁ hG₂ hm hp (by fun_prop) hmmap hpmap htmap
  have hphys : ∀ x ∈ ball b δ ×ˢ ball z δ, ∀ ξ ∈ ball (0 : ℂ) S,
      x.1 * ξ ∈ ball (0 : ℂ) dom.ρA := by
    intro x hx ξ hξ
    have ht := (hbounds x hx).2.2.2.1
    have hξn := (mem_ball_zero_iff.mp hξ).le
    have hn := (mul_le_mul_of_nonneg_left hξn (norm_nonneg x.1)).trans_lt ht
    apply mem_ball_zero_iff.mpr
    rw [norm_mul]
    have := dom.c₀_le
    have := dom.ρA_pos
    linarith
  have hpc := differentiableOn_fst.mul hp
  have hmc := differentiableOn_fst.mul hm
  have hpPhysMap : MapsTo (fun x : ℂ × ℂ => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 1 x.1)
      (ball b δ ×ˢ ball z δ) (ball 0 dom.ρA) := fun x hx => hphys x hx _ (hpmap hx)
  have hmPhysMap : MapsTo (fun x : ℂ × ℂ => x.1 * cepsScaledSignedRoot D θ ρW lam x.2 (-1) x.1)
      (ball b δ ×ˢ ball z δ) (ball 0 dom.ρA) := fun x hx => hphys x hx _ (hmmap hx)
  have hcQ := cepsScaledQuotient_continuousOn_joint_on_root_chart dom hW hθ hD lam
    (isOpen_ball.prod isOpen_ball) hpc hmc hpPhysMap hmPhysMap
  obtain ⟨hQ₁, hQ₂⟩ := cepsScaledQuotient_holomorphic_slices_on_root_chart dom hW hθ hD lam
    isOpen_ball isOpen_ball hpc hmc hpPhysMap hmPhysMap
  have hmarkMap : MapsTo (fun x : ℂ × ℂ => x.1 ^ 2 * x.2)
      (ball b δ ×ˢ ball z δ) (ball 0 dom.ρA) := by
    intro x hx
    simpa only [pow_two, mul_assoc] using hphys x hx (x.1 * x.2) (htmap hx)
  have hQraw := cepsNormal_differentiableOn_two_parameter_eval
    (G := fun x ξ => cepsScaledQuotient D θ ρW lam x.2 x.1 ξ)
    (a := fun x => x.1 ^ 2 * x.2)
    isOpen_ball isOpen_ball hcQ hQ₁ hQ₂ (by fun_prop) hmarkMap
  have hQ : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      cepsQ D θ ρW (x.1 * lam) (cepsComplexScaledDiscount lam x.2 x.1) (x.1 ^ 2 * x.2))
      (ball b δ ×ˢ ball z δ) := hQraw.congr fun x hx =>
    (cepsScaledQuotient_eq_actual_of_morse_bounds dom hW hθ hD lam x.2 x.1 (x.1 ^ 2 * x.2)
      (hbounds x hx).1.le (hbounds x hx).2.1).symm
  have hQnon : ∀ x ∈ ball b δ ×ˢ ball z δ,
      cepsQ D θ ρW (x.1 * lam) (cepsComplexScaledDiscount lam x.2 x.1) (x.1 ^ 2 * x.2) ≠ 0 := by
    intro x hx
    exact norm_pos_iff.mp ((div_pos (cepsVarLo_pos hD) (by norm_num)).trans_le
      (cepsQ_norm_ge_on_rootZone dom hW hθ hD (hbounds x hx).1.le
        ((hbounds x hx).2.2.1.le.trans (half_le_self dom.q₀_pos.le))
        (mem_ball_zero_iff.mp (hmarkMap hx))))
  have hL : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonDriftTaylor dom ρW N (x.1 * lam)
      (cepsComplexScaledDiscount lam x.2 x.1) (x.1 ^ 2 * x.2)) (ball b δ ×ˢ ball z δ) := by
    apply (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp
      (f := fun x : ℂ × ℂ => (x.1 * (lam : ℂ), (cepsComplexScaledDiscount lam x.2 x.1, x.1 ^ 2 * x.2))) ?_ ?_
    · unfold cepsComplexScaledDiscount
      fun_prop
    · intro x hx
      have ht := (hbounds x hx).2.2.2.1
      have hn := (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp (htmap hx)).le
        (norm_nonneg x.1)).trans_lt ht
      have hzmark : ‖x.1 ^ 2 * x.2‖ < dom.c₀ / 2 := by
        simpa only [pow_two, mul_assoc, norm_mul] using hn
      exact ⟨(re_le_norm _).trans_lt (hzmark.trans (half_lt_self dom.c₀_pos)), (hbounds x hx).2.2.1⟩
  have hbS := ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_right _ _) hb)
  have hneD := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz hbS
  have hx : (b, z) ∈ ball b δ ×ˢ ball z δ := ⟨mem_ball_self hδ, mem_ball_self hδ⟩
  have he := (hd.continuousOn.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds hx)).eventually_ne hneD
  obtain ⟨γ, hγ, hball⟩ := Metric.eventually_nhds_iff.mp he
  let ε := min δ γ
  have hε : 0 < ε := lt_min hδ hγ
  have hsub : ball b ε ×ˢ ball z ε ⊆ ball b δ ×ˢ ball z δ := fun x hx =>
    ⟨ball_subset_ball (min_le_left _ _) hx.1, ball_subset_ball (min_le_left _ _) hx.2⟩
  have hnon : ∀ x ∈ ball b ε ×ˢ ball z ε,
      cepsQ D θ ρW (x.1 * lam) (cepsComplexScaledDiscount lam x.2 x.1) (x.1 ^ 2 * x.2) *
        cepsScaledSurrogateDenominator dom ρW N lam x.2 x.1 ≠ 0 := by
    intro x hx
    apply mul_ne_zero (hQnon x (hsub hx))
    apply hball
    have hh : x ∈ ball (b, z) γ := by
      rw [← ball_prod_same]
      exact ⟨ball_subset_ball (min_le_right _ _) hx.1, ball_subset_ball (min_le_right _ _) hx.2⟩
    exact mem_ball.mp hh
  refine ⟨ε, hε, ?_⟩
  exact ((hL.mono hsub).cexp.neg.mul (hn.mono hsub)).mul
    (((hQ.mono hsub).mul (hd.mono hsub)).inv hnon)

end PGM
