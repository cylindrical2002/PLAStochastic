import PLAStochastic.Index.CEPS.Scaled.EntranceScaleCurve
import PLAStochastic.Index.CEPS.Normal.MovingHolomorphicSlope

/-! # Joint scale and spatial holomorphy of the actual-root surrogate weight -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateG_differentiableOn_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateG dom ρW N lam z x.1 x.2)
      (ball 0 (dom.entranceScaleRadius N M lam z) ×ˢ ball 0 (dom.entranceSpatialScaleRadius lam z)) := by
  let U : Set ℂ := ball 0 (dom.entranceScaleRadius N M lam z)
  let V : Set ℂ := ball 0 (dom.entranceSpatialScaleRadius lam z)
  have hbase : ∀ x ∈ U ×ˢ V, x.1 ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) ∧
      ‖x.1 * x.2‖ < dom.c₀ / 2 :=
    fun x hx => entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam hx.1 hx.2
  have hmapQ : MapsTo (fun x : ℂ × ℂ => (x.1, x.1 * x.2)) (U ×ˢ V)
      (ball 0 (dom.canonScaleRadius lam z) ×ˢ ball 0 dom.ρA) := by
    intro x hx
    obtain ⟨hb, hξ⟩ := hbase x hx
    refine ⟨hb, mem_ball_zero_iff.mpr ?_⟩
    have := dom.c₀_le
    have := dom.ρA_pos
    linarith
  have hQc := (cepsScaledQuotient_differentiableOn dom hW hθ hD lam hz).comp
    (differentiableOn_fst.prodMk (differentiableOn_fst.mul differentiableOn_snd)) hmapQ
  have hQ : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      cepsQ D θ ρW (x.1 * lam) (cepsComplexScaledDiscount lam z x.1) (x.1 * x.2)) (U ×ˢ V) := by
    apply hQc.congr
    intro x hx
    exact (cepsScaledQuotient_eq_actual dom hW hθ hD lam hz (hbase x hx).1 (x.1 * x.2)).symm
  have hcurve : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      (x.1 * (lam : ℂ), (cepsComplexScaledDiscount lam z x.1, x.1 * x.2))) (U ×ˢ V) := by
    unfold cepsComplexScaledDiscount
    fun_prop
  have hmapL : MapsTo (fun x : ℂ × ℂ =>
      (x.1 * (lam : ℂ), (cepsComplexScaledDiscount lam z x.1, x.1 * x.2))) (U ×ˢ V)
      {x : ℂ × (ℂ × ℂ) | x.2.2.re < dom.c₀ ∧ ‖x.2.1‖ < dom.q₀ / 2} := by
    intro x hx
    obtain ⟨hb, hξ⟩ := hbase x hx
    have hq := (canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hb).2.1
    exact ⟨(re_le_norm _).trans_lt (hξ.trans (by linarith [dom.c₀_pos])), hq⟩
  have hLc := (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp hcurve hmapL
  have hL : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      cepsCanonDriftTaylor dom ρW N (x.1 * lam) (cepsComplexScaledDiscount lam z x.1) (x.1 * x.2)) (U ×ˢ V) := by
    simpa only [Function.comp_apply] using! hLc
  have hE : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp (-x.2 * (1 + x.1 * lam))) (U ×ˢ V) := by
    fun_prop
  exact hE.mul (hQ.mul ((hL.const_mul (-2)).cexp))

include hW hθ hD in
theorem cepsScaledSurrogateG_second_dslope_differentiableOn_joint {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      dslope (dslope (cepsScaledSurrogateG dom ρW N lam z x.1)
        (cepsScaledSignedRoot D θ ρW lam z (-1) x.1))
          (cepsScaledSignedRoot D θ ρW lam z 1 x.1) x.2)
      (ball 0 (dom.entranceScaleRadius N M lam z) ×ˢ ball 0 (dom.entranceSpatialScaleRadius lam z)) := by
  have hsub : ball (0 : ℂ) (dom.entranceScaleRadius N M lam z) ⊆
      ball 0 (dom.actualRootScaleRadius lam z) :=
    ball_subset_ball ((min_le_right _ _).trans
      ((div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num)).trans (min_le_left _ _)))
  have hp := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1)).1.mono hsub
  have hm := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)).1.mono hsub
  have hpmap := fun b hb => entranceScaleCurve_roots_mem dom hW hθ hD N M lam hz (by norm_num : ‖(1 : ℂ)‖ ≤ 1) (b := b) hb
  have hmmap := fun b hb => entranceScaleCurve_roots_mem dom hW hθ hD N M lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) (b := b) hb
  exact cepsNormal_joint_moving_second_dslope_of_differentiable isOpen_ball
    (cepsScaledSurrogateG_differentiableOn_joint dom hW hθ hD hf hη N hN lam hz) hm hp hmmap hpmap

end PGM
