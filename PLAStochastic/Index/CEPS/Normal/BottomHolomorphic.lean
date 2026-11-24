import PLAStochastic.Index.CEPS.Normal.ActualSignedFactors
import PLAStochastic.Index.CEPS.Normal.InverseRelativeDerivative
import PLAStochastic.Index.CEPS.Normal.RegularEven

/-! # Holomorphic lower-end normal entrance from actual reciprocal weights -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

namespace CepsNormalData

theorem regularBottomEntrance_swap (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q l : ℂ)
    (hp : DifferentiableAt ℂ (a.normalK L μ q l) a.βp)
    (hm : DifferentiableAt ℂ (a.normalK L μ q l) a.βm) :
    a.swapRoots.regularBottomEntrance L μ q l = a.regularBottomEntrance L μ q l := by
  unfold regularBottomEntrance
  change exp (-L μ q 0) * dslope (dslope (a.normalK L μ q l) a.βp) a.βm 0 /
    dslope (a.normalK L μ q l) a.βp a.βm = _
  rw [cepsNormal_dslope_swap (a.normalK L μ q l) a.βp a.βm,
    ← cepsNormal_second_dslope_swap hp hm 0]

end CepsNormalData

set_option maxHeartbeats 800000 in
theorem cepsNormal_bottom_holomorphic_near
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} {A : ℂ → CepsNormalData}
    {L : ℂ → ℂ → ℂ → ℂ} {μ : ℂ} {q : ℂ → ℂ} {l : ℂ}
    (hK : DifferentiableOn ℂ (fun x : ℂ × ℂ => (A x.1).normalK L μ (q x.1) l x.2)
      (U ×ˢ ball 0 R))
    (hL : DifferentiableOn ℂ (fun x : ℂ × ℂ => L μ (q x.1) x.2) (U ×ˢ ball 0 R))
    (hbp : DifferentiableOn ℂ (fun r => (A r).βp) U)
    (hbm : DifferentiableOn ℂ (fun r => (A r).βm) U)
    (hbpmap : MapsTo (fun r => (A r).βp) U (ball 0 R))
    (hbmmap : MapsTo (fun r => (A r).βm) U (ball 0 R))
    (hR : 0 < R) {r₀ : ℂ} (hr₀ : r₀ ∈ U)
    (hS0 : dslope ((A r₀).normalK L μ (q r₀) l) (A r₀).βm (A r₀).βp ≠ 0) :
    ∃ ε > 0, ball r₀ ε ⊆ U ∧
      DifferentiableOn ℂ (fun r => (A r).regularBottomEntrance L μ (q r) l) (ball r₀ ε) := by
  let K := fun r ζ => (A r).normalK L μ (q r) l ζ
  let S := fun r => dslope (K r) (A r).βm (A r).βp
  let N := fun r => dslope (dslope (K r) (A r).βm) (A r).βp 0
  have hSJ := cepsNormal_joint_moving_dslope_of_differentiable (G := K)
    (a := fun r => (A r).βm) hU hK hbm hbmmap
  have hS : DifferentiableOn ℂ S U := hSJ.comp (f := fun r => (r, (A r).βp))
    (differentiableOn_id.prodMk hbp) (fun _ hr => ⟨hr, hbpmap hr⟩)
  have hNJ := cepsNormal_joint_moving_second_dslope_of_differentiable (G := K)
    (a := fun r => (A r).βm) (b := fun r => (A r).βp) hU hK hbm hbp hbmmap hbpmap
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hN : DifferentiableOn ℂ N U := hNJ.comp (f := fun r : ℂ => (r, (0 : ℂ)))
    (differentiableOn_id.prodMk (differentiableOn_const 0)) (fun _ hr => ⟨hr, h0⟩)
  have hL0 : DifferentiableOn ℂ (fun r => L μ (q r) 0) U := hL.comp
    (f := fun r : ℂ => (r, (0 : ℂ)))
    (differentiableOn_id.prodMk (differentiableOn_const 0)) (fun _ hr => ⟨hr, h0⟩)
  have hSe : ∀ᶠ r in 𝓝 r₀, S r ≠ 0 :=
    ((hS r₀ hr₀).differentiableAt (hU.mem_nhds hr₀)).continuousAt.eventually_ne hS0
  have hUe : ∀ᶠ r in 𝓝 r₀, r ∈ U := hU.mem_nhds hr₀
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff_ball.mp (hUe.and hSe)
  have hsub : ball r₀ ε ⊆ U := fun r hr => (he r hr).1
  refine ⟨ε, hε, hsub, ?_⟩
  exact (((hL0.mono hsub).neg.cexp).mul (hN.mono hsub)).div (hS.mono hsub)
    (fun r hr => (he r hr).2)

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMorseNormalData_normalK_differentiableOn_full {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    (l : ℂ) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      (cepsMorseNormalData D θ ρW μ x.1).normalK (dom.canonL ρW) μ
        (cepsMorseDiscount D θ ρW μ x.1) l x.2)
      (dom.normalMorseSet ρW μ ×ˢ ball 0 (dom.c₀ / 2)) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  refine (cepsMorseNormalData_normalG_differentiableOn_full dom hW hθ hD hμ l).inv ?_
  intro x hx
  have hzA : x.2 ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := mem_ball_zero_iff.mp hx.2; have := dom.c₀_le; have := dom.ρA_pos; linarith)
  exact (cepsMorseNormalData D θ ρW μ x.1).normalG_ne (dom.canonL ρW) μ
    (cepsMorseDiscount D θ ρW μ x.1) l
    (CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hx.1.2.le hzA)

include hW hθ hD in
theorem cepsMorseNormalData_bottom_holomorphic_near_of_dslope_ne {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {r : ℂ} (hr : r ∈ dom.normalMorseSet ρW μ) {l : ℝ}
    (hS : dslope ((cepsMorseNormalData D θ ρW μ r).normalG (dom.canonL ρW) μ
      (cepsMorseDiscount D θ ρW μ r) l)
        (cepsMorseNormalData D θ ρW μ r).βm (cepsMorseNormalData D θ ρW μ r).βp ≠ 0) :
    ∃ ε > 0, ball r ε ⊆ dom.normalMorseSet ρW μ ∧
      DifferentiableOn ℂ (fun r' => (cepsMorseNormalData D θ ρW μ r').regularBottomEntrance
        (dom.canonL ρW) μ (cepsMorseDiscount D θ ρW μ r') l) (ball r ε) := by
  let U := dom.normalMorseSet ρW (μ : ℂ)
  let A := cepsMorseNormalData D θ ρW (μ : ℂ)
  let q := cepsMorseDiscount D θ ρW (μ : ℂ)
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hU := cepsNormal_morseSet_open (ρW := ρW) dom (μ : ℂ)
  have hΘ := cepsMorseRoot_differentiableOn_r dom hW hθ hD hμ'
  have hbp : DifferentiableOn ℂ (fun r => (A r).βp) U := hΘ.mono inter_subset_left
  have hbm : DifferentiableOn ℂ (fun r => (A r).βm) U := by
    exact (hΘ.comp (f := fun r : ℂ => -r) differentiableOn_id.neg
      (fun r hr => mem_ball_zero_iff.mpr (by simpa using mem_ball_zero_iff.mp hr))).mono
        inter_subset_left
  obtain ⟨hbpmap, hbmmap⟩ := cepsMorseNormalData_root_maps_full dom hW hθ hD hμ
  have hG := cepsMorseNormalData_normalG_differentiableOn_full dom hW hθ hD hμ (l : ℂ)
  have hSm : (A r).βm ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have hn := mem_ball_zero_iff.mp (hbmmap hr); have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hSp : (A r).βp ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have hn := mem_ball_zero_iff.mp (hbpmap hr); have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hm := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hr.2.le hSm
  have hp := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hr.2.le hSp
  have hs := (A r).normalK_dslope (dom.canonL ρW) μ (q r) l
    (differentiableAt_slice_snd (hU.prod isOpen_ball) hG ⟨hr, hbmmap hr⟩) hm hp
  have hSK : dslope ((A r).normalK (dom.canonL ρW) μ (q r) l) (A r).βm (A r).βp ≠ 0 := by
    rw [hs]
    exact div_ne_zero (neg_ne_zero.mpr hS)
      (mul_ne_zero ((A r).normalG_ne (dom.canonL ρW) μ (q r) l hm)
        ((A r).normalG_ne (dom.canonL ρW) μ (q r) l hp))
  exact cepsNormal_bottom_holomorphic_near hU
    (cepsMorseNormalData_normalK_differentiableOn_full dom hW hθ hD hμ l)
    (cepsMorse_canonL_differentiableOn_full dom hW hθ hD hμ)
    hbp hbm hbpmap hbmmap (by linarith [dom.c₀_pos]) hr hSK

end PGM
