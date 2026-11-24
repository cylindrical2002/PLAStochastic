import PLAStochastic.Index.CEPS.Normal.MovingHolomorphicSlope
import PLAStochastic.Index.CEPS.Normal.MergedNonzero

/-! # Local normal forms from joint complex differentiability

The factor remains abstract. Actual joint complex differentiability of `Q` and `L`,
analytic moving roots and marker, and a strict large-width logarithmic
derivative budget provide a neighborhood on which both regular normal
forms are holomorphic. No divided-difference nonvanishing is assumed.
-/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

set_option maxHeartbeats 800000 in
theorem cepsNormal_holomorphic_near_merged_of_differentiable
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} {A : ℂ → CepsNormalData}
    {L : ℂ → ℂ → ℂ → ℂ} {μ : ℂ} {q t : ℂ → ℂ} {l M : ℝ}
    (hQ : DifferentiableOn ℂ (fun x : ℂ × ℂ => (A x.1).Q x.2) (U ×ˢ ball 0 R))
    (hL : DifferentiableOn ℂ (fun x : ℂ × ℂ => L μ (q x.1) x.2) (U ×ˢ ball 0 R))
    (hbp : DifferentiableOn ℂ (fun r => (A r).βp) U)
    (hbm : DifferentiableOn ℂ (fun r => (A r).βm) U)
    (ht : DifferentiableOn ℂ t U)
    (hbpmap : MapsTo (fun r => (A r).βp) U (ball 0 R))
    (hbmmap : MapsTo (fun r => (A r).βm) U (ball 0 R))
    (htmap : MapsTo t U (ball 0 R))
    {r₀ Q' L' : ℂ} (hr₀ : r₀ ∈ U) (hroots : (A r₀).βp = (A r₀).βm)
    (hQ' : HasDerivAt (A r₀).Q Q' (A r₀).βm)
    (hL' : HasDerivAt (L μ (q r₀)) L' (A r₀).βm)
    (hQm0 : (A r₀).Q (A r₀).βm ≠ 0) (hQt0 : (A r₀).Q (t r₀) ≠ 0)
    (hbudget : ‖Q' / (A r₀).Q (A r₀).βm - 2 * L'‖ ≤ M) (hl : M < l) :
    ∃ ε > 0,
      DifferentiableOn ℂ (fun r => (A r).regularEntrance L μ (q r) l (t r)) (ball r₀ ε) ∧
      DifferentiableOn ℂ (fun r => (A r).regularBridge L μ (q r) l) (ball r₀ ε) := by
  let G : ℂ → ℂ → ℂ := fun r ζ => (A r).normalG L μ (q r) l ζ
  have hE : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp (-x.2 * (l : ℂ)))
      (U ×ˢ ball 0 R) :=
    (differentiableOn_snd.neg.mul (differentiableOn_const (l : ℂ))).cexp
  have hEL : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp (-2 * L μ (q x.1) x.2))
      (U ×ˢ ball 0 R) :=
    ((differentiableOn_const (-2 : ℂ)).mul hL).cexp
  have hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2) (U ×ˢ ball 0 R) :=
    (hE.mul hQ).mul hEL
  let S : ℂ → ℂ := fun r => dslope (G r) (A r).βm (A r).βp
  let N : ℂ → ℂ := fun r => dslope (dslope (G r) (A r).βm) (A r).βp (t r)
  have hSJ := cepsNormal_joint_moving_dslope_of_differentiable (G := G)
    (a := fun r => (A r).βm) hU hG hbm hbmmap
  have hS : DifferentiableOn ℂ S U :=
    hSJ.comp (f := fun r => (r, (A r).βp))
      (differentiableOn_id.prodMk hbp) (fun _ hr => ⟨hr, hbpmap hr⟩)
  have hNJ := cepsNormal_joint_moving_second_dslope_of_differentiable (G := G)
    (a := fun r => (A r).βm) (b := fun r => (A r).βp) hU hG hbm hbp hbmmap hbpmap
  have hN : DifferentiableOn ℂ N U :=
    hNJ.comp (f := fun r => (r, t r)) (differentiableOn_id.prodMk ht)
      (fun _ hr => ⟨hr, htmap hr⟩)
  have hpT : DifferentiableOn ℂ (fun r => (r, t r)) U := differentiableOn_id.prodMk ht
  have hQT : DifferentiableOn ℂ (fun r => (A r).Q (t r)) U :=
    hQ.comp (f := fun r => (r, t r)) hpT (fun r hr => ⟨hr, htmap hr⟩)
  have hLT : DifferentiableOn ℂ (fun r => L μ (q r) (t r)) U :=
    hL.comp (f := fun r => (r, t r)) hpT (fun r hr => ⟨hr, htmap hr⟩)
  have hGP : DifferentiableOn ℂ (fun r => G r (A r).βp) U :=
    hG.comp (f := fun r => (r, (A r).βp)) (differentiableOn_id.prodMk hbp)
      (fun r hr => ⟨hr, hbpmap hr⟩)
  have hGM : DifferentiableOn ℂ (fun r => G r (A r).βm) U :=
    hG.comp (f := fun r => (r, (A r).βm)) (differentiableOn_id.prodMk hbm)
      (fun r hr => ⟨hr, hbmmap hr⟩)
  have hS0 : S r₀ ≠ 0 :=
    (A r₀).normalG_merged_dslope_ne L μ (q r₀) hroots hQ' hL' hQm0 hbudget hl
  have hSe : ∀ᶠ r in 𝓝 r₀, S r ≠ 0 :=
    ((hS r₀ hr₀).differentiableAt (hU.mem_nhds hr₀)).continuousAt.eventually_ne hS0
  have hQe : ∀ᶠ r in 𝓝 r₀, (A r).Q (t r) ≠ 0 :=
    ((hQT r₀ hr₀).differentiableAt (hU.mem_nhds hr₀)).continuousAt.eventually_ne hQt0
  have hUe : ∀ᶠ r in 𝓝 r₀, r ∈ U := hU.mem_nhds hr₀
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff_ball.mp
    (hUe.and (hSe.and hQe))
  have hsub : ball r₀ ε ⊆ U := fun r hr => (he r hr).1
  have hSne : ∀ r ∈ ball r₀ ε, S r ≠ 0 := fun r hr => (he r hr).2.1
  have hQne : ∀ r ∈ ball r₀ ε, (A r).Q (t r) ≠ 0 := fun r hr => (he r hr).2.2
  refine ⟨ε, hε, ?_, ?_⟩
  · change DifferentiableOn ℂ (fun r => -exp (L μ (q r) (t r)) * N r /
      ((A r).Q (t r) * S r)) (ball r₀ ε)
    exact ((hLT.cexp.neg.mul hN).mono hsub).div ((hQT.mul hS).mono hsub)
      (fun r hr => mul_ne_zero (hQne r hr) (hSne r hr))
  · change DifferentiableOn ℂ (fun r => -G r (A r).βp * G r (A r).βm / S r) (ball r₀ ε)
    exact ((hGP.neg.mul hGM).mono hsub).div (hS.mono hsub) hSne

end PGM
