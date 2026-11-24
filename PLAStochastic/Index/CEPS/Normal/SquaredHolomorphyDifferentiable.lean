import PLAStochastic.Index.CEPS.Normal.HolomorphyDifferentiable
import PLAStochastic.Index.CEPS.Normal.RegularEven

/-! # Squared-coordinate extensions paid by abstract factor budgets -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

set_option maxHeartbeats 400000 in
theorem cepsNormal_holomorphic_in_square_near_merged_of_differentiable
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
    (hA : ∀ r ∈ U, A (-r) = (A r).swapRoots)
    (hqe : ∀ r ∈ U, q (-r) = q r) (hte : ∀ r ∈ U, t (-r) = t r)
    {Q' L' : ℂ} (h0 : (0 : ℂ) ∈ U) (hroots : (A 0).βp = (A 0).βm)
    (hQ' : HasDerivAt (A 0).Q Q' (A 0).βm)
    (hL' : HasDerivAt (L μ (q 0)) L' (A 0).βm)
    (hQm0 : (A 0).Q (A 0).βm ≠ 0) (hQt0 : (A 0).Q (t 0) ≠ 0)
    (hbudget : ‖Q' / (A 0).Q (A 0).βm - 2 * L'‖ ≤ M) (hl : M < l) :
    ∃ ε > 0,
      DifferentiableOn ℂ
        (fun z => (A (sqrt z)).regularEntrance L μ (q (sqrt z)) l (t (sqrt z)))
        (ball 0 (ε ^ 2)) ∧
      DifferentiableOn ℂ (fun z => (A (sqrt z)).regularBridge L μ (q (sqrt z)) l)
        (ball 0 (ε ^ 2)) := by
  obtain ⟨ε, hε, hE, hB⟩ := cepsNormal_holomorphic_near_merged_of_differentiable
    (A := A) (L := L) (μ := μ) (q := q) (t := t) (l := l) (M := M)
    hU hQ hL hbp hbm ht hbpmap hbmmap htmap h0 hroots hQ' hL' hQm0 hQt0 hbudget hl
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let ε' := min ε δ
  have hε' : 0 < ε' := lt_min hε hδ
  have hsub : ball (0 : ℂ) ε' ⊆ U :=
    (ball_subset_ball (min_le_right ε δ)).trans hδU
  have hsubε : ball (0 : ℂ) ε' ⊆ ball 0 ε := ball_subset_ball (min_le_left ε δ)
  have hE' := hE.mono hsubε
  have hB' := hB.mono hsubε
  have hEexp : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp (-x.2 * (l : ℂ)))
      (U ×ˢ ball 0 R) :=
    (differentiableOn_snd.neg.mul (differentiableOn_const (l : ℂ))).cexp
  have hELexp : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp (-2 * L μ (q x.1) x.2))
      (U ×ˢ ball 0 R) :=
    ((differentiableOn_const (-2 : ℂ)).mul hL).cexp
  have hG : DifferentiableOn ℂ (fun x : ℂ × ℂ => (A x.1).normalG L μ (q x.1) l x.2)
      (U ×ˢ ball 0 R) := (hEexp.mul hQ).mul hELexp
  have hGr : ∀ r ∈ ball (0 : ℂ) ε',
      DifferentiableAt ℂ ((A r).normalG L μ (q r) l) (A r).βp ∧
      DifferentiableAt ℂ ((A r).normalG L μ (q r) l) (A r).βm := by
    intro r hr
    have hrU := hsub hr
    exact ⟨differentiableAt_slice_snd (hU.prod isOpen_ball) hG
        (show (r, (A r).βp) ∈ U ×ˢ ball 0 R from ⟨hrU, hbpmap hrU⟩),
      differentiableAt_slice_snd (hU.prod isOpen_ball) hG
        (show (r, (A r).βm) ∈ U ×ˢ ball 0 R from ⟨hrU, hbmmap hrU⟩)⟩
  exact ⟨ε', hε', cepsNormal_regular_forms_squared hε'
    (fun r hr => hA r (hsub hr)) (fun r hr => hqe r (hsub hr))
    (fun r hr => hte r (hsub hr)) hGr hE' hB'⟩

end PGM
