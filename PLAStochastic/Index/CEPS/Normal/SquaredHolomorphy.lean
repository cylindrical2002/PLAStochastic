import PLAStochastic.Index.CEPS.Normal.Holomorphy
import PLAStochastic.Index.CEPS.Normal.RegularEven

/-! # Squared-coordinate extensions paid by abstract factor budgets -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

set_option maxHeartbeats 400000 in
theorem cepsNormal_holomorphic_in_square_near_merged
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} {A : ℂ → CepsNormalData}
    {L : ℂ → ℂ → ℂ → ℂ} {μ : ℂ} {q t : ℂ → ℂ} {l M : ℝ}
    (hQ : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => (A x.1).Q x.2) (U ×ˢ ball 0 R))
    (hL : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => L μ (q x.1) x.2) (U ×ˢ ball 0 R))
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
  obtain ⟨ε, hε, hE, hB⟩ := cepsNormal_holomorphic_near_merged
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
  have hEexp : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => exp (-x.2 * (l : ℂ)))
      (U ×ˢ ball 0 R) :=
    (analyticOnNhd_snd.neg.mul (analyticOnNhd_const (v := (l : ℂ)))).cexp
  have hELexp : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => exp (-2 * L μ (q x.1) x.2))
      (U ×ˢ ball 0 R) :=
    ((analyticOnNhd_const (v := (-2 : ℂ))).mul hL).cexp
  have hG : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => (A x.1).normalG L μ (q x.1) l x.2)
      (U ×ˢ ball 0 R) := (hEexp.mul hQ).mul hELexp
  have hGr : ∀ r ∈ ball (0 : ℂ) ε',
      DifferentiableAt ℂ ((A r).normalG L μ (q r) l) (A r).βp ∧
      DifferentiableAt ℂ ((A r).normalG L μ (q r) l) (A r).βm := by
    intro r hr
    have hrU := hsub hr
    exact ⟨(hG (r, (A r).βp) ⟨hrU, hbpmap hrU⟩).curry_right.differentiableAt,
      (hG (r, (A r).βm) ⟨hrU, hbmmap hrU⟩).curry_right.differentiableAt⟩
  exact ⟨ε', hε', cepsNormal_regular_forms_squared hε'
    (fun r hr => hA r (hsub hr)) (fun r hr => hqe r (hsub hr))
    (fun r hr => hte r (hsub hr)) hGr hE' hB'⟩

/-- Once the two regular forms descend, their discount-derivative pair is
holomorphic too. This is the pair in the squared Morse coordinate; an actual
Morse instantiation identifies that coordinate with `q - m(μ)`.
-/
theorem cepsNormal_holomorphic_descended_pair {ε : ℝ} {E B : ℂ → ℂ} (c w : ℂ)
    (hE : DifferentiableOn ℂ E (ball 0 ε))
    (hB : DifferentiableOn ℂ B (ball 0 ε)) :
    DifferentiableOn ℂ (fun z => c * E z ^ 2 * (-deriv B z - w * B z)) (ball 0 ε) := by
  exact ((hE.pow 2).const_mul c).mul
    ((hB.deriv isOpen_ball).neg.sub (hB.const_mul w))

end PGM
