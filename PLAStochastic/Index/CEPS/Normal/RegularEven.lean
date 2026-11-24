import PLAStochastic.Index.CEPS.Normal.DividedDifferenceSymmetry

/-! # Root exchange and squared-coordinate holomorphy of the regular forms -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNormal_sqrt_of_locally_even {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 R))
    (he : ∀ r ∈ ball (0 : ℂ) R, F (-r) = F r) :
    DifferentiableOn ℂ (fun z => F (sqrt z)) (ball 0 (R ^ 2)) := by
  classical
  let G : ℂ → ℂ := fun r => if r ∈ ball (0 : ℂ) R then F r else 0
  have hG : DifferentiableOn ℂ G (ball 0 R) :=
    hF.congr (fun r hr => by simp only [G, if_pos hr])
  have hGe : ∀ r, G (-r) = G r := by
    intro r
    have hn : -r ∈ ball (0 : ℂ) R ↔ r ∈ ball (0 : ℂ) R := by
      simp [mem_ball, dist_zero_right]
    by_cases hr : r ∈ ball (0 : ℂ) R
    · simp only [G, if_pos hr, if_pos (hn.mpr hr)]
      exact he r hr
    · simp only [G, if_neg hr, if_neg (mt hn.mp hr)]
  apply (differentiableOn_comp_sqrt_of_even hR hG hGe).congr
  intro z hz
  have hs : sqrt z ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right] at hz ⊢
    exact norm_sqrt_lt hR hz
  simp only [G, if_pos hs]

namespace CepsNormalData

variable (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q l : ℂ)

theorem regularBridge_swap : a.swapRoots.regularBridge L μ q l = a.regularBridge L μ q l := by
  unfold regularBridge
  change -a.normalG L μ q l a.βm * a.normalG L μ q l a.βp /
    dslope (a.normalG L μ q l) a.βp a.βm = _
  rw [cepsNormal_dslope_swap (a.normalG L μ q l) a.βp a.βm]
  ring

theorem regularEntrance_swap (t : ℂ)
    (hp : DifferentiableAt ℂ (a.normalG L μ q l) a.βp)
    (hm : DifferentiableAt ℂ (a.normalG L μ q l) a.βm) :
    a.swapRoots.regularEntrance L μ q l t = a.regularEntrance L μ q l t := by
  unfold regularEntrance
  change -exp (L μ q t) * dslope (dslope (a.normalG L μ q l) a.βp) a.βm t /
    (a.Q t * dslope (a.normalG L μ q l) a.βp a.βm) = _
  rw [cepsNormal_dslope_swap (a.normalG L μ q l) a.βp a.βm,
    ← cepsNormal_second_dslope_swap hp hm t]

end CepsNormalData

/-- Root exchange implies evenness of the regular entrance itself, including
zero root differences and markers equal to either root.
-/
theorem cepsNormal_regularEntrance_even {R : ℝ} {A : ℂ → CepsNormalData}
    {L : ℂ → ℂ → ℂ → ℂ} {μ l : ℂ} {q t : ℂ → ℂ}
    (hA : ∀ r ∈ ball (0 : ℂ) R, A (-r) = (A r).swapRoots)
    (hq : ∀ r ∈ ball (0 : ℂ) R, q (-r) = q r)
    (ht : ∀ r ∈ ball (0 : ℂ) R, t (-r) = t r)
    (hG : ∀ r ∈ ball (0 : ℂ) R,
      DifferentiableAt ℂ ((A r).normalG L μ (q r) l) (A r).βp ∧
      DifferentiableAt ℂ ((A r).normalG L μ (q r) l) (A r).βm) :
    ∀ r ∈ ball (0 : ℂ) R,
      (A (-r)).regularEntrance L μ (q (-r)) l (t (-r)) =
        (A r).regularEntrance L μ (q r) l (t r) := by
  intro r hr
  rw [hA r hr, hq r hr, ht r hr]
  exact (A r).regularEntrance_swap L μ (q r) l (t r) (hG r hr).1 (hG r hr).2

theorem cepsNormal_regularBridge_even {R : ℝ} {A : ℂ → CepsNormalData}
    {L : ℂ → ℂ → ℂ → ℂ} {μ l : ℂ} {q : ℂ → ℂ}
    (hA : ∀ r ∈ ball (0 : ℂ) R, A (-r) = (A r).swapRoots)
    (hq : ∀ r ∈ ball (0 : ℂ) R, q (-r) = q r) :
    ∀ r ∈ ball (0 : ℂ) R,
      (A (-r)).regularBridge L μ (q (-r)) l = (A r).regularBridge L μ (q r) l := by
  intro r hr
  rw [hA r hr, hq r hr]
  exact (A r).regularBridge_swap L μ (q r) l

/-- The even regular forms descend holomorphically to `r²`, including zero.
The symmetry premises describe the roots/factor data, not the desired forms.
-/
theorem cepsNormal_regular_forms_squared {R : ℝ} (hR : 0 < R) {A : ℂ → CepsNormalData}
    {L : ℂ → ℂ → ℂ → ℂ} {μ l : ℂ} {q t : ℂ → ℂ}
    (hA : ∀ r ∈ ball (0 : ℂ) R, A (-r) = (A r).swapRoots)
    (hq : ∀ r ∈ ball (0 : ℂ) R, q (-r) = q r)
    (ht : ∀ r ∈ ball (0 : ℂ) R, t (-r) = t r)
    (hG : ∀ r ∈ ball (0 : ℂ) R,
      DifferentiableAt ℂ ((A r).normalG L μ (q r) l) (A r).βp ∧
      DifferentiableAt ℂ ((A r).normalG L μ (q r) l) (A r).βm)
    (hE : DifferentiableOn ℂ (fun r => (A r).regularEntrance L μ (q r) l (t r)) (ball 0 R))
    (hB : DifferentiableOn ℂ (fun r => (A r).regularBridge L μ (q r) l) (ball 0 R)) :
    DifferentiableOn ℂ (fun z => (A (sqrt z)).regularEntrance L μ (q (sqrt z)) l (t (sqrt z)))
        (ball 0 (R ^ 2)) ∧
      DifferentiableOn ℂ (fun z => (A (sqrt z)).regularBridge L μ (q (sqrt z)) l)
        (ball 0 (R ^ 2)) := by
  exact ⟨cepsNormal_sqrt_of_locally_even hR hE
    (cepsNormal_regularEntrance_even hA hq ht hG),
    cepsNormal_sqrt_of_locally_even hR hB (cepsNormal_regularBridge_even hA hq)⟩

end PGM
