import PLAStochastic.ForMathlib.Analysis.Complex.EvenSqrt

/-! # Square-root descent under local evenness -/

noncomputable section
open Set Metric Complex
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem differentiableOn_comp_sqrt_of_locally_even {Ψ : ℂ → E} {R : ℝ} (hR : 0 < R)
    (hΨ : DifferentiableOn ℂ Ψ (ball 0 R))
    (heven : ∀ r ∈ ball (0 : ℂ) R, Ψ (-r) = Ψ r) :
    DifferentiableOn ℂ (fun w => Ψ (Complex.sqrt w)) (ball 0 (R ^ 2)) := by
  classical
  let Ψ' : ℂ → E := fun r => if r ∈ ball (0 : ℂ) R then Ψ r else 0
  have hd : DifferentiableOn ℂ Ψ' (ball 0 R) :=
    hΨ.congr (fun r hr => by simp only [Ψ', if_pos hr])
  have he : ∀ r, Ψ' (-r) = Ψ' r := by
    intro r
    have hneg : -r ∈ ball (0 : ℂ) R ↔ r ∈ ball (0 : ℂ) R := by
      simp only [mem_ball_zero_iff, norm_neg]
    by_cases hr : r ∈ ball (0 : ℂ) R
    · simp only [Ψ', if_pos hr, if_pos (hneg.mpr hr), heven r hr]
    · simp only [Ψ', if_neg hr, if_neg (not_congr hneg |>.mpr hr)]
  apply (differentiableOn_comp_sqrt_of_even hR hd he).congr
  intro w hw
  have hs : Complex.sqrt w ∈ ball (0 : ℂ) R :=
    mem_ball_zero_iff.mpr (norm_sqrt_lt hR (mem_ball_zero_iff.mp hw))
  simp only [Ψ', if_pos hs]

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem continuousOn_comp_sqrt_of_locally_even {X : Type*} [TopologicalSpace X]
    {Ψ : X → ℂ → E} {P : Set X} {R : ℝ} (hR : 0 < R)
    (hΨ : ContinuousOn (fun x : X × ℂ => Ψ x.1 x.2) (P ×ˢ ball 0 R))
    (heven : ∀ x ∈ P, ∀ r ∈ ball (0 : ℂ) R, Ψ x (-r) = Ψ x r) :
    ContinuousOn (fun x : X × ℂ => Ψ x.1 (Complex.sqrt x.2)) (P ×ˢ ball 0 (R ^ 2)) := by
  classical
  let Ψ' : X → ℂ → E := fun x r => if x ∈ P ∧ r ∈ ball (0 : ℂ) R then Ψ x r else 0
  have hc : ContinuousOn (fun x : X × ℂ => Ψ' x.1 x.2) (P ×ˢ ball 0 R) :=
    hΨ.congr (fun x hx => by
      simp only [Ψ', if_pos (show x.1 ∈ P ∧ x.2 ∈ ball (0 : ℂ) R from hx)])
  have he : ∀ x r, Ψ' x (-r) = Ψ' x r := by
    intro x r
    have hneg : -r ∈ ball (0 : ℂ) R ↔ r ∈ ball (0 : ℂ) R := by
      simp only [mem_ball_zero_iff, norm_neg]
    dsimp only [Ψ']
    rw [hneg]
    split_ifs with h
    · exact heven x h.1 r h.2
    · rfl
  apply (continuousOn_comp_sqrt_of_even hR hc he).congr
  intro x hx
  have hs : Complex.sqrt x.2 ∈ ball (0 : ℂ) R :=
    mem_ball_zero_iff.mpr (norm_sqrt_lt hR (mem_ball_zero_iff.mp hx.2))
  simp only [Ψ', if_pos (show x.1 ∈ P ∧ x.2.sqrt ∈ ball (0 : ℂ) R from ⟨hx.1, hs⟩)]

end PGM
