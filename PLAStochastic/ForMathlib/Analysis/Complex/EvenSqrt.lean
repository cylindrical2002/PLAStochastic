import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Even functions of the square root

If `Ψ` is even (`Ψ (-ρ) = Ψ ρ`), then `w ↦ Ψ (√w)` (principal square root) does not see the
branch cut: `Ψ (√w) = Ψ (i √(-w))` for all `w` (`even_comp_sqrt_eq`), and the two branches
`√·` and `i √(-·)` cover `ℂ \ {0}` by their regularity regions.

* `differentiableOn_comp_sqrt_of_even`: `Ψ` holomorphic on `B(0, R)` and even ⇒
  `w ↦ Ψ (√w)` holomorphic on `B(0, R²)` (removable singularity at `0`);
* `continuousOn_comp_sqrt_of_even`: a parameter version of continuity: if
  `p ↦ Ψ p.1 p.2` is continuous on `P ×ˢ B(0, R)` and even in the second argument, then
  `p ↦ Ψ p.1 (√p.2)` is continuous on `P ×ˢ B(0, R²)`.
-/

noncomputable section

open Set Metric Complex Filter Topology

namespace PGM

theorem sqrt_sq_eq (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  rw [Complex.sqrt]; exact cpow_ofNat_inv_pow w 2

theorem I_mul_sqrt_neg_sq (w : ℂ) : (I * Complex.sqrt (-w)) ^ 2 = w := by
  rw [mul_pow, I_sq, sqrt_sq_eq]; ring

theorem norm_sqrt (w : ℂ) : ‖Complex.sqrt w‖ = Real.sqrt ‖w‖ := by
  have h : ‖Complex.sqrt w‖ ^ 2 = ‖w‖ := by rw [← norm_pow, sqrt_sq_eq]
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem norm_sqrt_lt {w : ℂ} {R : ℝ} (hR : 0 < R) (hw : ‖w‖ < R ^ 2) : ‖Complex.sqrt w‖ < R := by
  rw [norm_sqrt, Real.sqrt_lt' hR]; exact hw

/-- For an even function the two branches of the square root give the same value. -/
theorem even_comp_sqrt_eq {E : Type*} {Ψ : ℂ → E} (heven : ∀ ρ, Ψ (-ρ) = Ψ ρ) (w : ℂ) :
    Ψ (I * Complex.sqrt (-w)) = Ψ (Complex.sqrt w) := by
  have h : (I * Complex.sqrt (-w)) ^ 2 = Complex.sqrt w ^ 2 := by
    rw [I_mul_sqrt_neg_sq, sqrt_sq_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
  · rw [h']
  · rw [h', heven]

theorem mem_slitPlane_or_neg_mem {w : ℂ} (hw : w ≠ 0) : w ∈ slitPlane ∨ -w ∈ slitPlane := by
  by_cases h : w ∈ slitPlane
  · exact Or.inl h
  · right
    rw [mem_slitPlane_iff] at h ⊢
    push Not at h
    rw [neg_re, neg_im]
    by_cases hre : w.re = 0
    · exact absurd (Complex.ext hre h.2) hw
    · left; have := h.1; exact neg_pos.mpr (lt_of_le_of_ne this hre)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Holomorphy of `w ↦ Ψ (√w)` for an even holomorphic `Ψ`. -/
theorem differentiableOn_comp_sqrt_of_even {Ψ : ℂ → E} {R : ℝ} (hR : 0 < R)
    (hΨ : DifferentiableOn ℂ Ψ (ball 0 R)) (heven : ∀ ρ, Ψ (-ρ) = Ψ ρ) :
    DifferentiableOn ℂ (fun w => Ψ (Complex.sqrt w)) (ball 0 (R ^ 2)) := by
  have hball : ∀ w ∈ ball (0 : ℂ) (R ^ 2), Complex.sqrt w ∈ ball (0 : ℂ) R := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw ⊢
    exact norm_sqrt_lt hR hw
  have hball' : ∀ w ∈ ball (0 : ℂ) (R ^ 2), I * Complex.sqrt (-w) ∈ ball (0 : ℂ) R := by
    intro w hw
    have := hball (-w) (by rwa [mem_ball, dist_zero_right, norm_neg, ← dist_zero_right])
    rw [mem_ball, dist_zero_right] at this ⊢
    rwa [norm_mul, norm_I, one_mul]
  have hoff : DifferentiableOn ℂ (fun w => Ψ (Complex.sqrt w)) (ball 0 (R ^ 2) \ {0}) := by
    intro w ⟨hw, hw0⟩
    have hw0' : w ≠ 0 := hw0
    have hopen : ball (0 : ℂ) (R ^ 2) \ {0} ∈ 𝓝 w :=
      (isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hw, hw0⟩
    rcases mem_slitPlane_or_neg_mem hw0' with hs | hs
    · have h1 := (hΨ _ (hball w hw)).differentiableAt (isOpen_ball.mem_nhds (hball w hw))
      exact (h1.comp w (differentiableAt_sqrt hs)).differentiableWithinAt
    · have h1 := (hΨ _ (hball' w hw)).differentiableAt (isOpen_ball.mem_nhds (hball' w hw))
      have h2 : DifferentiableAt ℂ (fun w => I * Complex.sqrt (-w)) w :=
        ((differentiableAt_sqrt hs).comp w differentiableAt_id.neg).const_mul I
      have h3 : DifferentiableAt ℂ (fun w => Ψ (I * Complex.sqrt (-w))) w := h1.comp w h2
      have heq : (fun w => Ψ (I * Complex.sqrt (-w))) = fun w => Ψ (Complex.sqrt w) := by
        funext w; exact even_comp_sqrt_eq heven w
      rw [heq] at h3
      exact h3.differentiableWithinAt
  have hR2 : (0 : ℂ) ∈ ball (0 : ℂ) (R ^ 2) := mem_ball_self (by positivity)
  refine (differentiableOn_compl_singleton_and_continuousAt_iff
    (isOpen_ball.mem_nhds hR2)).mp ⟨hoff, ?_⟩
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hc : ContinuousAt Ψ (Complex.sqrt 0) := by
    rw [Complex.sqrt_zero]
    exact (hΨ 0 h0).continuousWithinAt.continuousAt (isOpen_ball.mem_nhds h0)
  exact hc.comp (continuousAt_sqrt (Or.inl (by simp)))

omit [NormedSpace ℂ E] [CompleteSpace E] in
/-- Continuity of `(p, w) ↦ Ψ p (√w)` for `Ψ` even in its second argument. -/
theorem continuousOn_comp_sqrt_of_even {X : Type*} [TopologicalSpace X] {Ψ : X → ℂ → E}
    {P : Set X} {R : ℝ} (hR : 0 < R)
    (hΨ : ContinuousOn (fun p : X × ℂ => Ψ p.1 p.2) (P ×ˢ ball 0 R))
    (heven : ∀ x ρ, Ψ x (-ρ) = Ψ x ρ) :
    ContinuousOn (fun p : X × ℂ => Ψ p.1 (Complex.sqrt p.2)) (P ×ˢ ball 0 (R ^ 2)) := by
  intro p ⟨hp1, hp2⟩
  have hball : ∀ w ∈ ball (0 : ℂ) (R ^ 2), Complex.sqrt w ∈ ball (0 : ℂ) R := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw ⊢
    exact norm_sqrt_lt hR hw
  by_cases hre : 0 ≤ p.2.re ∨ p.2.im ≠ 0
  · -- the principal branch is continuous at `p.2`
    have hs : ContinuousAt Complex.sqrt p.2 := continuousAt_sqrt hre
    have hmap : ContinuousWithinAt (fun q : X × ℂ => (q.1, Complex.sqrt q.2)) (P ×ˢ ball 0 (R ^ 2))
        p := continuousWithinAt_fst.prodMk (hs.comp_continuousWithinAt continuousWithinAt_snd)
    exact ContinuousWithinAt.comp (g := fun q : X × ℂ => Ψ q.1 q.2)
      (f := fun q : X × ℂ => (q.1, Complex.sqrt q.2)) (t := P ×ˢ ball 0 R)
      (hΨ (p.1, Complex.sqrt p.2) ⟨hp1, hball _ hp2⟩) hmap
      (fun q (hq : q ∈ P ×ˢ ball 0 (R ^ 2)) => ⟨hq.1, hball _ hq.2⟩)
  · -- negative real axis: use the branch `i √(-w)`
    push Not at hre
    have hneg : 0 ≤ (-p.2).re ∨ (-p.2).im ≠ 0 := Or.inl (by rw [neg_re]; linarith [hre.1])
    have hs : ContinuousAt (fun w => I * Complex.sqrt (-w)) p.2 :=
      ((continuousAt_sqrt hneg).comp continuousAt_id.neg).const_mul I
    have hball' : ∀ w ∈ ball (0 : ℂ) (R ^ 2), I * Complex.sqrt (-w) ∈ ball (0 : ℂ) R := by
      intro w hw
      have := hball (-w) (by rwa [mem_ball, dist_zero_right, norm_neg, ← dist_zero_right])
      rw [mem_ball, dist_zero_right] at this ⊢
      rwa [norm_mul, norm_I, one_mul]
    have hmap : ContinuousWithinAt (fun q : X × ℂ => (q.1, I * Complex.sqrt (-q.2)))
        (P ×ˢ ball 0 (R ^ 2)) p :=
      continuousWithinAt_fst.prodMk (hs.comp_continuousWithinAt continuousWithinAt_snd)
    have h := ContinuousWithinAt.comp (g := fun q : X × ℂ => Ψ q.1 q.2)
      (f := fun q : X × ℂ => (q.1, I * Complex.sqrt (-q.2))) (t := P ×ˢ ball 0 R)
      (hΨ (p.1, I * Complex.sqrt (-p.2)) ⟨hp1, hball' _ hp2⟩) hmap
      (fun q (hq : q ∈ P ×ˢ ball 0 (R ^ 2)) => ⟨hq.1, hball' _ hq.2⟩)
    have heq : ((fun p : X × ℂ => Ψ p.1 p.2) ∘ fun q : X × ℂ => (q.1, I * Complex.sqrt (-q.2))) =
        fun p : X × ℂ => Ψ p.1 (Complex.sqrt p.2) := by
      funext q; exact even_comp_sqrt_eq (heven q.1) q.2
    rwa [heq] at h

end PGM
