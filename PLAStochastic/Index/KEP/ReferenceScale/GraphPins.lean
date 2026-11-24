import PLAStochastic.Index.KEP.ReferenceScale.BridgeSupport

/-!
# The two graph fluxes as a finite family of pinned graphs

Every pin preserves the output coordinate and reduces exactly one tail length.
The final pin leaves a zero-step tail. This is a finite sum identity on actual
compact integrals, prior to any estimates or infinite-path summation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kepTailTest_neg (p : ℝ → ℝ → ℝ) (w s : ℝ) (n : ℕ) (x : ℝ) (φ : ℝ → ℝ) :
    kepTailTest p w s n x (fun y => -φ y) = -kepTailTest p w s n x φ := by
  simpa only [neg_one_mul] using kepTailTest_const_mul p w s n x (-1) φ

theorem kepTailTest_sub {p : ℝ → ℝ → ℝ} (hp : Continuous (Function.uncurry p))
    (w s : ℝ) (n : ℕ) (x : ℝ) {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    kepTailTest p w s n x (fun y => φ y - ψ y) =
      kepTailTest p w s n x φ - kepTailTest p w s n x ψ := by
  have h := kepTailTest_add hp w s n x hφ hψ.neg
  change kepTailTest p w s n x (fun y => φ y + -ψ y) =
    kepTailTest p w s n x φ + kepTailTest p w s n x (fun y => -ψ y) at h
  rw [kepTailTest_neg] at h
  simpa only [← sub_eq_add_neg] using h

theorem kepTailTest_finsetSum {α : Type*} {p : ℝ → ℝ → ℝ}
    (hp : Continuous (Function.uncurry p)) (w s : ℝ) (n : ℕ) (x : ℝ)
    (I : Finset α) (Φ : α → ℝ → ℝ) (hΦ : ∀ l ∈ I, Continuous (Φ l)) :
    kepTailTest p w s n x (fun y => ∑ l ∈ I, Φ l y) =
      ∑ l ∈ I, kepTailTest p w s n x (Φ l) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, kepTailTest_zero_test]
  | @insert a I ha ih =>
    have hs : Continuous (fun y => ∑ l ∈ I, Φ l y) :=
      continuous_finsetSum I (fun l hl => hΦ l (Finset.mem_insert_of_mem hl))
    simp only [Finset.sum_insert ha]
    have hadd := kepTailTest_add hp w s n x (hΦ a (Finset.mem_insert_self _ _)) hs
    change kepTailTest p w s n x (fun y => Φ a y + ∑ l ∈ I, Φ l y) = _ at hadd
    rw [hadd, ih (fun l hl => hΦ l (Finset.mem_insert_of_mem hl))]

theorem kepTailPairFlux_eq_pin_sums {pA pB : ℝ → ℝ → ℝ}
    (hA : Continuous (Function.uncurry pA)) (hB : Continuous (Function.uncurry pB))
    (w σA σB s : ℝ) (i r : ℕ) (xA xB : ℝ) {Φ : ℝ → ℝ → ℝ}
    (hΦ : Continuous (Function.uncurry Φ)) :
    kepTailPairFlux pA pB w σA σB s i r xA xB Φ =
      -(∑ l ∈ Finset.range i,
        ((w - xA - (l + 1 : ℕ) * σA) * kepFixedBridge pA w s l xA w *
            kepTailPairTest pA pB w s (i - 1 - l) r w xB Φ -
          (-xA - (l + 1 : ℕ) * σA) * kepFixedBridge pA w s l xA 0 *
            kepTailPairTest pA pB w s (i - 1 - l) r 0 xB Φ)) -
      (∑ l ∈ Finset.range r,
        ((w - xB - (l + 1 : ℕ) * σB) * kepFixedBridge pB w s l xB w *
            kepTailPairTest pA pB w s i (r - 1 - l) xA w Φ -
          (-xB - (l + 1 : ℕ) * σB) * kepFixedBridge pB w s l xB 0 *
            kepTailPairTest pA pB w s i (r - 1 - l) xA 0 Φ)) := by
  have hinner : Continuous (fun u => kepTailTest pB w s r xB (Φ u)) :=
    continuous_kepTailTest hB continuous_const hΦ w r xB
  unfold kepTailPairFlux
  rw [kepTailFluxTest_eq_sum hA w σA s i xA hinner]
  have he : kepTailTest pA w s i xA (fun u => kepTailFluxTest pB w σB s r xB (Φ u)) =
      -(∑ l ∈ Finset.range r,
        ((w - xB - (l + 1 : ℕ) * σB) * kepFixedBridge pB w s l xB w *
            kepTailPairTest pA pB w s i (r - 1 - l) xA w Φ -
          (-xB - (l + 1 : ℕ) * σB) * kepFixedBridge pB w s l xB 0 *
            kepTailPairTest pA pB w s i (r - 1 - l) xA 0 Φ)) := by
    let F : ℕ → ℝ → ℝ := fun l u =>
      (w - xB - (l + 1 : ℕ) * σB) * kepFixedBridge pB w s l xB w *
          kepTailTest pB w s (r - 1 - l) w (Φ u) -
        (-xB - (l + 1 : ℕ) * σB) * kepFixedBridge pB w s l xB 0 *
          kepTailTest pB w s (r - 1 - l) 0 (Φ u)
    have hF (l : ℕ) : Continuous (F l) :=
      ((continuous_kepTailTest hB continuous_const hΦ w (r - 1 - l) w).const_mul _).sub
        ((continuous_kepTailTest hB continuous_const hΦ w (r - 1 - l) 0).const_mul _)
    have hrep : kepTailTest pA w s i xA (fun u => kepTailFluxTest pB w σB s r xB (Φ u)) =
        kepTailTest pA w s i xA (fun u => -∑ l ∈ Finset.range r, F l u) := by
      apply kepTailTest_congr
      intro u
      exact kepTailFluxTest_eq_sum hB w σB s r xB (hΦ.comp
        (continuous_const.prodMk continuous_id))
    rw [hrep, kepTailTest_neg,
      kepTailTest_finsetSum hA w s i xA (Finset.range r) F (fun l _ => hF l)]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    have hw' : Continuous (fun u => (w - xB - (l + 1 : ℕ) * σB) *
        kepFixedBridge pB w s l xB w * kepTailTest pB w s (r - 1 - l) w (Φ u)) :=
      (continuous_kepTailTest hB continuous_const hΦ w (r - 1 - l) w).const_mul _
    have h0' : Continuous (fun u => (-xB - (l + 1 : ℕ) * σB) *
        kepFixedBridge pB w s l xB 0 * kepTailTest pB w s (r - 1 - l) 0 (Φ u)) :=
      (continuous_kepTailTest hB continuous_const hΦ w (r - 1 - l) 0).const_mul _
    dsimp only [F]
    rw [kepTailTest_sub hA w s i xA hw' h0', kepTailTest_const_mul, kepTailTest_const_mul]
    rfl
  rw [he]
  rfl

end

end PGM
