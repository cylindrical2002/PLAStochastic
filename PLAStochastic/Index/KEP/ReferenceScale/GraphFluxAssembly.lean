import PLAStochastic.Index.KEP.ReferenceScale.ActualGraphTransfer

/-!
# Integrating the complete finite pin graph sum

Each pin scalar includes the slope Jacobian `exp(s) / D`. Its updated graph
keeps the exact output coordinate. The four outward signs are combined only
after the compact slope integrals have been proved integrable.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

def kepGraphBoundarySum (i r : ℕ) (w : ℝ) (FL FR : ℕ → ℝ → ℝ) : ℝ :=
  -(∑ l ∈ Finset.range i, FL l w) + (∑ l ∈ Finset.range i, FL l 0) +
    (∑ l ∈ Finset.range r, FR l w) - (∑ l ∈ Finset.range r, FR l 0)

def kepGraphLeftPinIntegral (pA pB : ℝ → ℝ → ℝ) (w lo hi D : ℝ) (i r : ℕ)
    (xA xB : ℝ) (R φ : ℝ → ℝ) (l : ℕ) (b : ℝ) : ℝ :=
  let d := kepGapNumerator (-1) (l + 1) xA b
  kepLogGraphIntegral pA pB w lo hi (D + d) (i - 1 - l) r b xB
    (kepGraphPinScalar pA w D d l xA b R) φ

def kepGraphRightPinIntegral (pA pB : ℝ → ℝ → ℝ) (w lo hi D : ℝ) (i r : ℕ)
    (xA xB : ℝ) (R φ : ℝ → ℝ) (l : ℕ) (b : ℝ) : ℝ :=
  let d := kepGapNumerator 1 (l + 1) xB b
  kepLogGraphIntegral pA pB w lo hi (D + d) i (r - 1 - l) xA b
    (kepGraphPinScalar pB w D d l xB b R) φ

theorem kepLogGraphFluxIntegral_eq_pin_integrals {pA pB : ℝ → ℝ → ℝ}
    (hA : Continuous (Function.uncurry pA)) (hB : Continuous (Function.uncurry pB))
    {R φ : ℝ → ℝ} (hR : Continuous R) (hφ : Continuous φ)
    (w lo hi D : ℝ) (i r : ℕ) (xA xB : ℝ) :
    kepLogGraphFluxIntegral pA pB w lo hi D i r xA xB R φ =
      kepGraphBoundarySum i r w
        (kepGraphLeftPinIntegral pA pB w lo hi D i r xA xB R φ)
        (kepGraphRightPinIntegral pA pB w lo hi D i r xA xB R φ) := by
  let FL : ℝ → ℕ → ℝ → ℝ := fun s l b =>
    let d := kepGapNumerator (-1) (l + 1) xA b
    kepGraphPinScalar pA w D d l xA b R s *
      kepTailPairTest pA pB w s (i - 1 - l) r b xB
        (fun u v => φ (kepGraphOutput (D + d) (i - 1 - l) r b xB s u v))
  let FR : ℝ → ℕ → ℝ → ℝ := fun s l b =>
    let d := kepGapNumerator 1 (l + 1) xB b
    kepGraphPinScalar pB w D d l xB b R s *
      kepTailPairTest pA pB w s i (r - 1 - l) xA b
        (fun u v => φ (kepGraphOutput (D + d) i (r - 1 - l) xA b s u v))
  have hFL (l : ℕ) (b : ℝ) : Continuous (fun s => FL s l b) := by
    have hK : Continuous (fun s => kepFixedBridge pA w s l xA b) :=
      (continuous_kepFixedBridge hA w l).comp
        (continuous_id.prodMk (continuous_const.prodMk continuous_const))
    have hP := continuous_kepTailPairTest hA hB
      (Φ := fun s u v => φ (kepGraphOutput
        (D + kepGapNumerator (-1) (l + 1) xA b) (i - 1 - l) r b xB s u v))
      (hφ.comp (continuous_kepGraphOutput
        (D + kepGapNumerator (-1) (l + 1) xA b) (i - 1 - l) r b xB))
      w (i - 1 - l) r b xB
    dsimp [FL, kepGraphPinScalar]
    fun_prop
  have hFR (l : ℕ) (b : ℝ) : Continuous (fun s => FR s l b) := by
    have hK : Continuous (fun s => kepFixedBridge pB w s l xB b) :=
      (continuous_kepFixedBridge hB w l).comp
        (continuous_id.prodMk (continuous_const.prodMk continuous_const))
    have hP := continuous_kepTailPairTest hA hB
      (Φ := fun s u v => φ (kepGraphOutput
        (D + kepGapNumerator 1 (l + 1) xB b) i (r - 1 - l) xA b s u v))
      (hφ.comp (continuous_kepGraphOutput
        (D + kepGapNumerator 1 (l + 1) xB b) i (r - 1 - l) xA b))
      w i (r - 1 - l) xA b
    dsimp [FR, kepGraphPinScalar]
    fun_prop
  have hleft (s : ℝ) (l : ℕ) (hl : l < i) (b : ℝ) :
      (Real.exp s * R s / D) * ((b - xA - (l + 1 : ℕ) * (-1)) *
        kepFixedBridge pA w s l xA b * kepTailPairTest pA pB w s (i - 1 - l) r b xB
          (fun u v => φ (kepGraphOutput D i r xA xB s u v))) = FL s l b := by
    have he : kepTailPairTest pA pB w s (i - 1 - l) r b xB
        (fun u v => φ (kepGraphOutput D i r xA xB s u v)) =
      kepTailPairTest pA pB w s (i - 1 - l) r b xB
        (fun u v => φ (kepGraphOutput
          (D + kepGapNumerator (-1) (l + 1) xA b) (i - 1 - l) r b xB s u v)) := by
      apply kepTailPairTest_congr
      intro u v
      congr 1
      have hp := kepGraphOutput_left_pin D i r (l + 1) (by omega) xA xB b s u v
      have hlen : i - (l + 1) = i - 1 - l := by omega
      simpa only [hlen] using hp.symm
    rw [he]
    dsimp [FL, kepGraphPinScalar, kepGapNumerator]
    ring
  have hright (s : ℝ) (l : ℕ) (hl : l < r) (b : ℝ) :
      (Real.exp s * R s / D) * ((b - xB - (l + 1 : ℕ) * 1) *
        kepFixedBridge pB w s l xB b * kepTailPairTest pA pB w s i (r - 1 - l) xA b
          (fun u v => φ (kepGraphOutput D i r xA xB s u v))) = -FR s l b := by
    have he : kepTailPairTest pA pB w s i (r - 1 - l) xA b
        (fun u v => φ (kepGraphOutput D i r xA xB s u v)) =
      kepTailPairTest pA pB w s i (r - 1 - l) xA b
        (fun u v => φ (kepGraphOutput
          (D + kepGapNumerator 1 (l + 1) xB b) i (r - 1 - l) xA b s u v)) := by
      apply kepTailPairTest_congr
      intro u v
      congr 1
      have hp := kepGraphOutput_right_pin D i r (l + 1) (by omega) xA xB b s u v
      have hlen : r - (l + 1) = r - 1 - l := by omega
      simpa only [hlen] using hp.symm
    rw [he]
    dsimp [FR, kepGraphPinScalar, kepGapNumerator]
    ring
  have hpoint (s : ℝ) : (Real.exp s * R s / D) *
      kepTailPairFlux pA pB w (-1) 1 s i r xA xB
        (fun u v => φ (kepGraphOutput D i r xA xB s u v)) =
      kepGraphBoundarySum i r w (FL s) (FR s) := by
    have hΦ : Continuous (fun t : ℝ × ℝ => φ (kepGraphOutput D i r xA xB s t.1 t.2)) :=
      hφ.comp ((continuous_kepGraphOutput D i r xA xB).comp
        (continuous_const.prodMk continuous_id))
    rw [kepTailPairFlux_eq_pin_sums hA hB w (-1) 1 s i r xA xB
      (Φ := fun u v => φ (kepGraphOutput D i r xA xB s u v)) hΦ, mul_sub, mul_neg]
    have hL : (Real.exp s * R s / D) *
        (∑ l ∈ Finset.range i,
          ((w - xA - (l + 1 : ℕ) * (-1)) * kepFixedBridge pA w s l xA w *
              kepTailPairTest pA pB w s (i - 1 - l) r w xB
                (fun u v => φ (kepGraphOutput D i r xA xB s u v)) -
            (-xA - (l + 1 : ℕ) * (-1)) * kepFixedBridge pA w s l xA 0 *
              kepTailPairTest pA pB w s (i - 1 - l) r 0 xB
                (fun u v => φ (kepGraphOutput D i r xA xB s u v)))) =
        (∑ l ∈ Finset.range i, FL s l w) - ∑ l ∈ Finset.range i, FL s l 0 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_sub, hleft s l (Finset.mem_range.mp hl) w]
      have hz := hleft s l (Finset.mem_range.mp hl) 0
      simpa only [zero_sub] using congrArg (fun t => FL s l w - t) hz
    have hR' : (Real.exp s * R s / D) *
        (∑ l ∈ Finset.range r,
          ((w - xB - (l + 1 : ℕ) * 1) * kepFixedBridge pB w s l xB w *
              kepTailPairTest pA pB w s i (r - 1 - l) xA w
                (fun u v => φ (kepGraphOutput D i r xA xB s u v)) -
            (-xB - (l + 1 : ℕ) * 1) * kepFixedBridge pB w s l xB 0 *
              kepTailPairTest pA pB w s i (r - 1 - l) xA 0
                (fun u v => φ (kepGraphOutput D i r xA xB s u v)))) =
        -(∑ l ∈ Finset.range r, FR s l w) + ∑ l ∈ Finset.range r, FR s l 0 := by
      rw [Finset.mul_sum]
      have hs : (∑ l ∈ Finset.range r,
          (Real.exp s * R s / D) *
            ((w - xB - (l + 1 : ℕ) * 1) * kepFixedBridge pB w s l xB w *
                kepTailPairTest pA pB w s i (r - 1 - l) xA w
                  (fun u v => φ (kepGraphOutput D i r xA xB s u v)) -
              (-xB - (l + 1 : ℕ) * 1) * kepFixedBridge pB w s l xB 0 *
                kepTailPairTest pA pB w s i (r - 1 - l) xA 0
                  (fun u v => φ (kepGraphOutput D i r xA xB s u v)))) =
          ∑ l ∈ Finset.range r, (-FR s l w + FR s l 0) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [mul_sub, hright s l (Finset.mem_range.mp hl) w]
        have hz := hright s l (Finset.mem_range.mp hl) 0
        simp only [zero_sub] at hz
        rw [hz, sub_neg_eq_add]
      rw [hs, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [hL, hR']
    unfold kepGraphBoundarySum
    ring
  unfold kepLogGraphFluxIntegral
  simp_rw [hpoint]
  have hLw : Continuous (fun s => ∑ l ∈ Finset.range i, FL s l w) :=
    continuous_finsetSum _ fun l _ => hFL l w
  have hL0 : Continuous (fun s => ∑ l ∈ Finset.range i, FL s l 0) :=
    continuous_finsetSum _ fun l _ => hFL l 0
  have hRw : Continuous (fun s => ∑ l ∈ Finset.range r, FR s l w) :=
    continuous_finsetSum _ fun l _ => hFR l w
  have hR0 : Continuous (fun s => ∑ l ∈ Finset.range r, FR s l 0) :=
    continuous_finsetSum _ fun l _ => hFR l 0
  have hint (g : ℝ → ℝ) (hg : Continuous g) :
      Integrable g (volume.restrict (Ioc lo hi)) :=
    hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  unfold kepGraphBoundarySum
  rw [integral_sub (f := fun s => -(∑ l ∈ Finset.range i, FL s l w) +
      (∑ l ∈ Finset.range i, FL s l 0) + ∑ l ∈ Finset.range r, FR s l w)
    (g := fun s => ∑ l ∈ Finset.range r, FR s l 0) (hint _ (by fun_prop)) (hint _ hR0),
    integral_add (f := fun s => -(∑ l ∈ Finset.range i, FL s l w) +
      ∑ l ∈ Finset.range i, FL s l 0) (g := fun s => ∑ l ∈ Finset.range r, FR s l w)
    (hint _ (by fun_prop)) (hint _ hRw),
    integral_add (f := fun s => -(∑ l ∈ Finset.range i, FL s l w))
    (g := fun s => ∑ l ∈ Finset.range i, FL s l 0) (hint _ hLw.neg) (hint _ hL0), integral_neg,
    integral_finsetSum _ (fun l _ => hint _ (hFL l w)),
    integral_finsetSum _ (fun l _ => hint _ (hFL l 0)),
    integral_finsetSum _ (fun l _ => hint _ (hFR l w)),
    integral_finsetSum _ (fun l _ => hint _ (hFR l 0))]
  rfl

end

end PGM
