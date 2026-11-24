import PLAStochastic.Index.KEP.ReferenceScale.KernelRemainder
import PLAStochastic.Index.GEP.Kernel.Row.Long.KilledBV

/-!
# Real representatives of the existing killed-row decomposition

The original Fourier decomposition uses complex L2 functions. Taking real
parts preserves its variation bound and decreases the remainder norm. The
remainder is defined by subtraction from the actual row, so reconstruction is
pointwise and interval support is retained.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

theorem eVariationOn_ofReal_re_le (g : ℝ → ℂ) :
    eVariationOn (fun t => ((g t).re : ℂ)) univ ≤ eVariationOn g univ := by
  have hl : LipschitzWith 1 (fun z : ℂ => (z.re : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, ← Complex.sub_re] using
        Complex.abs_re_le_norm (z - w)
  have h := hl.lipschitzOnWith.comp_eVariationOn_le (g := g) (s := univ)
    (mapsTo_univ _ _)
  simp only [ENNReal.coe_one, one_mul] at h
  have he : (fun t => ((g t).re : ℂ)) = (fun z : ℂ => (z.re : ℂ)) ∘ g := by
    funext t
    rfl
  rw [he]
  exact h

theorem kBV_decomposition_real_representatives {J : Set ℝ} {B : ℝ} {q : ℝ → ℝ}
    (hq : Measurable q) (hq1 : Integrable q volume)
    (hq2 : MemLp (fun x => (q x : ℂ)) 2 volume)
    (hsupp : ∀ x, x ∉ J → q x = 0) {G R : KernelL2}
    (hGR : hq2.toLp _ = G + R) (hG : kBVHasRep J B G) :
    ∃ g r : ℝ → ℝ, Measurable g ∧ Integrable g volume ∧ MemLp g 2 volume ∧
      Measurable r ∧ Integrable r volume ∧ MemLp r 2 volume ∧
      (∀ x, x ∉ J → g x = 0 ∧ r x = 0) ∧
      (∀ x, q x = g x + r x) ∧
      eVariationOn (fun x => (g x : ℂ)) univ ≤ ENNReal.ofReal B ∧
      (∫ x, r x ^ 2) ≤ ‖R‖ ^ 2 := by
  obtain ⟨g, r, hg, hg1, hg2, hr, hr1, hr2, hs, hsum, hvar, hnorm⟩ :=
    kBV_decomposition_representatives (Complex.measurable_ofReal.comp hq) hq1.ofReal
      hq2 (fun x hx => by simp only [Function.comp_apply, hsupp x hx, Complex.ofReal_zero])
      hGR hG
  refine ⟨fun x => (g x).re, fun x => (r x).re,
    Complex.measurable_re.comp hg, hg1.re, hg2.re,
    Complex.measurable_re.comp hr, hr1.re, hr2.re, ?_, ?_,
    (eVariationOn_ofReal_re_le g).trans hvar, ?_⟩
  · intro x hx
    obtain ⟨hgx, hrx⟩ := hs x hx
    simp only [hgx, hrx, Complex.zero_re, and_self]
  · intro x
    have h := congrArg Complex.re (hsum x)
    simpa only [Function.comp_apply, Complex.ofReal_re, Complex.add_re] using h
  · calc
      (∫ x, (r x).re ^ 2) ≤ ∫ x, ‖r x‖ ^ 2 := by
        apply integral_mono
          ((memLp_two_iff_integrable_sq hr2.re.aestronglyMeasurable).1 hr2.re)
          ((memLp_two_iff_integrable_sq_norm hr2.aestronglyMeasurable).1 hr2)
        intro x
        change (r x).re ^ 2 ≤ ‖r x‖ ^ 2
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (r x).re)
          (Complex.abs_re_le_norm (r x)) 2
      _ = ‖R‖ ^ 2 := hnorm

/-- Real regular/small components of the actual long killed row, with the
same explicit class-uniform budgets as the existing Fourier decomposition. -/
theorem krDens_long_real_decomposition {D θ vlo vhi K L w A a β a' : ℝ}
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (m k : ℕ) (hk : 8 ≤ k) (x : ℝ) :
    ∃ g r : ℝ → ℝ, Measurable g ∧ Integrable g volume ∧ MemLp g 2 volume ∧
      Measurable r ∧ Integrable r volume ∧ MemLp r 2 volume ∧
      (∀ y, y ∉ Icc 0 w → g y = 0 ∧ r y = 0) ∧
      (∀ y, krDens (Icc 0 w) ν f β a' (m + 1 + k) x y = g y + r y) ∧
      eVariationOn (fun y => (g y : ℂ)) univ ≤ ENNReal.ofReal
        ((8 * Real.pi * Real.sqrt w +
          8 * Real.pi * Real.sqrt w / (1 - Real.sqrt (1 - killCnu D vlo vhi))) *
          Real.sqrt (Real.exp (-(krKappa D vlo vhi * (k / 4 : ℕ) / w ^ 2)) *
            (∫ y, krDens (Icc 0 w) ν f β a' (m + 1) x y ^ 2) /
              (killCnu D vlo vhi * (k / 4 : ℕ)))) ∧
      Real.sqrt (∫ y, r y ^ 2) ≤ Real.sqrt (1 - killCnu D vlo vhi) ^ (k / 2) *
        Real.sqrt (Real.exp (-(krKappa D vlo vhi * (k / 4 : ℕ) / w ^ 2)) *
          (∫ y, krDens (Icc 0 w) ν f β a' (m + 1) x y ^ 2) /
            (killCnu D vlo vhi * (k / 4 : ℕ))) := by
  obtain ⟨G, R, hq, hGR, hG, hR⟩ := krDens_long_decomposition ν H m k hk x
  obtain ⟨g, r, hg, hg1, hg2, hr, hr1, hr2, hs, hsum, hvar, hnorm⟩ :=
    kBV_decomposition_real_representatives
      (measurable_krDens_right ν H.hJ H.hf β a' (m + 1 + k) x)
      (kr_integrable_krDens_right ν H.hJ H.hJfin H.hf H.hf0 H.hfD _ x)
      hq (fun y hy => krDens_eq_zero_of_right_notMem ν hy _ x) hGR hG
  refine ⟨g, r, hg, hg1, hg2, hr, hr1, hr2, hs, hsum, hvar, ?_⟩
  exact (Real.sqrt_le_sqrt hnorm).trans
    (by simpa only [Real.sqrt_sq (norm_nonneg R)] using hR)

end

end PGM
