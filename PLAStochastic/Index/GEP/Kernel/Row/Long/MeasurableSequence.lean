import PLAStochastic.Index.GEP.Kernel.Row.Long.MeasurableGreen
import PLAStochastic.Index.GEP.Kernel.Row.Long.AbsoluteBudget

/-!
# A jointly measurable decomposition of every actual long row

The family is chosen at each discrete length, with joint measurability retained
in the slope parameter and spatial coordinate. Its absolute weighted budgets
are independent of any reward later assigned to a pair of lengths.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X] [Nonempty X]
variable {D θ vlo vhi K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
variable {a β a' : X → ℝ}

theorem krDens_measurable_row_decomposition (hβ : Measurable β) (ha' : Measurable a')
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) (β p) (a' p))
    {b : ℝ} (hb : b = 0 ∨ b = w) {n : ℕ} (hn : 13 ≤ n) :
    ∃ G R : X → ℝ → ℂ,
      Measurable (fun p : X × ℝ => G p.1 p.2) ∧
      Measurable (fun p : X × ℝ => R p.1 p.2) ∧
      (∀ p x, x ∉ Icc 0 w → G p x = 0 ∧ R p x = 0) ∧
      (∀ p x, (krDens (Icc 0 w) ν f (β p) (a' p) n b x : ℂ) = G p x + R p x) ∧
      (∀ p, eVariationOn (G p) univ ≤ ENNReal.ofReal (krRowVarBudget D K L vlo vhi w A n)) ∧
      (∀ p, ∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖G p x - G p y‖ ≤
        (2 * D * krRowVarBudget D K L vlo vhi w A n) * |x-y|) ∧
      (∀ p x, ‖R p x‖ ≤ 4 * krRowRemBudget D K L vlo vhi A n) := by
  classical
  have H₀ := H (Classical.choice ‹Nonempty X›)
  have hV : 0 ≤ krRowVarBudget D K L vlo vhi w A n :=
    mul_nonneg (mul_nonneg (mul_nonneg H₀.classConsts.2.2.2.2.le (Real.sqrt_nonneg _))
      (by linarith [H₀.hA])) (krVarTerm_nonneg H₀.hw0 _)
  have hR : 0 ≤ krRowRemBudget D K L vlo vhi A n :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (mul_nonneg H₀.classConsts.2.2.2.1.le (Real.sqrt_nonneg _))
        (by linarith [H₀.hA])) (pow_nonneg H₀.classConsts.1 _))
  apply kr_measurable_bv_decomposition (le_trans zero_le_one H₀.hw)
    (mul_nonneg (by linarith [H₀.hD0]) hV) hR
  · exact Complex.measurable_ofReal.comp
      (measurable_krDens_param ν measurableSet_Icc H₀.hf (hβ.comp measurable_fst)
        (ha'.comp measurable_fst) measurable_const measurable_snd n)
  · intro p x hx
    rw [krDens_eq_zero_of_right_notMem ν hx, Complex.ofReal_zero]
  · intro p
    obtain ⟨g, r, _, _, hs, he, hv, hl, hr⟩ := krDens_row_decomposition ν (H p) hb hn
    refine ⟨g, fun x hx => (hs x hx).1, hv, hl, ?_⟩
    intro x
    rw [he, add_sub_cancel_left]
    exact hr x

/-- A single family of actual rows, retaining each time index before any reward is applied. -/
theorem krDens_measurable_long_sequence (hβ : Measurable β) (ha' : Measurable a')
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) (β p) (a' p))
    {b : ℝ} (hb : b = 0 ∨ b = w) {P : ℕ} (hP : 12 ≤ P) :
    ∃ G R : ℕ → X → ℝ → ℂ,
      (∀ i, Measurable (fun p : X × ℝ => G i p.1 p.2)) ∧
      (∀ i, Measurable (fun p : X × ℝ => R i p.1 p.2)) ∧
      (∀ i p x, x ∉ Icc 0 w → G i p x = 0 ∧ R i p x = 0) ∧
      (∀ i p x, (krDens (Icc 0 w) ν f (β p) (a' p) (P+1+i) b x : ℂ) =
        G i p x + R i p x) ∧
      (∀ i p, eVariationOn (G i p) univ ≤
        ENNReal.ofReal (krRowVarBudget D K L vlo vhi w A (P+1+i))) ∧
      (∀ i p, ∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖G i p x-G i p y‖ ≤
        (2 * D * krRowVarBudget D K L vlo vhi w A (P+1+i)) * |x-y|) ∧
      (∀ i p x, ‖R i p x‖ ≤ 4 * krRowRemBudget D K L vlo vhi A (P+1+i)) ∧
      (∀ i p x, ‖G i p x‖ ≤ krRowVarBudget D K L vlo vhi w A (P+1+i)) := by
  classical
  have hd := fun i : ℕ => krDens_measurable_row_decomposition ν hβ ha' H hb
    (n := P+1+i) (by omega)
  choose G R hG hR hs he hv hl hr using hd
  refine ⟨G, R, hG, hR, hs, he, hv, hl, hr, ?_⟩
  intro i p x
  have hV0 : 0 ≤ krRowVarBudget D K L vlo vhi w A (P+1+i) :=
    mul_nonneg (mul_nonneg (mul_nonneg (H p).classConsts.2.2.2.2.le (Real.sqrt_nonneg _))
      (by linarith [(H p).hA])) (krVarTerm_nonneg (H p).hw0 _)
  have hgv : BoundedVariationOn (G i p) univ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hv i p)
  have hd := hgv.dist_le (mem_univ x) (mem_univ (-1 : ℝ))
  have hbnd := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hv i p)
  rw [ENNReal.toReal_ofReal hV0] at hbnd
  rw [(hs i p (-1) (by simp)).1, dist_zero_right] at hd
  exact hd.trans hbnd

end
end PGM
