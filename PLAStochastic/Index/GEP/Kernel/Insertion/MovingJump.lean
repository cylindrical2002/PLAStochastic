import PLAStochastic.Index.GEP.Kernel.Row.Long.MeasurableSequence
import PLAStochastic.Index.GEP.Kernel.Marked.ZeroSide
import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FullDensity

/-!
# Retaining the actual moving endpoint trace

Clipping the regular row inside its fixed band gives a globally Lipschitz
function. The omitted endpoint value is recorded as the jump coefficient.
The identities exclude the single crossing slope; no trace is silently erased.
-/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

def krClippedRegular {w : ℝ} (hw : 0 ≤ w) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  g (projIcc 0 w hw x)

theorem krClippedRegular_lip {w L : ℝ} (hw : 0 ≤ w) (hL : 0 ≤ L) {g : ℝ → ℂ}
    (hg : ∀ u ∈ Icc 0 w, ∀ v ∈ Icc 0 w, ‖g u-g v‖ ≤ L*|u-v|) (x y : ℝ) :
    ‖krClippedRegular hw g x-krClippedRegular hw g y‖ ≤ L*|x-y| := by
  have hc := LipschitzWith.projIcc hw
  have hd : |(projIcc 0 w hw x : ℝ)-(projIcc 0 w hw y : ℝ)| ≤ |x-y| := by
    simpa only [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using hc.dist_le_mul x y
  exact (hg _ (projIcc 0 w hw x).property _ (projIcc 0 w hw y).property).trans
    (mul_le_mul_of_nonneg_left hd hL)

theorem krRegular_lower_jump {w : ℝ} (hw : 0 ≤ w) {g : ℝ → ℂ}
    (hs : ∀ x, x ∉ Icc 0 w → g x=0) {u : ℝ} (hu : u ≤ w) (hu0 : u ≠ 0) :
    g u = (krClippedRegular hw g u-g 0) + (if 0 < u then g 0 else 0) := by
  by_cases h : 0 < u
  · rw [if_pos h]
    have hm : u ∈ Icc 0 w := ⟨h.le, hu⟩
    simp only [krClippedRegular, projIcc_of_mem hw hm]
    ring
  · have hn : u < 0 := lt_of_le_of_ne (le_of_not_gt h) hu0
    rw [if_neg h, hs u (fun hu => (not_le_of_gt hn) hu.1)]
    simp only [krClippedRegular, projIcc_of_le_left hw hn.le]
    simp

theorem krRegular_upper_jump {w : ℝ} (hw : 0 ≤ w) {g : ℝ → ℂ}
    (hs : ∀ x, x ∉ Icc 0 w → g x=0) {u : ℝ} (hu : 0 ≤ u) (huw : u ≠ w) :
    g u = (krClippedRegular hw g u-g w) + (if u < w then g w else 0) := by
  by_cases h : u < w
  · rw [if_pos h]
    have hm : u ∈ Icc 0 w := ⟨hu, h.le⟩
    simp only [krClippedRegular, projIcc_of_mem hw hm]
    ring
  · have hn : w < u := lt_of_le_of_ne (le_of_not_gt h) huw.symm
    rw [if_neg h, hs u (fun hu => (not_le_of_gt hn) hu.2)]
    simp only [krClippedRegular, projIcc_of_right_le hw hn.le]
    simp

theorem krRegular_lower_jump_complement {w : ℝ} (hw : 0 ≤ w) {g : ℝ → ℂ}
    (hs : ∀ x, x ∉ Icc 0 w → g x=0) {u : ℝ} (hu : u ≤ w) (hu0 : u ≠ 0) :
    g u = krClippedRegular hw g u + (if u < 0 then -g 0 else 0) := by
  have h := krRegular_lower_jump hw hs hu hu0
  by_cases hp : 0 < u
  · simp only [if_pos hp, if_neg (not_lt_of_ge hp.le)] at h ⊢
    linear_combination h
  · have hn : u < 0 := lt_of_le_of_ne (le_of_not_gt hp) hu0
    simp only [if_neg hp, if_pos hn] at h ⊢
    linear_combination h

theorem krRegular_upper_jump_complement {w : ℝ} (hw : 0 ≤ w) {g : ℝ → ℂ}
    (hs : ∀ x, x ∉ Icc 0 w → g x=0) {u : ℝ} (hu : 0 ≤ u) (huw : u ≠ w) :
    g u = krClippedRegular hw g u + (if w < u then -g w else 0) := by
  have h := krRegular_upper_jump hw hs hu huw
  by_cases hp : u < w
  · simp only [if_pos hp, if_neg (not_lt_of_ge hp.le)] at h ⊢
    linear_combination h
  · have hn : w < u := lt_of_le_of_ne (le_of_not_gt hp) huw.symm
    simp only [if_neg hp, if_pos hn] at h ⊢
    linear_combination h

set_option maxHeartbeats 600000 in
/-- The actual up-crossing insertion with no random steps before the mark. -/
theorem krInsertion_zero_left_up_long {X : Type*} [MeasurableSpace X] [Nonempty X]
    {D θ vlo vhi K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {a : X → ℝ} (ha : Measurable a) (ha0 : ∀ p, 0 ≤ a p)
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) 1 (a p))
    {n : ℕ} (hn : 12 ≤ n) :
    ∃ h r : X → ℝ → ℂ, ∃ j : X → ℂ,
      Measurable (fun p : X × ℝ => h p.1 p.2) ∧
      Measurable (fun p : X × ℝ => r p.1 p.2) ∧ Measurable j ∧
      (∀ p x, 0 ≤ x → a p*x ≠ 1 →
        (kernelMarkedFullDens (Icc 0 w) ν f 1 (a p) x 0 (n+1) 0 w : ℂ) =
          h p x + (if a p*x < 1 then j p else 0) + r p x) ∧
      (∀ p x y, ‖h p x-h p y‖ ≤
        (4*D*krRowVarBudget D K L vlo vhi w A (n+1))*|x-y|) ∧
      (∀ p x, ‖r p x‖ ≤ 4*krRowRemBudget D K L vlo vhi A (n+1)) ∧
      (∀ p, ‖j p‖ ≤ krDens (Icc 0 w) ν f (-1) (-a p) (n+1) w 0 +
        4*krRowRemBudget D K L vlo vhi A (n+1)) ∧
      (∀ p x, ‖h p x‖ ≤ 2*krRowVarBudget D K L vlo vhi w A (n+1)) := by
  classical
  have H₀ := H (Classical.choice ‹Nonempty X›)
  have hw : 0 ≤ w := le_trans zero_le_one H₀.hw
  obtain ⟨g, e, hg, he, hs, hsum, hvar, hl, herr⟩ :=
    krDens_measurable_row_decomposition ν measurable_const ha.neg
      (fun p => (H p).rev) (Or.inr rfl) (n := n+1) (by omega)
  simp only [Pi.neg_apply] at hsum
  let h : X → ℝ → ℂ := fun p x => krClippedRegular hw (g p) (1-a p*x)-g p 0
  let r : X → ℝ → ℂ := fun p x => e p (1-a p*x)
  let j : X → ℂ := fun p => g p 0
  have hclip : Measurable (fun p : X × ℝ => krClippedRegular hw (g p.1) (1-a p.1*p.2)) := by
    exact hg.comp (measurable_fst.prodMk (measurable_subtype_coe.comp
      ((continuous_projIcc (h := hw)).measurable.comp
        (measurable_const.sub ((ha.comp measurable_fst).mul measurable_snd)))))
  have hj : Measurable j := hg.comp (measurable_id.prodMk measurable_const)
  have hh : Measurable (fun p : X × ℝ => h p.1 p.2) := hclip.sub (hj.comp measurable_fst)
  have hr : Measurable (fun p : X × ℝ => r p.1 p.2) :=
    he.comp (measurable_fst.prodMk (measurable_const.sub ((ha.comp measurable_fst).mul measurable_snd)))
  refine ⟨h, r, j, hh, hr, hj, ?_, ?_, fun p x => herr p _, ?_, ?_⟩
  · intro p x hx hcross
    have hm : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw⟩
    simp only [kernelMarkedFullDens, indicator_of_mem hm, one_mul, zero_add]
    rw [krDens_symm ν (H p).hJ (H p).hJfin (H p).hf (H p).hf0 (H p).hfD
      (H p).hνf (H p).ha' n]
    rw [hsum p (1-a p*x)]
    have hbound : 1-a p*x ≤ w := by nlinarith [mul_nonneg (ha0 p) hx, H₀.hw]
    have hnon : 1-a p*x ≠ 0 := by intro hz; apply hcross; linarith
    rw [krRegular_lower_jump hw (fun u hu => (hs p u hu).1) hbound hnon]
    have hi : 0 < 1-a p*x ↔ a p*x < 1 := by constructor <;> intro ht <;> linarith
    simp only [h, r, j, hi]
  · intro p x y
    have hV0 : 0 ≤ krRowVarBudget D K L vlo vhi w A (n+1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (H p).classConsts.2.2.2.2.le (Real.sqrt_nonneg _))
        (by linarith [(H p).hA])) (krVarTerm_nonneg (H p).hw0 _)
    have hL0 : 0 ≤ 2*D*krRowVarBudget D K L vlo vhi w A (n+1) :=
      mul_nonneg (by linarith [(H p).hD0]) hV0
    have hb := krClippedRegular_lip hw hL0 (hl p) (1-a p*x) (1-a p*y)
    have hd : (1-a p*x)-(1-a p*y) = -a p*(x-y) := by ring
    rw [hd, abs_mul, abs_neg] at hb
    have ha2 := (H p).ha₂
    calc
      ‖h p x-h p y‖ = ‖krClippedRegular hw (g p) (1-a p*x)-krClippedRegular hw (g p) (1-a p*y)‖ := by
        congr 1
        dsimp only [h]
        ring
      _ ≤ (2*D*krRowVarBudget D K L vlo vhi w A (n+1))*(|a p| *|x-y|) := hb
      _ ≤ (2*D*krRowVarBudget D K L vlo vhi w A (n+1))*(2*|x-y|) := by gcongr
      _ = _ := by ring
  · intro p
    have hid := hsum p 0
    have hq0 := krDens_nonneg (J := Icc 0 w) ν (H p).hf0 (β := (-1 : ℝ)) (a := -a p) (n+1) w 0
    have hjid : j p = (krDens (Icc 0 w) ν f (-1) (-a p) (n+1) w 0 : ℂ)-e p 0 := by
      dsimp only [j]
      rw [hid]
      ring
    rw [hjid]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (herr p 0))
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0, le_refl]
  · intro p x
    have hV0 : 0 ≤ krRowVarBudget D K L vlo vhi w A (n+1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (H p).classConsts.2.2.2.2.le (Real.sqrt_nonneg _))
        (by linarith [(H p).hA])) (krVarTerm_nonneg (H p).hw0 _)
    have hsup : ∀ u, ‖g p u‖ ≤ krRowVarBudget D K L vlo vhi w A (n+1) := by
      intro u
      have hgv : BoundedVariationOn (g p) univ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hvar p)
      have hd := hgv.dist_le (mem_univ u) (mem_univ (-1 : ℝ))
      have hbnd := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvar p)
      rw [ENNReal.toReal_ofReal hV0] at hbnd
      rw [(hs p (-1) (by simp)).1, dist_zero_right] at hd
      exact hd.trans hbnd
    dsimp only [h, krClippedRegular]
    exact (norm_sub_le _ _).trans ((add_le_add (hsup _) (hsup _)).trans_eq (by ring))


set_option maxHeartbeats 600000 in
/-- The actual up-crossing insertion with no random steps after the mark. -/
theorem krInsertion_zero_right_up_long {X : Type*} [MeasurableSpace X] [Nonempty X]
    {D θ vlo vhi K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {a : X → ℝ} (ha : Measurable a) (ha0 : ∀ p, 0 ≤ a p)
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) 1 (a p))
    {n : ℕ} (hn : 12 ≤ n) :
    ∃ h r : X → ℝ → ℂ, ∃ j : X → ℂ,
      Measurable (fun p : X × ℝ => h p.1 p.2) ∧
      Measurable (fun p : X × ℝ => r p.1 p.2) ∧ Measurable j ∧
      (∀ p x, 0 ≤ x → a p*x ≠ 1 →
        (kernelMarkedFullDens (Icc 0 w) ν f 1 (a p) x (n+1) 0 0 w : ℂ) =
          h p x + (if a p*x < 1 then j p else 0) + r p x) ∧
      (∀ p x y, ‖h p x-h p y‖ ≤
        (4*D*krRowVarBudget D K L vlo vhi w A (n+1))*|x-y|) ∧
      (∀ p x, ‖r p x‖ ≤ 4*krRowRemBudget D K L vlo vhi A (n+1)) ∧
      (∀ p, ‖j p‖ ≤ krDens (Icc 0 w) ν f 1 (a p) (n+1) 0 w +
        4*krRowRemBudget D K L vlo vhi A (n+1)) ∧
      (∀ p x, ‖h p x‖ ≤ 2*krRowVarBudget D K L vlo vhi w A (n+1)) := by
  classical
  have H₀ := H (Classical.choice ‹Nonempty X›)
  have hw : 0 ≤ w := le_trans zero_le_one H₀.hw
  obtain ⟨g, e, hg, he, hs, hsum, hvar, hl, herr⟩ :=
    krDens_measurable_row_decomposition ν measurable_const ha
      H (Or.inl rfl) (n := n+1) (by omega)
  let h : X → ℝ → ℂ := fun p x => krClippedRegular hw (g p) (w-1+a p*x)-g p w
  let r : X → ℝ → ℂ := fun p x => e p (w-1+a p*x)
  let j : X → ℂ := fun p => g p w
  have hclip : Measurable (fun p : X × ℝ => krClippedRegular hw (g p.1) (w-1+a p.1*p.2)) := by
    exact hg.comp (measurable_fst.prodMk (measurable_subtype_coe.comp
      ((continuous_projIcc (h := hw)).measurable.comp
        (measurable_const.add ((ha.comp measurable_fst).mul measurable_snd)))))
  have hj : Measurable j := hg.comp (measurable_id.prodMk measurable_const)
  have hh : Measurable (fun p : X × ℝ => h p.1 p.2) := hclip.sub (hj.comp measurable_fst)
  have hr : Measurable (fun p : X × ℝ => r p.1 p.2) :=
    he.comp (measurable_fst.prodMk (measurable_const.add ((ha.comp measurable_fst).mul measurable_snd)))
  refine ⟨h, r, j, hh, hr, hj, ?_, ?_, fun p x => herr p _, ?_, ?_⟩
  · intro p x hx hcross
    have hm : w ∈ Icc 0 w := ⟨hw, le_rfl⟩
    simp only [kernelMarkedFullDens, indicator_of_mem hm, mul_one]
    rw [hsum p (w-1+a p*x)]
    have hbound : 0 ≤ w-1+a p*x := by nlinarith [mul_nonneg (ha0 p) hx, H₀.hw]
    have hnon : w-1+a p*x ≠ w := by intro hz; apply hcross; linarith
    rw [krRegular_upper_jump hw (fun u hu => (hs p u hu).1) hbound hnon]
    have hi : w-1+a p*x < w ↔ a p*x < 1 := by constructor <;> intro ht <;> linarith
    simp only [h, r, j, hi]
  · intro p x y
    have hV0 : 0 ≤ krRowVarBudget D K L vlo vhi w A (n+1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (H p).classConsts.2.2.2.2.le (Real.sqrt_nonneg _))
        (by linarith [(H p).hA])) (krVarTerm_nonneg (H p).hw0 _)
    have hL0 : 0 ≤ 2*D*krRowVarBudget D K L vlo vhi w A (n+1) :=
      mul_nonneg (by linarith [(H p).hD0]) hV0
    have hb := krClippedRegular_lip hw hL0 (hl p) (w-1+a p*x) (w-1+a p*y)
    have hd : (w-1+a p*x)-(w-1+a p*y) = a p*(x-y) := by ring
    rw [hd, abs_mul] at hb
    have ha2 := (H p).ha₂
    calc
      ‖h p x-h p y‖ = ‖krClippedRegular hw (g p) (w-1+a p*x)-krClippedRegular hw (g p) (w-1+a p*y)‖ := by
        congr 1
        dsimp only [h]
        ring
      _ ≤ (2*D*krRowVarBudget D K L vlo vhi w A (n+1))*(|a p| *|x-y|) := hb
      _ ≤ (2*D*krRowVarBudget D K L vlo vhi w A (n+1))*(2*|x-y|) := by gcongr
      _ = _ := by ring
  · intro p
    have hid := hsum p w
    have hq0 := krDens_nonneg (J := Icc 0 w) ν (H p).hf0 (β := (1 : ℝ)) (a := a p) (n+1) 0 w
    have hjid : j p = (krDens (Icc 0 w) ν f 1 (a p) (n+1) 0 w : ℂ)-e p w := by
      dsimp only [j]
      rw [hid]
      ring
    rw [hjid]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (herr p w))
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0, le_refl]
  · intro p x
    have hV0 : 0 ≤ krRowVarBudget D K L vlo vhi w A (n+1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (H p).classConsts.2.2.2.2.le (Real.sqrt_nonneg _))
        (by linarith [(H p).hA])) (krVarTerm_nonneg (H p).hw0 _)
    have hsup : ∀ u, ‖g p u‖ ≤ krRowVarBudget D K L vlo vhi w A (n+1) := by
      intro u
      have hgv : BoundedVariationOn (g p) univ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hvar p)
      have hd := hgv.dist_le (mem_univ u) (mem_univ (-1 : ℝ))
      have hbnd := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvar p)
      rw [ENNReal.toReal_ofReal hV0] at hbnd
      rw [(hs p (-1) (by simp)).1, dist_zero_right] at hd
      exact hd.trans hbnd
    dsimp only [h, krClippedRegular]
    exact (norm_sub_le _ _).trans ((add_le_add (hsup _) (hsup _)).trans_eq (by ring))


set_option maxHeartbeats 600000 in
/-- The actual down-crossing insertion with no random steps before the mark. -/
theorem krInsertion_zero_left_down_long {X : Type*} [MeasurableSpace X] [Nonempty X]
    {D θ vlo vhi K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {a : X → ℝ} (ha : Measurable a)
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) 1 (a p))
    {n : ℕ} (hn : 12 ≤ n) {R : ℝ} (hWR : 2*R ≤ w) :
    ∃ h r : X → ℝ → ℂ, ∃ j : X → ℂ,
      Measurable (fun p : X × ℝ => h p.1 p.2) ∧
      Measurable (fun p : X × ℝ => r p.1 p.2) ∧ Measurable j ∧
      (∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 →
        (kernelMarkedFullDens (Icc 0 w) ν f 1 (a p) x 0 (n+1) w 0 : ℂ) =
          h p x + (if a p*x < 1 then j p else 0) + r p x) ∧
      (∀ p x y, ‖h p x-h p y‖ ≤
        (4*D*krRowVarBudget D K L vlo vhi w A (n+1))*|x-y|) ∧
      (∀ p x, ‖r p x‖ ≤ 4*krRowRemBudget D K L vlo vhi A (n+1)) ∧
      (∀ p, ‖j p‖ ≤ krDens (Icc 0 w) ν f (-1) (-a p) (n+1) 0 w +
        4*krRowRemBudget D K L vlo vhi A (n+1)) ∧
      (∀ p x, ‖h p x‖ ≤ 2*krRowVarBudget D K L vlo vhi w A (n+1)) := by
  classical
  have H₀ := H (Classical.choice ‹Nonempty X›)
  have hw : 0 ≤ w := le_trans zero_le_one H₀.hw
  obtain ⟨g, e, hg, he, hs, hsum, hvar, hl, herr⟩ :=
    krDens_measurable_row_decomposition ν measurable_const ha.neg
      (fun p => (H p).rev) (Or.inl rfl) (n := n+1) (by omega)
  simp only [Pi.neg_apply] at hsum
  let h : X → ℝ → ℂ := fun p x => krClippedRegular hw (g p) (w+1-a p*x)
  let r : X → ℝ → ℂ := fun p x => e p (w+1-a p*x)
  let j : X → ℂ := fun p => -g p w
  have hclip : Measurable (fun p : X × ℝ => krClippedRegular hw (g p.1) (w+1-a p.1*p.2)) := by
    exact hg.comp (measurable_fst.prodMk (measurable_subtype_coe.comp
      ((continuous_projIcc (h := hw)).measurable.comp
        (measurable_const.sub ((ha.comp measurable_fst).mul measurable_snd)))))
  have hj : Measurable j := (hg.comp (show Measurable (fun p : X => (p,w)) from measurable_id.prodMk measurable_const)).neg
  have hh : Measurable (fun p : X × ℝ => h p.1 p.2) := hclip
  have hr : Measurable (fun p : X × ℝ => r p.1 p.2) :=
    he.comp (measurable_fst.prodMk (measurable_const.sub ((ha.comp measurable_fst).mul measurable_snd)))
  refine ⟨h, r, j, hh, hr, hj, ?_, ?_, fun p x => herr p _, ?_, ?_⟩
  · intro p x hx hcross
    have hm : w ∈ Icc 0 w := ⟨hw, le_rfl⟩
    simp only [kernelMarkedFullDens, indicator_of_mem hm, one_mul]
    rw [krDens_symm ν (H p).hJ (H p).hJfin (H p).hf (H p).hf0 (H p).hfD
      (H p).hνf (H p).ha' n]
    rw [hsum p (w+1-a p*x)]
    have ha2 : a p ≤ 2 := (le_abs_self _).trans (H p).ha₂
    have hax : a p*x ≤ 2*R := (mul_le_mul_of_nonneg_right ha2 hx.1).trans (by linarith [hx.2])
    have hbound : 0 ≤ w+1-a p*x := by linarith
    have hnon : w+1-a p*x ≠ w := by intro hz; apply hcross; linarith
    rw [krRegular_upper_jump_complement hw (fun u hu => (hs p u hu).1) hbound hnon]
    have hi : w < w+1-a p*x ↔ a p*x < 1 := by constructor <;> intro ht <;> linarith
    simp only [h, r, j, hi]
  · intro p x y
    have hV0 : 0 ≤ krRowVarBudget D K L vlo vhi w A (n+1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (H p).classConsts.2.2.2.2.le (Real.sqrt_nonneg _))
        (by linarith [(H p).hA])) (krVarTerm_nonneg (H p).hw0 _)
    have hL0 : 0 ≤ 2*D*krRowVarBudget D K L vlo vhi w A (n+1) :=
      mul_nonneg (by linarith [(H p).hD0]) hV0
    have hb := krClippedRegular_lip hw hL0 (hl p) (w+1-a p*x) (w+1-a p*y)
    have hd : (w+1-a p*x)-(w+1-a p*y) = -a p*(x-y) := by ring
    rw [hd, abs_mul, abs_neg] at hb
    have ha2 := (H p).ha₂
    calc
      ‖h p x-h p y‖ = ‖krClippedRegular hw (g p) (w+1-a p*x)-krClippedRegular hw (g p) (w+1-a p*y)‖ := by
        rfl
      _ ≤ (2*D*krRowVarBudget D K L vlo vhi w A (n+1))*(|a p| *|x-y|) := hb
      _ ≤ (2*D*krRowVarBudget D K L vlo vhi w A (n+1))*(2*|x-y|) := by gcongr
      _ = _ := by ring
  · intro p
    have hid := hsum p w
    have hq0 := krDens_nonneg (J := Icc 0 w) ν (H p).hf0 (β := (-1 : ℝ)) (a := -a p) (n+1) 0 w
    have hjid : g p w = (krDens (Icc 0 w) ν f (-1) (-a p) (n+1) 0 w : ℂ)-e p w := by
      rw [hid]
      ring
    change ‖-g p w‖ ≤ _
    rw [norm_neg, hjid]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (herr p w))
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0, le_refl]
  · intro p x
    have hV0 : 0 ≤ krRowVarBudget D K L vlo vhi w A (n+1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (H p).classConsts.2.2.2.2.le (Real.sqrt_nonneg _))
        (by linarith [(H p).hA])) (krVarTerm_nonneg (H p).hw0 _)
    have hsup : ∀ u, ‖g p u‖ ≤ krRowVarBudget D K L vlo vhi w A (n+1) := by
      intro u
      have hgv : BoundedVariationOn (g p) univ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hvar p)
      have hd := hgv.dist_le (mem_univ u) (mem_univ (-1 : ℝ))
      have hbnd := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvar p)
      rw [ENNReal.toReal_ofReal hV0] at hbnd
      rw [(hs p (-1) (by simp)).1, dist_zero_right] at hd
      exact hd.trans hbnd
    dsimp only [h, krClippedRegular]
    exact (hsup _).trans (by linarith)



set_option maxHeartbeats 600000 in
/-- The actual down-crossing insertion with no random steps after the mark. -/
theorem krInsertion_zero_right_down_long {X : Type*} [MeasurableSpace X] [Nonempty X]
    {D θ vlo vhi K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {a : X → ℝ} (ha : Measurable a)
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) 1 (a p))
    {n : ℕ} (hn : 12 ≤ n) {R : ℝ} (hWR : 2*R ≤ w) :
    ∃ h r : X → ℝ → ℂ, ∃ j : X → ℂ,
      Measurable (fun p : X × ℝ => h p.1 p.2) ∧
      Measurable (fun p : X × ℝ => r p.1 p.2) ∧ Measurable j ∧
      (∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 →
        (kernelMarkedFullDens (Icc 0 w) ν f 1 (a p) x (n+1) 0 w 0 : ℂ) =
          h p x + (if a p*x < 1 then j p else 0) + r p x) ∧
      (∀ p x y, ‖h p x-h p y‖ ≤
        (4*D*krRowVarBudget D K L vlo vhi w A (n+1))*|x-y|) ∧
      (∀ p x, ‖r p x‖ ≤ 4*krRowRemBudget D K L vlo vhi A (n+1)) ∧
      (∀ p, ‖j p‖ ≤ krDens (Icc 0 w) ν f 1 (a p) (n+1) w 0 +
        4*krRowRemBudget D K L vlo vhi A (n+1)) ∧
      (∀ p x, ‖h p x‖ ≤ 2*krRowVarBudget D K L vlo vhi w A (n+1)) := by
  classical
  have H₀ := H (Classical.choice ‹Nonempty X›)
  have hw : 0 ≤ w := le_trans zero_le_one H₀.hw
  obtain ⟨g, e, hg, he, hs, hsum, hvar, hl, herr⟩ :=
    krDens_measurable_row_decomposition ν measurable_const ha
      H (Or.inr rfl) (n := n+1) (by omega)
  let h : X → ℝ → ℂ := fun p x => krClippedRegular hw (g p) (-1+a p*x)
  let r : X → ℝ → ℂ := fun p x => e p (-1+a p*x)
  let j : X → ℂ := fun p => -g p 0
  have hclip : Measurable (fun p : X × ℝ => krClippedRegular hw (g p.1) (-1+a p.1*p.2)) := by
    exact hg.comp (measurable_fst.prodMk (measurable_subtype_coe.comp
      ((continuous_projIcc (h := hw)).measurable.comp
        (measurable_const.add ((ha.comp measurable_fst).mul measurable_snd)))))
  have hj : Measurable j := (hg.comp (show Measurable (fun p : X => (p,0)) from measurable_id.prodMk measurable_const)).neg
  have hh : Measurable (fun p : X × ℝ => h p.1 p.2) := hclip
  have hr : Measurable (fun p : X × ℝ => r p.1 p.2) :=
    he.comp (measurable_fst.prodMk (measurable_const.add ((ha.comp measurable_fst).mul measurable_snd)))
  refine ⟨h, r, j, hh, hr, hj, ?_, ?_, fun p x => herr p _, ?_, ?_⟩
  · intro p x hx hcross
    have hm : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw⟩
    simp only [kernelMarkedFullDens, indicator_of_mem hm, mul_one, zero_sub]
    rw [hsum p (-1+a p*x)]
    have ha2 : a p ≤ 2 := (le_abs_self _).trans (H p).ha₂
    have hax : a p*x ≤ 2*R := (mul_le_mul_of_nonneg_right ha2 hx.1).trans (by linarith [hx.2])
    have hbound : -1+a p*x ≤ w := by linarith
    have hnon : -1+a p*x ≠ 0 := by intro hz; apply hcross; linarith
    rw [krRegular_lower_jump_complement hw (fun u hu => (hs p u hu).1) hbound hnon]
    have hi : -1+a p*x < 0 ↔ a p*x < 1 := by constructor <;> intro ht <;> linarith
    simp only [h, r, j, hi]
  · intro p x y
    have hV0 : 0 ≤ krRowVarBudget D K L vlo vhi w A (n+1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (H p).classConsts.2.2.2.2.le (Real.sqrt_nonneg _))
        (by linarith [(H p).hA])) (krVarTerm_nonneg (H p).hw0 _)
    have hL0 : 0 ≤ 2*D*krRowVarBudget D K L vlo vhi w A (n+1) :=
      mul_nonneg (by linarith [(H p).hD0]) hV0
    have hb := krClippedRegular_lip hw hL0 (hl p) (-1+a p*x) (-1+a p*y)
    have hd : (-1+a p*x)-(-1+a p*y) = a p*(x-y) := by ring
    rw [hd, abs_mul] at hb
    have ha2 := (H p).ha₂
    calc
      ‖h p x-h p y‖ = ‖krClippedRegular hw (g p) (-1+a p*x)-krClippedRegular hw (g p) (-1+a p*y)‖ := by
        rfl
      _ ≤ (2*D*krRowVarBudget D K L vlo vhi w A (n+1))*(|a p| *|x-y|) := hb
      _ ≤ (2*D*krRowVarBudget D K L vlo vhi w A (n+1))*(2*|x-y|) := by gcongr
      _ = _ := by ring
  · intro p
    have hid := hsum p 0
    have hq0 := krDens_nonneg (J := Icc 0 w) ν (H p).hf0 (β := (1 : ℝ)) (a := a p) (n+1) w 0
    have hjid : g p 0 = (krDens (Icc 0 w) ν f 1 (a p) (n+1) w 0 : ℂ)-e p 0 := by
      rw [hid]
      ring
    change ‖-g p 0‖ ≤ _
    rw [norm_neg, hjid]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (herr p 0))
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0, le_refl]
  · intro p x
    have hV0 : 0 ≤ krRowVarBudget D K L vlo vhi w A (n+1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (H p).classConsts.2.2.2.2.le (Real.sqrt_nonneg _))
        (by linarith [(H p).hA])) (krVarTerm_nonneg (H p).hw0 _)
    have hsup : ∀ u, ‖g p u‖ ≤ krRowVarBudget D K L vlo vhi w A (n+1) := by
      intro u
      have hgv : BoundedVariationOn (g p) univ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hvar p)
      have hd := hgv.dist_le (mem_univ u) (mem_univ (-1 : ℝ))
      have hbnd := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvar p)
      rw [ENNReal.toReal_ofReal hV0] at hbnd
      rw [(hs p (-1) (by simp)).1, dist_zero_right] at hd
      exact hd.trans hbnd
    dsimp only [h, krClippedRegular]
    exact (hsup _).trans (by linarith)



end
end PGM
