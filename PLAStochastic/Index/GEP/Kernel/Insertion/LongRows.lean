import PLAStochastic.Index.GEP.Kernel.Row.Long.MeasurableSequence
import PLAStochastic.Index.GEP.Kernel.Row.Long.SupBudget
import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FullDensity
import PLAStochastic.Index.GEP.Kernel.Marked.CorrelationSplit

/-!
# Actual positive-left, long-right insertion rows

Each pair of lengths keeps its own jointly measurable regular part. Thus the
regularity bounds can be summed after multiplication by a signed reward of the
total length, without requiring a factorization of that reward.
-/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

theorem measurable_kernelCorrelation_param {X : Type*} [MeasurableSpace X]
    {F G : X → ℝ → ℂ} {d : X → ℝ}
    (hF : Measurable fun p : X × ℝ => F p.1 p.2)
    (hG : Measurable fun p : X × ℝ => G p.1 p.2) (hd : Measurable d) :
    Measurable fun p => kernelCorrelation (F p) (G p) (d p) := by
  have hm : Measurable (fun p : X × ℝ => F p.1 p.2 * G p.1 (p.2+d p.1)) :=
    hF.mul (hG.comp (measurable_fst.prodMk (measurable_snd.add (hd.comp measurable_fst))))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem kr_integrable_of_band_support {w B : ℝ} {g : ℝ → ℂ}
    (hg : Measurable g) (hs : ∀ x, x ∉ Icc 0 w → g x=0) (hB : ∀ x, ‖g x‖ ≤ B) :
    Integrable g := by
  have hi : IntegrableOn (fun _ : ℝ => B) (Icc 0 w) := integrableOn_const (by simp)
  have hgi : IntegrableOn g (Icc 0 w) :=
    hi.mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  exact hgi.integrable_of_forall_notMem_eq_zero hs

variable {X : Type*} [MeasurableSpace X] [Nonempty X]
variable {D θ vlo vhi K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
variable {a β a' : X → ℝ}

set_option maxHeartbeats 400000 in
theorem krInsertion_long_right_family (hβ : Measurable β) (ha' : Measurable a')
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) (β p) (a' p))
    {b c : ℝ} (hb : b=0 ∨ b=w) (hc : c=0 ∨ c=w) {P : ℕ} (hP : 12 ≤ P) :
    ∃ G R : ℕ → ℕ → X → ℝ → ℂ,
      (∀ l i, Measurable (fun p : X × ℝ => G l i p.1 p.2)) ∧
      (∀ l i, Measurable (fun p : X × ℝ => R l i p.1 p.2)) ∧
      (∀ l i p x, (kernelMarkedFullDens (Icc 0 w) ν f (β p) (a' p) x
        (l+1) (P+1+i) b c : ℂ) = G l i p x + R l i p x) ∧
      (∀ l i p x y, ‖G l i p x-G l i p y‖ ≤
        (2 * krRowVarBudget D K L vlo vhi w A (P+1+i) *
          krRowSupBudget D K L vlo vhi w A (l+1)) * |x-y|) ∧
      (∀ l i p x, ‖R l i p x‖ ≤
        (4 * krRowRemBudget D K L vlo vhi A (P+1+i)) *
          krSurv (Icc 0 w) (ν : Measure ℝ) (β p) (a' p) (l+1) b) ∧
      (∀ l i p x, ‖G l i p x‖ ≤ krRowVarBudget D K L vlo vhi w A (P+1+i) *
          krSurv (Icc 0 w) (ν : Measure ℝ) (β p) (a' p) (l+1) b) := by
  classical
  obtain ⟨g, r, hg, hr, hs, he, hv, _, hrem, hsup⟩ :=
    krDens_measurable_long_sequence ν hβ.neg ha'.neg (fun p => (H p).rev) hc hP
  let F : ℕ → X → ℝ → ℂ := fun l p =>
    kernelComplexRow (Icc 0 w) ν f (β p) (a' p) (l+1) b
  let G : ℕ → ℕ → X → ℝ → ℂ := fun l i p x =>
    kernelCorrelation (F l p) (g i p) (β p-a' p*x)
  let R : ℕ → ℕ → X → ℝ → ℂ := fun l i p x =>
    kernelCorrelation (F l p) (r i p) (β p-a' p*x)
  have H₀ := H (Classical.choice ‹Nonempty X›)
  have hF : ∀ l, Measurable (fun p : X × ℝ => F l p.1 p.2) := fun l =>
    Complex.measurable_ofReal.comp (measurable_krDens_param ν measurableSet_Icc H₀.hf
      (hβ.comp measurable_fst) (ha'.comp measurable_fst) measurable_const measurable_snd (l+1))
  have hgM : ∀ i p, Measurable (g i p) := fun i p =>
    (hg i).comp (measurable_const.prodMk measurable_id)
  have hrM : ∀ i p, Measurable (r i p) := fun i p =>
    (hr i).comp (measurable_const.prodMk measurable_id)
  have hFM : ∀ l p, Measurable (F l p) := fun l p =>
    measurable_kernelComplexRow (H p).hJ ν (H p).hf (β p) (a' p) (l+1) b
  have hFI : ∀ l p, Integrable (F l p) := fun l p =>
    integrable_kernelComplexRow (H p).hJ (H p).hJfin ν (H p).hf (H p).hf0
      (H p).hfD (β p) (a' p) (l+1) b
  have hGI : ∀ i p, Integrable (g i p) := fun i p =>
    kr_integrable_of_band_support (hgM i p) (fun x hx => (hs i p x hx).1) (hsup i p)
  have hGV : ∀ i p, BoundedVariationOn (g i p) univ := fun i p =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hv i p)
  have hFB : ∀ l p u, ‖F l p u‖ ≤ krRowSupBudget D K L vlo vhi w A (l+1) := by
    intro l p u
    simpa only [F, kernelComplexRow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (krDens_nonneg ν (H p).hf0 _ _ _)] using
        krDens_le_rowSupBudget ν (H p) hb (by omega : 1 ≤ l+1) u
  have hnorm : ∀ l p, (∫ u, ‖F l p u‖) =
      krSurv (Icc 0 w) (ν : Measure ℝ) (β p) (a' p) (l+1) b := fun l p =>
    kernelComplexRow_norm_integral (H p).hJ (H p).hJfin ν (H p).hf (H p).hf0
      (H p).hfD (H p).hνf (H p).ha' (β p) l b
  have hGM : ∀ l i, Measurable (fun p : X × ℝ => G l i p.1 p.2) := by
    intro l i
    exact measurable_kernelCorrelation_param
      ((hF l).comp (show Measurable (fun q : (X × ℝ) × ℝ => (q.1.1, q.2)) from
        measurable_fst.fst.prodMk measurable_snd))
      ((hg i).comp (show Measurable (fun q : (X × ℝ) × ℝ => (q.1.1, q.2)) from
        measurable_fst.fst.prodMk measurable_snd))
      ((hβ.comp measurable_fst).sub ((ha'.comp measurable_fst).mul measurable_snd))
  have hRM : ∀ l i, Measurable (fun p : X × ℝ => R l i p.1 p.2) := by
    intro l i
    exact measurable_kernelCorrelation_param
      ((hF l).comp (show Measurable (fun q : (X × ℝ) × ℝ => (q.1.1, q.2)) from
        measurable_fst.fst.prodMk measurable_snd))
      ((hr i).comp (show Measurable (fun q : (X × ℝ) × ℝ => (q.1.1, q.2)) from
        measurable_fst.fst.prodMk measurable_snd))
      ((hβ.comp measurable_fst).sub ((ha'.comp measurable_fst).mul measurable_snd))
  refine ⟨G, R, hGM, hRM, ?_, ?_, ?_, ?_⟩
  · intro l i p x
    have hidx : P+1+i = (P+i)+1 := by omega
    rw [hidx]
    change (kernelMarkedDens (Icc 0 w) ν f (β p) (a' p) x (l+1) ((P+i)+1) b c : ℂ) = _
    rw [kernelMarkedDens_eq_correlation (H p).hJ (H p).hJfin ν
      (H p).hf (H p).hf0 (H p).hfD (H p).hνf (H p).ha']
    apply kernelCorrelation_split_right (hFM l p) (hFI l p) (hFB l p)
      (hGI i p) (hrM i p) (hrem i p)
    intro u
    simpa only [kernelComplexRow, hidx, Pi.neg_apply] using he i p u
  · intro l i p x y
    have hV0 : 0 ≤ krRowVarBudget D K L vlo vhi w A (P+1+i) :=
      (norm_nonneg (g i p 0)).trans (hsup i p 0)
    have hbnd := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hv i p)
    rw [ENNReal.toReal_ofReal hV0] at hbnd
    have ha2 : |a' p| ≤ 2 := by rw [(H p).habs]; exact (H p).ha₂
    refine (kernelCorrelation_affine_lip_right (hFM l p) (hFB l p)
      (hGV i p) (hGI i p) (β p) (a' p) x y).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul ha2 hbnd ENNReal.toReal_nonneg (by norm_num))
        (krRowSupBudget_nonneg ν (H p) (l+1))) (abs_nonneg _)
  · intro l i p x
    have h := kernelCorrelation_norm_le_left (hFI l p) (hrem i p) (β p-a' p*x)
    rwa [hnorm l p] at h
  · intro l i p x
    have h := kernelCorrelation_norm_le_left (hFI l p) (hsup i p) (β p-a' p*x)
    rwa [hnorm l p] at h

/-- Reversal also preserves the marked coordinate and reverses the pair of lengths. -/
theorem kernelMarkedFullDens_pos_symm {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β x : ℝ) (l r : ℕ) (y z : ℝ) :
    kernelMarkedFullDens J ν f β a x (l+1) (r+1) y z =
      kernelMarkedFullDens J ν f (-β) (-a) x (r+1) (l+1) z y := by
  apply Complex.ofReal_injective
  simp only [kernelMarkedFullDens]
  rw [kernelMarkedDens_eq_correlation hJ hJfin ν hf hf0 hfD hν ha,
    kernelMarkedDens_eq_correlation hJ hJfin ν hf hf0 hfD hν (neg_ne_zero.mpr ha)]
  simp only [neg_neg]
  rw [kernelCorrelation_flip]
  congr 1
  ring

set_option maxHeartbeats 400000 in
theorem krInsertion_long_left_family (hβ : Measurable β) (ha' : Measurable a')
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) (β p) (a' p))
    {b c : ℝ} (hb : b=0 ∨ b=w) (hc : c=0 ∨ c=w) {P : ℕ} (hP : 12 ≤ P) :
    ∃ G R : ℕ → ℕ → X → ℝ → ℂ,
      (∀ l i, Measurable (fun p : X × ℝ => G l i p.1 p.2)) ∧
      (∀ l i, Measurable (fun p : X × ℝ => R l i p.1 p.2)) ∧
      (∀ l i p x, (kernelMarkedFullDens (Icc 0 w) ν f (β p) (a' p) x
        (P+1+i) (l+1) b c : ℂ) = G l i p x + R l i p x) ∧
      (∀ l i p x y, ‖G l i p x-G l i p y‖ ≤
        (2 * krRowVarBudget D K L vlo vhi w A (P+1+i) *
          krRowSupBudget D K L vlo vhi w A (l+1)) * |x-y|) ∧
      (∀ l i p x, ‖R l i p x‖ ≤
        (4 * krRowRemBudget D K L vlo vhi A (P+1+i)) *
          krSurv (Icc 0 w) (ν : Measure ℝ) (-β p) (-a' p) (l+1) c) ∧
      (∀ l i p x, ‖G l i p x‖ ≤ krRowVarBudget D K L vlo vhi w A (P+1+i) *
          krSurv (Icc 0 w) (ν : Measure ℝ) (-β p) (-a' p) (l+1) c) := by
  obtain ⟨G, R, hG, hR, he, hl, hr, hbnd⟩ :=
    krInsertion_long_right_family ν hβ.neg ha'.neg (fun p => (H p).rev) hc hb hP
  refine ⟨G, R, hG, hR, ?_, hl, hr, hbnd⟩
  intro l i p x
  have hi : P+1+i = (P+i)+1 := by omega
  rw [hi, kernelMarkedFullDens_pos_symm (H p).hJ (H p).hJfin ν
    (H p).hf (H p).hf0 (H p).hfD (H p).hνf (H p).ha']
  simpa only [hi, Pi.neg_apply] using he l i p x

end
end PGM
