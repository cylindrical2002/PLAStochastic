import PLAStochastic.Index.GEP.Kernel.Marked.CorrelationSplit

/-!
# One-sided marked densities and their retained boundary projections

These formulas use only positive-step density representatives. When the other
side has zero steps, the surviving density is translated and projected. Global
BV is preserved; Lipschitz control is asserted only while both shifted points
remain in the band.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

def kernelProjectedTranslate (J : Set ℝ) (y c a : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  J.indicator (fun _ => g (c+a*t)) y

theorem measurable_kernelProjectedTranslate (J : Set ℝ) (y c a : ℝ)
    {g : ℝ → ℂ} (hg : Measurable g) : Measurable (kernelProjectedTranslate J y c a g) := by
  unfold kernelProjectedTranslate
  by_cases hy : y ∈ J
  · simp only [indicator_of_mem hy]
    fun_prop
  · simp only [indicator_of_notMem hy]
    exact measurable_const

theorem kernelProjectedTranslate_add (J : Set ℝ) (y c a : ℝ)
    (g e : ℝ → ℂ) (t : ℝ) :
    kernelProjectedTranslate J y c a (fun u => g u+e u) t =
      kernelProjectedTranslate J y c a g t + kernelProjectedTranslate J y c a e t := by
  by_cases hy : y ∈ J <;> simp [kernelProjectedTranslate, hy]

theorem kernelProjectedTranslate_norm_le (J : Set ℝ) (y c a : ℝ)
    {e : ℝ → ℂ} {R : ℝ} (hR : ∀ u, ‖e u‖ ≤ R) (t : ℝ) :
    ‖kernelProjectedTranslate J y c a e t‖ ≤ R := by
  by_cases hy : y ∈ J
  · simpa only [kernelProjectedTranslate, indicator_of_mem hy] using hR (c+a*t)
  · simpa only [kernelProjectedTranslate, indicator_of_notMem hy, norm_zero] using
      (norm_nonneg (e 0)).trans (hR 0)

theorem kernelVariation_affine_le (g : ℝ → ℂ) (c a : ℝ) :
    eVariationOn (fun t => g (c+a*t)) univ ≤ eVariationOn g univ := by
  by_cases ha : 0 ≤ a
  · exact eVariationOn.comp_le_of_monotoneOn g (fun t => c+a*t)
      (fun x _ y _ hxy => by dsimp; nlinarith) (fun _ _ => mem_univ _)
  · exact eVariationOn.comp_le_of_antitoneOn g (fun t => c+a*t)
      (fun x _ y _ hxy => by dsimp; nlinarith) (fun _ _ => mem_univ _)

theorem kernelProjectedTranslate_variation_le (J : Set ℝ) (y c a : ℝ)
    (g : ℝ → ℂ) :
    eVariationOn (kernelProjectedTranslate J y c a g) univ ≤ eVariationOn g univ := by
  unfold kernelProjectedTranslate
  by_cases hy : y ∈ J
  · simpa only [indicator_of_mem hy] using kernelVariation_affine_le g c a
  · simp only [indicator_of_notMem hy]
    rw [eVariationOn.constant_on (by simp)]
    exact zero_le

theorem kernelProjectedTranslate_lip_on {J : Set ℝ} (y c a : ℝ)
    {g : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ u ∈ J, ∀ v ∈ J, ‖g u-g v‖ ≤ L*|u-v|)
    {x x' : ℝ} (hx : c+a*x ∈ J) (hx' : c+a*x' ∈ J) :
    ‖kernelProjectedTranslate J y c a g x - kernelProjectedTranslate J y c a g x'‖ ≤
      (|a| * L) * |x-x'| := by
  by_cases hy : y ∈ J
  · simp only [kernelProjectedTranslate, indicator_of_mem hy]
    have h := hg _ hx _ hx'
    rw [show (c+a*x)-(c+a*x') = a*(x-x') by ring, abs_mul] at h
    exact h.trans_eq (by ring)
  · simp only [kernelProjectedTranslate, indicator_of_notMem hy, sub_self, norm_zero]
    positivity

def kernelMarkedZeroLeftDens (J : Set ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (β a t : ℝ) (r : ℕ) (y z : ℝ) : ℝ :=
  J.indicator (fun _ => (1 : ℝ)) y * krDens J ν f β a (r+1) (y+β-a*t) z

def kernelMarkedZeroRightDens (J : Set ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (β a t : ℝ) (l : ℕ) (y z : ℝ) : ℝ :=
  krDens J ν f β a (l+1) y (z-β+a*t) * J.indicator (fun _ => (1 : ℝ)) z

theorem kernelMarkedZeroLeftDens_represents {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β t : ℝ) (r : ℕ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ z, |φ z| ≤ M) (y : ℝ) :
    kernelMarkedRow J ν β a t 0 (r+1) φ y =
      ∫ z, kernelMarkedZeroLeftDens J ν f β a t r y z * φ z :=
  kernelMarkedRow_zero_succ ν hJ hJfin hf hf0 hfD hν ha t r hφ hM y

theorem kernelMarkedZeroRightDens_represents {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β t : ℝ) (l : ℕ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ z, |φ z| ≤ M) (y : ℝ) :
    kernelMarkedRow J ν β a t (l+1) 0 φ y =
      ∫ z, kernelMarkedZeroRightDens J ν f β a t l y z * φ z :=
  kernelMarkedRow_succ_zero ν hJ hJfin hf hf0 hfD hν ha t l hφ hM y

/-- A zero left side keeps the starting projection and translates the actual
reverse row decomposition. No zero-step density is used. -/
theorem kernelMarkedZeroLeftDens_split {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β : ℝ) (r : ℕ) (y z : ℝ)
    {g e : ℝ → ℂ}
    (hsplit : ∀ u, kernelComplexRow J ν f (-β) (-a) (r+1) z u = g u+e u) (t : ℝ) :
    (kernelMarkedZeroLeftDens J ν f β a t r y z : ℂ) =
      kernelProjectedTranslate J y (y+β) (-a) g t +
        kernelProjectedTranslate J y (y+β) (-a) e t := by
  by_cases hy : y ∈ J
  · simp only [kernelMarkedZeroLeftDens, kernelProjectedTranslate, indicator_of_mem hy, one_mul]
    rw [krDens_symm ν hJ hJfin hf hf0 hfD hν ha r]
    rw [show y+β-a*t = y+β+(-a)*t by ring]
    exact hsplit _
  · simp [kernelMarkedZeroLeftDens, kernelProjectedTranslate, hy]

/-- A zero right side keeps the terminal projection and translates the actual
forward row decomposition. -/
theorem kernelMarkedZeroRightDens_split (J : Set ℝ) (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ) (β a : ℝ) (l : ℕ) (y z : ℝ) {g e : ℝ → ℂ}
    (hsplit : ∀ u, kernelComplexRow J ν f β a (l+1) y u = g u+e u) (t : ℝ) :
    (kernelMarkedZeroRightDens J ν f β a t l y z : ℂ) =
      kernelProjectedTranslate J z (z-β) a g t +
        kernelProjectedTranslate J z (z-β) a e t := by
  by_cases hz : z ∈ J
  · simp only [kernelMarkedZeroRightDens, kernelProjectedTranslate, indicator_of_mem hz, mul_one]
    exact hsplit _
  · simp [kernelMarkedZeroRightDens, kernelProjectedTranslate, hz]

end
end PGM
