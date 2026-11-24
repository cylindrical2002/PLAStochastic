import PLAStochastic.Index.GEP.Kernel.Marked.Correlation
import PLAStochastic.Index.GEP.Kernel.Marked.Density

/-!
# Actual marked densities consume whole-line BV row decompositions

Both random sides have positive length. A genuine row representative is split
pointwise into a BV part and a uniformly small remainder. Its correlation is
then Lipschitz plus a uniformly controlled error, with the other row's actual
survival mass and any valid uniform row bound.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

def kernelComplexRow (J : Set ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (β a : ℝ) (n : ℕ) (y u : ℝ) : ℂ := krDens J ν f β a n y u

theorem measurable_kernelComplexRow {J : Set ℝ} (hJ : MeasurableSet J)
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (β a : ℝ) (n : ℕ) (y : ℝ) : Measurable (kernelComplexRow J ν f β a n y) :=
  Complex.measurable_ofReal.comp (measurable_krDens_right ν hJ hf β a n y)

theorem integrable_kernelComplexRow {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (β a : ℝ) (n : ℕ) (y : ℝ) : Integrable (kernelComplexRow J ν f β a n y) :=
  (kr_integrable_krDens_right ν hJ hJfin hf hf0 hfD n y).ofReal

theorem kernelComplexRow_norm_le {J : Set ℝ} (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (β a : ℝ) (n : ℕ) (y u : ℝ) :
    ‖kernelComplexRow J ν f β a n y u‖ ≤ D / |a| := by
  simpa only [kernelComplexRow, Complex.norm_real, Real.norm_eq_abs] using
    abs_krDens_le (β := β) (a := a) ν hf0 hfD n y u

theorem kernelComplexRow_norm_integral {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β : ℝ) (n : ℕ) (y : ℝ) :
    (∫ u, ‖kernelComplexRow J ν f β a (n+1) y u‖) =
      krSurv J (ν : Measure ℝ) β a (n+1) y := by
  simp only [kernelComplexRow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (krDens_nonneg ν hf0 _ _ _)]
  exact integral_krDens ν hJ hJfin hf hf0 hfD hν ha n y

/-- The original real marked density is exactly the complex correlation of
the original forward and reverse density representatives. -/
theorem kernelMarkedDens_eq_correlation {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β t : ℝ) (l r : ℕ) (y z : ℝ) :
    (kernelMarkedDens J ν f β a t (l+1) (r+1) y z : ℂ) =
      kernelCorrelation (kernelComplexRow J ν f β a (l+1) y)
        (kernelComplexRow J ν f (-β) (-a) (r+1) z) (β-a*t) := by
  rw [kernelMarkedDens_reverse ν hJ hJfin hf hf0 hfD hν ha]
  unfold kernelCorrelation kernelComplexRow
  calc
    _ = ∫ u, ((krDens J ν f β a (l+1) y u *
        krDens J ν f (-β) (-a) (r+1) z (u+β-a*t) : ℝ) : ℂ) := integral_ofReal.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [Complex.ofReal_mul, show u+β-a*t = u+(β-a*t) by ring]

/-- The reverse row is decomposed; the forward row supplies its actual L¹
survival mass and a freely chosen valid L∞ bound. -/
theorem kernelMarkedDens_split_reverse {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β : ℝ) (l r : ℕ) (y z : ℝ)
    {g e : ℝ → ℂ} (hg : Measurable g) (hgi : Integrable g)
    (hgv : BoundedVariationOn g univ) (he : Measurable e)
    {B R : ℝ} (hB : ∀ u, ‖kernelComplexRow J ν f β a (l+1) y u‖ ≤ B)
    (hR : ∀ u, ‖e u‖ ≤ R)
    (hsplit : ∀ u, kernelComplexRow J ν f (-β) (-a) (r+1) z u = g u + e u) :
    ∃ G E : ℝ → ℂ, Measurable G ∧ Measurable E ∧
      (∀ t, (kernelMarkedDens J ν f β a t (l+1) (r+1) y z : ℂ) = G t + E t) ∧
      (∀ x x', ‖G x - G x'‖ ≤ (|a| * (eVariationOn g univ).toReal * B) * |x-x'|) ∧
      (∀ t, ‖E t‖ ≤ R * krSurv J (ν : Measure ℝ) β a (l+1) y) := by
  let F := kernelComplexRow J ν f β a (l+1) y
  have hF : Measurable F := measurable_kernelComplexRow hJ ν hf β a (l+1) y
  have hFi : Integrable F := integrable_kernelComplexRow hJ hJfin ν hf hf0 hfD β a (l+1) y
  refine ⟨fun t => kernelCorrelation F g (β-a*t),
    fun t => kernelCorrelation F e (β-a*t),
    (measurable_kernelCorrelation hF hg).comp (by fun_prop),
    (measurable_kernelCorrelation hF he).comp (by fun_prop), ?_, ?_, ?_⟩
  · intro t
    rw [kernelMarkedDens_eq_correlation hJ hJfin ν hf hf0 hfD hν ha]
    exact kernelCorrelation_split_right hF hFi hB hgi he hR hsplit (β-a*t)
  · exact kernelCorrelation_affine_lip_right hF hB hgv hgi β a
  · intro t
    have h := kernelCorrelation_norm_le_left hFi hR (β-a*t)
    rw [kernelComplexRow_norm_integral hJ hJfin ν hf hf0 hfD hν ha β l y] at h
    exact h

/-- The forward row may supply the BV part instead, with the reverse row's
actual survival mass controlling the uniform error. -/
theorem kernelMarkedDens_split_forward {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β : ℝ) (l r : ℕ) (y z : ℝ)
    {g e : ℝ → ℂ} (hg : Measurable g) (hgi : Integrable g)
    (hgv : BoundedVariationOn g univ) (he : Measurable e)
    {B R : ℝ} (hB : ∀ u, ‖kernelComplexRow J ν f (-β) (-a) (r+1) z u‖ ≤ B)
    (hR : ∀ u, ‖e u‖ ≤ R)
    (hsplit : ∀ u, kernelComplexRow J ν f β a (l+1) y u = g u + e u) :
    ∃ G E : ℝ → ℂ, Measurable G ∧ Measurable E ∧
      (∀ t, (kernelMarkedDens J ν f β a t (l+1) (r+1) y z : ℂ) = G t + E t) ∧
      (∀ x x', ‖G x - G x'‖ ≤ (|a| * (eVariationOn g univ).toReal * B) * |x-x'|) ∧
      (∀ t, ‖E t‖ ≤ R * krSurv J (ν : Measure ℝ) (-β) (-a) (r+1) z) := by
  let F := kernelComplexRow J ν f (-β) (-a) (r+1) z
  have hF : Measurable F := measurable_kernelComplexRow hJ ν hf (-β) (-a) (r+1) z
  have hFi : Integrable F :=
    integrable_kernelComplexRow hJ hJfin ν hf hf0 hfD (-β) (-a) (r+1) z
  refine ⟨fun t => kernelCorrelation g F (β-a*t),
    fun t => kernelCorrelation e F (β-a*t),
    (measurable_kernelCorrelation hg hF).comp (by fun_prop),
    (measurable_kernelCorrelation he hF).comp (by fun_prop), ?_, ?_, ?_⟩
  · intro t
    rw [kernelMarkedDens_eq_correlation hJ hJfin ν hf hf0 hfD hν ha]
    exact kernelCorrelation_split_left hF hFi hB hgi he hR hsplit (β-a*t)
  · exact kernelCorrelation_affine_lip_left hF hB hgv hgi β a
  · intro t
    have h := kernelCorrelation_norm_le_right hFi hR (β-a*t)
    rw [kernelComplexRow_norm_integral hJ hJfin ν hf hf0 hfD hν (neg_ne_zero.mpr ha)
      (-β) r z] at h
    exact h

/-- Taking real parts preserves the exact sum, Lipschitz constant, and error
budget when the original correlation is real-valued. -/
theorem kernel_real_split_of_complex {F : ℝ → ℝ} {G E : ℝ → ℂ}
    (hG : Measurable G) (hE : Measurable E) (hF : ∀ t, (F t : ℂ) = G t+E t)
    {L R : ℝ} (hL : ∀ x y, ‖G x-G y‖ ≤ L*|x-y|) (hR : ∀ t, ‖E t‖ ≤ R) :
    ∃ G' E' : ℝ → ℝ, Measurable G' ∧ Measurable E' ∧
      (∀ t, F t = G' t+E' t) ∧
      (∀ x y, |G' x-G' y| ≤ L*|x-y|) ∧ (∀ t, |E' t| ≤ R) := by
  refine ⟨fun t => (G t).re, fun t => (E t).re,
    Complex.measurable_re.comp hG, Complex.measurable_re.comp hE, ?_, ?_, ?_⟩
  · intro t
    have h := congrArg Complex.re (hF t)
    simpa only [Complex.ofReal_re, Complex.add_re] using h
  · intro x y
    have h := (Complex.abs_re_le_norm (G x-G y)).trans (hL x y)
    simpa only [Complex.sub_re] using h
  · intro t
    exact (Complex.abs_re_le_norm (E t)).trans (hR t)

theorem kernelMarkedDens_split_reverse_real {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β : ℝ) (l r : ℕ) (y z : ℝ)
    {g e : ℝ → ℂ} (hg : Measurable g) (hgi : Integrable g)
    (hgv : BoundedVariationOn g univ) (he : Measurable e)
    {B R : ℝ} (hB : ∀ u, ‖kernelComplexRow J ν f β a (l+1) y u‖ ≤ B)
    (hR : ∀ u, ‖e u‖ ≤ R)
    (hsplit : ∀ u, kernelComplexRow J ν f (-β) (-a) (r+1) z u = g u+e u) :
    ∃ G E : ℝ → ℝ, Measurable G ∧ Measurable E ∧
      (∀ t, kernelMarkedDens J ν f β a t (l+1) (r+1) y z = G t+E t) ∧
      (∀ x x', |G x-G x'| ≤ (|a| * (eVariationOn g univ).toReal*B)*|x-x'|) ∧
      (∀ t, |E t| ≤ R*krSurv J (ν : Measure ℝ) β a (l+1) y) := by
  obtain ⟨G,E,hG,hE,hF,hL,hErr⟩ := kernelMarkedDens_split_reverse hJ hJfin ν
    hf hf0 hfD hν ha β l r y z hg hgi hgv he hB hR hsplit
  exact kernel_real_split_of_complex hG hE hF hL hErr

theorem kernelMarkedDens_split_forward_real {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β : ℝ) (l r : ℕ) (y z : ℝ)
    {g e : ℝ → ℂ} (hg : Measurable g) (hgi : Integrable g)
    (hgv : BoundedVariationOn g univ) (he : Measurable e)
    {B R : ℝ} (hB : ∀ u, ‖kernelComplexRow J ν f (-β) (-a) (r+1) z u‖ ≤ B)
    (hR : ∀ u, ‖e u‖ ≤ R)
    (hsplit : ∀ u, kernelComplexRow J ν f β a (l+1) y u = g u+e u) :
    ∃ G E : ℝ → ℝ, Measurable G ∧ Measurable E ∧
      (∀ t, kernelMarkedDens J ν f β a t (l+1) (r+1) y z = G t+E t) ∧
      (∀ x x', |G x-G x'| ≤ (|a| * (eVariationOn g univ).toReal*B)*|x-x'|) ∧
      (∀ t, |E t| ≤ R*krSurv J (ν : Measure ℝ) (-β) (-a) (r+1) z) := by
  obtain ⟨G,E,hG,hE,hF,hL,hErr⟩ := kernelMarkedDens_split_forward hJ hJfin ν
    hf hf0 hfD hν ha β l r y z hg hgi hgv he hB hR hsplit
  exact kernel_real_split_of_complex hG hE hF hL hErr

end
end PGM
