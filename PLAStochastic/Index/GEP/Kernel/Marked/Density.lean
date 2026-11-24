import PLAStochastic.Index.GEP.Kernel.Row.FreeDensity
import PLAStochastic.Index.GEP.Kernel.Tilt.Conjugacy

/-!
# The actual inserted step and its density correlation

The marked row is the real killed operator `Q^l M_t Q^r`. Both endpoint
projections are retained, including when either side has zero random steps.
The two-sided density below is the correlation of the actual row densities.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option maxHeartbeats 800000

def kernelMarkedRow (J : Set ℝ) (ν : Measure ℝ) (β a t : ℝ)
    (l r : ℕ) (φ : ℝ → ℝ) : ℝ → ℝ :=
  krRow J ν β a l (fun u => krRow J ν β a r φ (u + β - a * t))

theorem kernelMarkedRow_zero_zero (J : Set ℝ) (ν : Measure ℝ) (β a t : ℝ)
    (φ : ℝ → ℝ) (y : ℝ) :
    kernelMarkedRow J ν β a t 0 0 φ y =
      J.indicator (fun _ => (1 : ℝ)) y *
        J.indicator (fun _ => (1 : ℝ)) (y + β - a * t) * φ (y + β - a * t) := by
  unfold kernelMarkedRow
  simp only [krRow_zero]
  by_cases hy : y ∈ J <;> by_cases hz : y + β - a * t ∈ J <;> simp [hy, hz]

/-- The real marked row is exactly the zero-perturbation complex killed row
with its shifted inner row. The outer terminal projection is the marked step's
projection. This identifies the correlation with the original BV operators. -/
theorem kernelMarkedRow_eq_kRow (J : Set ℝ) (ν : Measure ℝ) (β a t : ℝ)
    (l r : ℕ) (φ : ℝ → ℝ) :
    kRow J ν ν 0 β a l
      (fun u => kRow J ν ν 0 β a r (fun z => (φ z : ℂ)) (u + β - a * t)) =
        fun y => (kernelMarkedRow J ν β a t l r φ y : ℂ) := by
  rw [kRow_zero_eq_krRow ν ν r, kRow_zero_eq_krRow ν ν l]
  rfl

def kernelMarkedDens (J : Set ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (β a t : ℝ) (l r : ℕ) (y z : ℝ) : ℝ :=
  ∫ u, krDens J ν f β a l y u * krDens J ν f β a r (u + β - a * t) z

variable {J : Set ℝ} {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

theorem kernelMarkedDens_nonneg (hf0 : ∀ x, 0 ≤ f x) (t : ℝ) (l r : ℕ) (y z : ℝ) :
    0 ≤ kernelMarkedDens J ν f β a t l r y z :=
  integral_nonneg fun _ => mul_nonneg (krDens_nonneg ν hf0 _ _ _) (krDens_nonneg ν hf0 _ _ _)

/-- The right factor is literally a reverse row, at every point including
the boundary. This is the correlation consumed by the BV row decomposition. -/
theorem kernelMarkedDens_reverse (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (t : ℝ) (l r : ℕ) (y z : ℝ) :
    kernelMarkedDens J ν f β a t l (r + 1) y z =
      ∫ u, krDens J ν f β a l y u * krDens J ν f (-β) (-a) (r + 1) z (u + β - a * t) := by
  unfold kernelMarkedDens
  apply integral_congr_ae
  filter_upwards [] with u
  rw [krDens_symm ν hJ hJfin hf hf0 hfD hν ha r]

theorem measurable_kernelMarkedDens (hJ : MeasurableSet J) (hf : Measurable f)
    (t : ℝ) (l r : ℕ) (y : ℝ) :
    Measurable (kernelMarkedDens J ν f β a t l r y) := by
  have hp : Measurable (fun p : ℝ × ℝ => (p.2 + β - a * t, p.1)) := by fun_prop
  have hm : Measurable (fun p : ℝ × ℝ =>
      krDens J ν f β a l y p.2 * krDens J ν f β a r (p.2 + β - a * t) p.1) :=
    ((measurable_krDens_right ν hJ hf β a l y).comp measurable_snd).mul
      ((measurable_krDens_prod ν hJ hf β a r).comp hp)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem kernel_marked_product_integrable (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (t : ℝ) (l r : ℕ) (y : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ)
    {M : ℝ} (hM : ∀ z, |φ z| ≤ M) :
    Integrable (fun p : ℝ × ℝ =>
      krDens J ν f β a l y p.1 * krDens J ν f β a r (p.1 + β - a * t) p.2 * φ p.2)
      (volume.prod volume) := by
  have hp : Measurable (fun p : ℝ × ℝ => (p.1 + β - a * t, p.2)) := by fun_prop
  have hDa : 0 ≤ D / |a| := div_nonneg ((hf0 0).trans (hfD 0)) (abs_nonneg _)
  have hm : Measurable (fun p : ℝ × ℝ =>
      krDens J ν f β a l y p.1 * krDens J ν f β a r (p.1 + β - a * t) p.2 * φ p.2) :=
    (((measurable_krDens_right ν hJ hf β a l y).comp measurable_fst).mul
      ((measurable_krDens_prod ν hJ hf β a r).comp hp)).mul
        (hφ.comp measurable_snd)
  have hdom : Integrable (fun p : ℝ × ℝ =>
      (J ×ˢ J).indicator (fun _ => (D / |a|) * (D / |a|) * M) p) (volume.prod volume) := by
    rw [integrable_indicator_iff (hJ.prod hJ)]
    exact integrableOn_const (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hJfin hJfin)
  refine hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  by_cases h₁ : p.1 ∈ J
  · by_cases h₂ : p.2 ∈ J
    · rw [indicator_of_mem (show p ∈ J ×ˢ J from ⟨h₁, h₂⟩), abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (abs_krDens_le ν hf0 hfD _ _ _)
        (abs_krDens_le ν hf0 hfD _ _ _) (abs_nonneg _) hDa)
        (hM _) (abs_nonneg _) (mul_self_nonneg _)
    · rw [krDens_eq_zero_of_right_notMem ν h₂, mul_zero, zero_mul, abs_zero]
      simp [h₂]
  · rw [krDens_eq_zero_of_right_notMem ν h₁, zero_mul, zero_mul, abs_zero]
    simp [h₁]

/-- Pointwise density representation of the actual marked row when both
random sides are positive. No derivative of the input density is used. -/
theorem kernelMarkedRow_succ_succ (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (t : ℝ) (l r : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ z, |φ z| ≤ M) (y : ℝ) :
    kernelMarkedRow J ν β a t (l + 1) (r + 1) φ y =
      ∫ z, kernelMarkedDens J ν f β a t (l + 1) (r + 1) y z * φ z := by
  unfold kernelMarkedRow
  have hp : Measurable (fun u : ℝ => u + β - a * t) := by fun_prop
  have hψ : Measurable (fun u => krRow J ν β a (r + 1) φ (u + β - a * t)) :=
    (measurable_krRow hJ ν β a (r + 1) hφ hM).comp hp
  rw [krRow_succ_eq_integral_krDens (β := β) ν hJ hJfin hf hf0 hfD hν ha l
    hψ
    (fun _ => abs_krRow_le hJ ν β a (r + 1) hφ hM _) y]
  simp_rw [krRow_succ_eq_integral_krDens ν hJ hJfin hf hf0 hfD hν ha r hφ hM]
  simp_rw [← integral_const_mul]
  have hs := integral_integral_swap
    (f := fun u z => krDens J ν f β a (l + 1) y u *
      krDens J ν f β a (r + 1) (u + β - a * t) z * φ z)
    (kernel_marked_product_integrable (β := β) (a := a) ν hJ hJfin hf hf0 hfD
      t (l + 1) (r + 1) y hφ hM)
  simp only [mul_assoc] at hs
  rw [hs]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [kernelMarkedDens, ← integral_mul_const, mul_assoc]

/-- A zero left side retains its starting-band projection. -/
theorem kernelMarkedRow_zero_succ (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (t : ℝ) (r : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ z, |φ z| ≤ M) (y : ℝ) :
    kernelMarkedRow J ν β a t 0 (r + 1) φ y =
      ∫ z, (J.indicator (fun _ => (1 : ℝ)) y *
        krDens J ν f β a (r + 1) (y + β - a * t) z) * φ z := by
  unfold kernelMarkedRow
  rw [krRow_zero]
  by_cases hy : y ∈ J
  · simp only [indicator_of_mem hy, one_mul]
    exact krRow_succ_eq_integral_krDens ν hJ hJfin hf hf0 hfD hν ha r hφ hM _
  · simp [indicator_of_notMem hy]

/-- A zero right side translates the genuine left density and retains the
terminal band projection. The change of variables has unit Jacobian. -/
theorem kernelMarkedRow_succ_zero (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) (ha : a ≠ 0)
    (t : ℝ) (l : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ z, |φ z| ≤ M) (y : ℝ) :
    kernelMarkedRow J ν β a t (l + 1) 0 φ y =
      ∫ z, (krDens J ν f β a (l + 1) y (z - β + a * t) *
        J.indicator (fun _ => (1 : ℝ)) z) * φ z := by
  unfold kernelMarkedRow
  simp only [krRow_zero]
  have hp : Measurable (fun u : ℝ => u + β - a * t) := by fun_prop
  have hψ : Measurable (fun u => J.indicator φ (u + β - a * t)) :=
    (hφ.indicator hJ).comp hp
  have hψb (u : ℝ) : |J.indicator φ (u + β - a * t)| ≤ M := by
    by_cases hu : u + β - a * t ∈ J
    · simpa only [indicator_of_mem hu] using hM (u + β - a * t)
    · simpa only [indicator_of_notMem hu, abs_zero] using (abs_nonneg (φ 0)).trans (hM 0)
  rw [krRow_succ_eq_integral_krDens (β := β) ν hJ hJfin hf hf0 hfD hν ha l hψ hψb y]
  rw [← integral_add_right_eq_self
    (fun z => (krDens J ν f β a (l + 1) y (z - β + a * t) *
      J.indicator (fun _ => (1 : ℝ)) z) * φ z) (β - a * t)]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [show u + (β - a * t) - β + a * t = u by ring]
  have he : u + (β - a * t) = u + β - a * t := by ring
  rw [he]
  by_cases hu : u + β - a * t ∈ J <;> simp [hu]

end
end PGM
