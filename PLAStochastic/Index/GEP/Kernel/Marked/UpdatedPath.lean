import PLAStochastic.Index.GEP.Kernel.Marked.Density
import PLAStochastic.Index.GEP.Kernel.Facet.FourBlocks

/-!
# The original updated path and its last-random-gap density

The marked operator is represented by `Function.update` on the original iid
path. Integrating the last unmarked random gap gives a true density, with a
separate projected formula when the left random side is empty.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option maxHeartbeats 800000

theorem kernel_update_tail (g : ℕ → ℝ) (l : ℕ) (t : ℝ) :
    (fun j => Function.update g (l+1) t (j+1)) =
      Function.update (fun j => g (j+1)) l t := by
  funext j
  by_cases hj : j = l
  · subst j
    simp
  · have hj' : j+1 ≠ l+1 := by omega
    simp only [Function.update_of_ne hj', Function.update_of_ne hj]

theorem kernel_update_zero_tail (g : ℕ → ℝ) (t : ℝ) :
    (fun j => Function.update g 0 t (j+1)) = fun j => g (j+1) := by
  funext j
  simp

theorem kernelMarkedRow_succ_left (J : Set ℝ) (ν : Measure ℝ) (β a t : ℝ)
    (l r : ℕ) (φ : ℝ → ℝ) :
    kernelMarkedRow J ν β a t (l+1) r φ =
      krStep J ν β a (kernelMarkedRow J ν β a t l r φ) := by
  unfold kernelMarkedRow
  rw [krRow_succ]

theorem measurable_kernel_marked_test {J : Set ℝ} (hJ : MeasurableSet J)
    (β a t : ℝ) (l r : ℕ) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) =>
      krAlive J β a (l+r+1) p.1 (Function.update p.2 l t) *
        φ (kWalk p.1 β a (Function.update p.2 l t) (l+r+1))) := by
  have hu' : Measurable (fun p : ℝ × (ℕ → ℝ) => Function.update p.2 l t) := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j = l
    · subst j
      simpa only [Function.update_self] using (measurable_const :
        Measurable (fun _ : ℝ × (ℕ → ℝ) => t))
    · simpa only [Function.update_of_ne hj, Function.comp_def] using
        (measurable_pi_apply j).comp measurable_snd
  have hu : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      (p.1, Function.update p.2 l t)) := measurable_fst.prodMk hu'
  exact ((measurable_krAlive_prod hJ β a (l+r+1)).mul
    (hφ.comp (measurable_kWalk_prod β a (l+r+1)))).comp hu

/-- The actual marked operator has the original one-gap-update path formula. -/
theorem kernelMarkedRow_eq_updated_path {J : Set ℝ} (hJ : MeasurableSet J)
    (ν : ProbabilityMeasure ℝ) (β a t : ℝ) (l r : ℕ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ z, |φ z| ≤ M) (y : ℝ) :
    kernelMarkedRow J ν β a t l r φ y =
      ∫ g, krAlive J β a (l+r+1) y (Function.update g l t) *
        φ (kWalk y β a (Function.update g l t) (l+r+1)) ∂iidLaw ν := by
  induction l generalizing y with
  | zero =>
    simp only [Nat.zero_add, krAlive_succ, kWalk_succ, Function.update_self,
      kernel_update_zero_tail]
    unfold kernelMarkedRow
    rw [krRow_zero]
    by_cases hy : y ∈ J
    · simp only [indicator_of_mem hy, one_mul]
      exact (kernel_shifted_block_integral ν hJ β a 1 r (y+β-a*t) hφ hM).symm
    · simp only [indicator_of_notMem hy, zero_mul, integral_zero]
  | succ l ih =>
    rw [kernelMarkedRow_succ_left]
    by_cases hy : y ∉ J
    · rw [krStep_eq_zero_of_notMem hy]
      simp only [krAlive_eq_zero_of_notMem hy, zero_mul, integral_zero]
    push Not at hy
    let F : ℝ → (ℕ → ℝ) → ℝ := fun x g =>
      krAlive J β a (l+r+1) (y+β-a*x) (Function.update g l t) *
        φ (kWalk (y+β-a*x) β a (Function.update g l t) (l+r+1))
    have hFm : Measurable (Function.uncurry F) := by
      have hcomp := (measurable_kernel_marked_test hJ β a t l r hφ).comp
        (show Measurable (fun p : ℝ × (ℕ → ℝ) => (y+β-a*p.1,p.2)) from
          (measurable_const.sub (measurable_const.mul measurable_fst)).prodMk measurable_snd)
      exact hcomp
    have hFb : ∀ x g, |F x g| ≤ M := by
      intro x g
      dsimp only [F]
      rw [abs_mul]
      exact (mul_le_mul (abs_krAlive_le_one _ _ _) (hM _) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul M)
    have he (g : ℕ → ℝ) :
        krAlive J β a (l+1+r+1) y (Function.update g (l+1) t) *
            φ (kWalk y β a (Function.update g (l+1) t) (l+1+r+1)) =
          F (g 0) (fun j => g (j+1)) := by
      rw [show l+1+r+1 = (l+r+1)+1 by omega, krAlive_succ, kWalk_succ,
        Function.update_of_ne (by omega : 0 ≠ l+1), kernel_update_tail,
        indicator_of_mem hy, one_mul]
    simp_rw [he]
    rw [kr_integral_head ν hFm hFb, krStep_of_mem hy]
    apply integral_congr_ae
    filter_upwards [] with x
    exact ih (y+β-a*x)

/-- Testing a killed row by its genuine last one-step density gives the next
positive-step density representative, at every endpoint. -/
theorem kernel_krRow_krKer {J : Set ℝ} (hJ : MeasurableSet J)
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (β a : ℝ) (r : ℕ) (y z : ℝ) :
    krRow J ν β a r (fun u => krKer J f β a u z) y =
      krDens J ν f β a (r+1) y z := by
  rw [krRow_eq_integral hJ ν β a r
    (φ := fun u => krKer J f β a u z)
    ((measurable_krKer_prod hJ hf β a).comp (measurable_id.prodMk measurable_const))
    (fun u => abs_krKer_le hf0 hfD u z) y, krDens_succ]

/-- The density obtained by integrating the final unmarked random gap of the
actual updated path. Here `r` is the number of random steps after the mark and
must be positive when this function is consumed as a density. -/
def kernelUpdatedLastDensity (J : Set ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (β a t : ℝ) (l r : ℕ) (y z : ℝ) : ℝ :=
  ∫ g, krAlive J β a (l+r) y (Function.update g l t) *
    krKer J f β a (kWalk y β a (Function.update g l t) (l+r)) z ∂iidLaw ν

theorem kernelUpdatedLastDensity_eq_markedRow {J : Set ℝ} (hJ : MeasurableSet J)
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (β a t : ℝ) (l r : ℕ) (y z : ℝ) :
    kernelUpdatedLastDensity J ν f β a t l (r+1) y z =
      kernelMarkedRow J ν β a t l r (fun u => krKer J f β a u z) y := by
  rw [kernelMarkedRow_eq_updated_path hJ ν β a t l r
    (φ := fun u => krKer J f β a u z)
    ((measurable_krKer_prod hJ hf β a).comp (measurable_id.prodMk measurable_const))
    (fun u => abs_krKer_le hf0 hfD u z) y]
  simp only [kernelUpdatedLastDensity, Nat.add_assoc]

/-- With positive random lengths on both sides, the last-gap density is the
actual marked correlation, rather than a probability of a pinned endpoint. -/
theorem kernelUpdatedLastDensity_succ_succ {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β t : ℝ) (l r : ℕ) (y z : ℝ) :
    kernelUpdatedLastDensity J ν f β a t (l+1) (r+1) y z =
      kernelMarkedDens J ν f β a t (l+1) (r+1) y z := by
  rw [kernelUpdatedLastDensity_eq_markedRow hJ ν hf hf0 hfD]
  unfold kernelMarkedRow
  have he : (fun u => krRow J ν β a r (fun v => krKer J f β a v z) (u+β-a*t)) =
      fun u => krDens J ν f β a (r+1) (u+β-a*t) z := by
    funext u
    exact kernel_krRow_krKer hJ ν hf hf0 hfD β a r _ z
  rw [he, krRow_succ_eq_integral_krDens (β := β) ν hJ hJfin hf hf0 hfD hν ha l
    (φ := fun u => krDens J ν f β a (r+1) (u+β-a*t) z)
    ((measurable_krDens_left ν hJ hf β a (r+1) z).comp (by fun_prop))
    (fun u => abs_krDens_le ν hf0 hfD (r+1) (u+β-a*t) z) y]
  rfl

/-- The zero-left case retains the original starting-band projection. -/
theorem kernelUpdatedLastDensity_zero_succ {J : Set ℝ} (hJ : MeasurableSet J)
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (β a t : ℝ) (r : ℕ) (y z : ℝ) :
    kernelUpdatedLastDensity J ν f β a t 0 (r+1) y z =
      J.indicator (fun _ => (1 : ℝ)) y * krDens J ν f β a (r+1) (y+β-a*t) z := by
  rw [kernelUpdatedLastDensity_eq_markedRow hJ ν hf hf0 hfD]
  unfold kernelMarkedRow
  rw [krRow_zero]
  by_cases hy : y ∈ J
  · simp only [indicator_of_mem hy, one_mul]
    exact kernel_krRow_krKer hJ ν hf hf0 hfD β a r _ z
  · simp only [indicator_of_notMem hy, zero_mul]

theorem kernelUpdatedLastDensity_of_pos {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β t : ℝ) {l r : ℕ} (hl : 1 ≤ l) (hr : 1 ≤ r)
    (y z : ℝ) :
    (∫ g, krAlive J β a (l+r) y (Function.update g l t) *
      krKer J f β a (kWalk y β a (Function.update g l t) (l+r)) z ∂iidLaw ν) =
      kernelMarkedDens J ν f β a t l r y z := by
  obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  exact kernelUpdatedLastDensity_succ_succ hJ hJfin ν hf hf0 hfD hν ha β t l' r' y z

theorem kernelUpdatedLastDensity_zero_of_pos {J : Set ℝ} (hJ : MeasurableSet J)
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (β a t : ℝ) {r : ℕ} (hr : 1 ≤ r) (y z : ℝ) :
    (∫ g, krAlive J β a r y (Function.update g 0 t) *
      krKer J f β a (kWalk y β a (Function.update g 0 t) r) z ∂iidLaw ν) =
      J.indicator (fun _ => (1 : ℝ)) y * krDens J ν f β a r (y+β-a*t) z := by
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simpa only [kernelUpdatedLastDensity, Nat.zero_add] using
    kernelUpdatedLastDensity_zero_succ hJ ν hf hf0 hfD β a t r' y z

end
end PGM
