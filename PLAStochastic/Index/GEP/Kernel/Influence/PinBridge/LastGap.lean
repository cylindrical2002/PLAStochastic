import PLAStochastic.Index.GEP.Kernel.Marked.UpdatedPath
import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FullDensity

/-!
# Last-random-gap reconstruction of the actual pinned bridges

Replacing the final random gap by its unique endpoint value converts its
physical-gap density into the genuine killed endpoint density, with the exact
factor `|a|`. Arbitrary path rewards can be retained through this pointwise
identity. The marked specialization uses the original one-coordinate update.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 800000

theorem kernel_kWalk_update_after (β a y : ℝ) (g : ℕ → ℝ) {n j : ℕ}
    (hnj : n ≤ j) (x : ℝ) :
    kWalk y β a (Function.update g j x) n = kWalk y β a g n := by
  unfold kWalk gapKeys
  congr 2
  exact Finset.sum_congr rfl fun l hl =>
    Function.update_of_ne (by have := Finset.mem_range.mp hl; omega : l ≠ j) _ _

theorem kernel_krAlive_update_after (J : Set ℝ) (β a y : ℝ) (g : ℕ → ℝ)
    {n j : ℕ} (hnj : n ≤ j) (x : ℝ) :
    krAlive J β a n y (Function.update g j x) = krAlive J β a n y g := by
  unfold krAlive
  apply Finset.prod_congr rfl
  intro l hl
  rw [kernel_kWalk_update_after β a y g (by have := Finset.mem_range.mp hl; omega) x]

def kernelPinLastGap (β a y z : ℝ) (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  (kWalk y β a g n + β - z) / a

def kernelPinLastPath (β a y z : ℝ) (n : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  Function.update g n (kernelPinLastGap β a y z n g)

theorem kernel_pin_last_endpoint {a : ℝ} (ha : a ≠ 0) (β y z : ℝ)
    (n : ℕ) (g : ℕ → ℝ) :
    kWalk y β a (kernelPinLastPath β a y z n g) (n+1) = z := by
  rw [kernel_kWalk_succ_last]
  simp only [kernelPinLastPath, kernel_kWalk_update_after β a y g le_rfl,
    Function.update_self, kernelPinLastGap]
  field_simp
  ring

/-- This is the physical-sum to residual-endpoint factor. Both endpoint band
projections are the original ones, including zero-length preceding paths. -/
theorem kernel_pin_last_density_factor (J : Set ℝ) (f : ℝ → ℝ)
    {a : ℝ} (ha : a ≠ 0) (β y z : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    f (kernelPinLastGap β a y z n g) *
        krAlive J β a (n+1) y (kernelPinLastPath β a y z n g) =
      |a| * (krAlive J β a n y g * krKer J f β a (kWalk y β a g n) z) := by
  rw [krAlive_succ_last, kernel_pin_last_endpoint ha]
  simp only [kernelPinLastPath, kernel_krAlive_update_after J β a y g le_rfl]
  unfold krKer
  rw [show krAlive J β a n y g *
      (J.indicator (fun _ => (1 : ℝ)) (kWalk y β a g n) *
        J.indicator (fun _ => (1 : ℝ)) z * (f ((kWalk y β a g n + β - z) / a) / |a|)) =
      (krAlive J β a n y g * J.indicator (fun _ => (1 : ℝ)) (kWalk y β a g n)) *
        J.indicator (fun _ => (1 : ℝ)) z * (f ((kWalk y β a g n + β - z) / a) / |a|) by ring,
    krAlive_mul_indicator]
  unfold kernelPinLastGap
  field_simp [abs_ne_zero.mpr ha]

/-- Arbitrary path rewards are carried through the same reconstructed path. -/
theorem kernel_pin_last_weighted_integral (J : Set ℝ) (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ) {a : ℝ} (ha : a ≠ 0) (β y z : ℝ) (n : ℕ)
    (W : (ℕ → ℝ) → ℝ) :
    (∫ g, f (kernelPinLastGap β a y z n g) *
        krAlive J β a (n+1) y (kernelPinLastPath β a y z n g) *
          W (kernelPinLastPath β a y z n g) ∂iidLaw ν) =
      |a| * ∫ g, krAlive J β a n y g * krKer J f β a (kWalk y β a g n) z *
        W (kernelPinLastPath β a y z n g) ∂iidLaw ν := by
  simp_rw [kernel_pin_last_density_factor J f ha, mul_assoc]
  rw [integral_const_mul]

theorem kernel_pin_last_integral_eq_density (J : Set ℝ) (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ) {a : ℝ} (ha : a ≠ 0) (β y z : ℝ) (n : ℕ) :
    (∫ g, f (kernelPinLastGap β a y z n g) *
        krAlive J β a (n+1) y (kernelPinLastPath β a y z n g) ∂iidLaw ν) =
      |a| * krDens J ν f β a (n+1) y z := by
  simp_rw [kernel_pin_last_density_factor J f ha]
  rw [integral_const_mul, krDens_succ]

theorem kernelUpdatedLastDensity_eq_full {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β t : ℝ) (l : ℕ) {r : ℕ} (hr : 1 ≤ r) (y z : ℝ) :
    kernelUpdatedLastDensity J ν f β a t l r y z =
      kernelMarkedFullDens J ν f β a t l r y z := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  cases l with
  | zero =>
    exact kernelUpdatedLastDensity_zero_succ hJ ν hf hf0 hfD β a t r y z
  | succ l =>
    exact kernelUpdatedLastDensity_succ_succ hJ hJfin ν hf hf0 hfD hν ha β t l r y z

/-- An actual designated gap followed by a positive random tail. The last
random gap is integrated as a density, rather than as a zero-probability pin. -/
theorem kernel_pin_marked_last_integral {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β t : ℝ) (l : ℕ) {r : ℕ} (hr : 1 ≤ r) (y z : ℝ) :
    (∫ g, f (kernelPinLastGap β a y z (l+r) (Function.update g l t)) *
        krAlive J β a (l+r+1) y
          (kernelPinLastPath β a y z (l+r) (Function.update g l t)) ∂iidLaw ν) =
      |a| * kernelMarkedFullDens J ν f β a t l r y z := by
  simp_rw [kernel_pin_last_density_factor J f ha]
  rw [integral_const_mul]
  congr 1
  exact kernelUpdatedLastDensity_eq_full hJ hJfin ν hf hf0 hfD hν ha β t l hr y z

/-- When the designated gap is last, reconstruct the preceding random gap at
the translated endpoint, then append the unchanged designated step. -/
def kernelPinMarkedEndPath (β a t y z : ℝ) (n : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  Function.update (kernelPinLastPath β a y (z-β+a*t) n g) (n+1) t

theorem kernel_pin_marked_end_endpoint {a : ℝ} (ha : a ≠ 0) (β t y z : ℝ)
    (n : ℕ) (g : ℕ → ℝ) :
    kWalk y β a (kernelPinMarkedEndPath β a t y z n g) (n+1+1) = z := by
  rw [kernel_kWalk_succ_last]
  simp only [kernelPinMarkedEndPath, kernel_kWalk_update_after β a y _ le_rfl,
    Function.update_self, kernel_pin_last_endpoint ha]
  ring

theorem kernel_pin_marked_end_density_factor (J : Set ℝ) (f : ℝ → ℝ)
    {a : ℝ} (ha : a ≠ 0) (β t y z : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    f (kernelPinLastGap β a y (z-β+a*t) n g) *
        krAlive J β a (n+1+1) y (kernelPinMarkedEndPath β a t y z n g) =
      |a| * ((krAlive J β a n y g * krKer J f β a (kWalk y β a g n) (z-β+a*t)) *
        J.indicator (fun _ => (1 : ℝ)) z) := by
  rw [krAlive_succ_last, kernel_pin_marked_end_endpoint ha]
  simp only [kernelPinMarkedEndPath, kernel_krAlive_update_after J β a y _ le_rfl]
  rw [← mul_assoc, kernel_pin_last_density_factor J f ha]
  ring

/-- The last-position mark gives exactly the terminal-projected one-sided
density. It is not lost when the right random length vanishes. -/
theorem kernel_pin_marked_end_integral (J : Set ℝ) (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ) {a : ℝ} (ha : a ≠ 0) (β t y z : ℝ) (n : ℕ) :
    (∫ g, f (kernelPinLastGap β a y (z-β+a*t) n g) *
        krAlive J β a (n+1+1) y (kernelPinMarkedEndPath β a t y z n g) ∂iidLaw ν) =
      |a| * kernelMarkedFullDens J ν f β a t (n+1) 0 y z := by
  simp_rw [kernel_pin_marked_end_density_factor J f ha]
  rw [integral_const_mul, integral_mul_const, kernelMarkedFullDens, krDens_succ]

end
end PGM
