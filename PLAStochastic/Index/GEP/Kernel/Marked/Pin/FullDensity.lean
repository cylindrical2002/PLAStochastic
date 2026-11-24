import PLAStochastic.Index.GEP.Kernel.Marked.Pin.Spectral
import PLAStochastic.Index.GEP.Kernel.Row.Measurable

/-!
# Marked pin densities with every non-Dirac random length

The two zero-side cases are the actual translated one-sided densities, with
their remaining endpoint projections. The zero-zero bridge is deliberately
excluded from the density representation: it remains the Dirac measure treated
in `GEPKernelDirac`. Spectral estimates retain `1 / |a|` for each random pin,
so integration over arbitrarily large slopes is possible.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 800000

/-- The density of the actual marked row whenever at least one random step
remains. At zero-zero this is only a placeholder, not the Dirac bridge. -/
def kernelMarkedFullDens (J : Set ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (β a t : ℝ) : ℕ → ℕ → ℝ → ℝ → ℝ
  | 0, 0, _, _ => 0
  | 0, r + 1, y, z => J.indicator (fun _ => (1 : ℝ)) y *
      krDens J ν f β a (r + 1) (y + β - a * t) z
  | l + 1, 0, y, z => krDens J ν f β a (l + 1) y (z - β + a * t) *
      J.indicator (fun _ => (1 : ℝ)) z
  | l + 1, r + 1, y, z => kernelMarkedDens J ν f β a t (l + 1) (r + 1) y z

/-- Every continuous parameter may vary measurably, also in the one-sided
cases. The density representative and killing interval remain fixed. -/
theorem measurable_kernelMarkedFullDens_param {X : Type*} [MeasurableSpace X]
    {J : Set ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hJ : MeasurableSet J) (hf : Measurable f) {β a t y z : X → ℝ}
    (hβ : Measurable β) (ha : Measurable a) (ht : Measurable t)
    (hy : Measurable y) (hz : Measurable z) (l r : ℕ) :
    Measurable (fun p => kernelMarkedFullDens J ν f (β p) (a p) (t p) l r (y p) (z p)) := by
  cases l with
  | zero =>
    cases r with
    | zero => exact measurable_const
    | succ r =>
      exact ((measurable_const.indicator hJ).comp hy).mul
        (measurable_krDens_param ν hJ hf hβ ha ((hy.add hβ).sub (ha.mul ht)) hz (r + 1))
  | succ l =>
    cases r with
    | zero =>
      exact (measurable_krDens_param ν hJ hf hβ ha hy
        ((hz.sub hβ).add (ha.mul ht)) (l + 1)).mul ((measurable_const.indicator hJ).comp hz)
    | succ r =>
      have hm : Measurable (fun p : X × ℝ =>
          krDens J ν f (β p.1) (a p.1) (l + 1) (y p.1) p.2 *
          krDens J ν f (β p.1) (a p.1) (r + 1)
            (p.2 + β p.1 - a p.1 * t p.1) (z p.1)) :=
        (measurable_krDens_param ν hJ hf (hβ.comp measurable_fst) (ha.comp measurable_fst)
          (hy.comp measurable_fst) measurable_snd (l + 1)).mul
        (measurable_krDens_param ν hJ hf (hβ.comp measurable_fst) (ha.comp measurable_fst)
          ((measurable_snd.add (hβ.comp measurable_fst)).sub
            ((ha.comp measurable_fst).mul (ht.comp measurable_fst)))
          (hz.comp measurable_fst) (r + 1))
      exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem kernelMarkedFullDens_nonneg {J : Set ℝ} (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (β a t : ℝ) (l r : ℕ) (y z : ℝ) :
    0 ≤ kernelMarkedFullDens J ν f β a t l r y z := by
  cases l <;> cases r
  · exact le_rfl
  · exact mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (krDens_nonneg ν hf0 _ _ _)
  · exact mul_nonneg (krDens_nonneg ν hf0 _ _ _)
      (indicator_nonneg (fun _ _ => zero_le_one) _)
  · exact kernelMarkedDens_nonneg ν hf0 _ _ _ _ _

/-- All positive-total-random-length cases represent the original row, including
an insertion at its first or last position. -/
theorem kernelMarkedRow_eq_integral_full {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D β a : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (ha : a ≠ 0) (t : ℝ) (l r : ℕ) (hlr : 1 ≤ l + r)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ z, |φ z| ≤ M) (y : ℝ) :
    kernelMarkedRow J ν β a t l r φ y =
      ∫ z, kernelMarkedFullDens J ν f β a t l r y z * φ z := by
  cases l with
  | zero =>
    cases r with
    | zero => omega
    | succ r => exact kernelMarkedRow_zero_succ ν hJ hJfin hf hf0 hfD hν ha t r hφ hM y
  | succ l =>
    cases r with
    | zero => exact kernelMarkedRow_succ_zero ν hJ hJfin hf hf0 hfD hν ha t l hφ hM y
    | succ r => exact kernelMarkedRow_succ_succ ν hJ hJfin hf hf0 hfD hν ha t l r hφ hM y

/-- The fixed density representative retains its genuine slope denominator in
the spectral bound, while the spectral constant is uniform above `a₀`. -/
theorem kernel_regLaw_density_spectral_slope (D θ vlo vhi a₀ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (ha₀ : 0 < a₀) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
      ∀ α w β a : ℝ, 1 ≤ w → a₀ ≤ |a| → ∀ n : ℕ, 1 ≤ n → ∀ y z : ℝ,
        krDens (Icc α (α + w)) ν f β a n y z ≤
          (D / |a|) * (1 + 3 * Real.sqrt (D * w / a₀)) *
            Real.exp (-(c * ((n : ℝ) - 2) / (2 * w ^ 2))) := by
  obtain ⟨c, hc, hb⟩ := kernel_norm_pure_row_regLaw_scaled D θ vlo vhi a₀ hD hθ hvlo hv ha₀
  refine ⟨c, hc, ?_⟩
  intro ν hν f hf hf0 hfD α w β a hw ha n hn y z
  have ha0 : 0 < |a| := ha₀.trans_le ha
  have hw0 : 0 < w := by linarith
  by_cases hn2 : 2 ≤ n
  · let J := Icc α (α + w)
    let φ : ℝ → ℝ := fun u => krKer J f β a u z
    have hφ : Measurable φ :=
      (measurable_krKer_prod measurableSet_Icc hf β a).comp (measurable_id.prodMk measurable_const)
    have hφD (u : ℝ) : ‖(φ u : ℂ)‖ ≤ D / |a| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_krKer_le hf0 hfD u z
    have hh := hb ν hν α w β a hw ha (fun u => (φ u : ℂ))
      (Complex.measurable_ofReal.comp hφ) (D / |a|) (div_pos hD ha0) hφD
      (n - 1) (by omega) y
    have hi : J.indicator (fun u => (φ u : ℂ)) = fun u => (φ u : ℂ) := by
      funext u
      by_cases hu : u ∈ J
      · simp only [indicator_of_mem hu]
      · simp only [indicator_of_notMem hu, φ, krKer_eq_zero_of_left_notMem hu, Complex.ofReal_zero]
    change ‖((kStep J (ν : Measure ℝ) β a)^[n - 1]
      (J.indicator (fun u => (φ u : ℂ)))) y‖ ≤ _ at hh
    rw [hi, kernel_killed_ofReal] at hh
    have hnreal : ((n - 1 : ℕ) : ℝ) - 1 = (n : ℝ) - 2 := by
      rw [Nat.cast_sub hn, Nat.cast_one]
      ring
    rw [hnreal, Complex.norm_real, Real.norm_eq_abs] at hh
    have he := kernel_krDens_eq_iterate (J := J) measurableSet_Icc ν hf hf0 hfD β a n y z
    change krDens J ν f β a n y z = ((krStep J (ν : Measure ℝ) β a)^[n - 1] φ) y at he
    rw [← he, abs_of_nonneg (krDens_nonneg ν hf0 n y z)] at hh
    apply hh.trans
    have h0 : 0 ≤ D / |a| * Real.exp (-(c * ((n : ℝ) - 2) / (2 * w ^ 2))) := by positivity
    nlinarith
  · have hn1 : n = 1 := by omega
    subst n
    have he : 1 ≤ Real.exp (-(c * ((1 : ℝ) - 2) / (2 * w ^ 2))) := by
      apply Real.one_le_exp_iff.mpr
      have hh : 0 ≤ c / (2 * w ^ 2) := by positivity
      convert hh using 1
      ring
    have hcoef : D / |a| ≤ (D / |a|) * (1 + 3 * Real.sqrt (D * w / a₀)) := by
      have hh : 0 ≤ (D / |a|) * (3 * Real.sqrt (D * w / a₀)) := by positivity
      nlinarith
    exact (krDens_le_div ν hf0 hfD 1 y z).trans
      (hcoef.trans (le_mul_of_one_le_right (by positivity) (by simpa using he)))

/-- A full marked density inherits a uniform density bound from its longest
random side. This includes an insertion adjacent to either endpoint. -/
theorem kernelFar_fullDens_le_longer {J : Set ℝ} (hJ : MeasurableSet J)
    (hJfin : volume J ≠ ⊤) (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D B β a t : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (ha : a ≠ 0) (hB : 0 ≤ B) (l r : ℕ)
    (hb : ∀ u v, krDens J ν f β a (max l r) u v ≤ B) (y z : ℝ) :
    kernelMarkedFullDens J ν f β a t l r y z ≤ B := by
  cases l with
  | zero =>
    cases r with
    | zero => exact hB
    | succ r =>
      simp only [kernelMarkedFullDens]
      by_cases hy : y ∈ J
      · simpa only [indicator_of_mem hy, one_mul, Nat.zero_max] using hb (y + β - a * t) z
      · simpa only [indicator_of_notMem hy, zero_mul] using hB
  | succ l =>
    cases r with
    | zero =>
      simp only [kernelMarkedFullDens]
      by_cases hz : z ∈ J
      · simpa only [indicator_of_mem hz, mul_one, Nat.max_zero] using hb y (z - β + a * t)
      · simpa only [indicator_of_notMem hz, mul_zero] using hB
    | succ r =>
      change kernelMarkedDens J ν f β a t (l + 1) (r + 1) y z ≤ B
      by_cases hlr : l + 1 ≤ r + 1
      · rw [max_eq_right hlr] at hb
        exact kernelFar_marked_le_right hJ hJfin ν hf hf0 hfD hν ha hB (by omega) _ y z (fun u => hb u z)
      · rw [max_eq_left (by omega : r + 1 ≤ l + 1)] at hb
        exact kernelFar_marked_le_left hJ hJfin ν hf hf0 hfD hν ha hB _ (by omega) y z (fun u => hb y u)

/-- Both genuine random pins contribute their `1 / |a|` factors; all three
random lengths occur in the exponential, including a zero insertion side. -/
theorem kernel_regLaw_full_marked_pair_spectral (D θ vlo vhi a₀ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (ha₀ : 0 < a₀) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ α w β a : ℝ, 1 ≤ w → a₀ ≤ |a| → ∀ t y z : ℝ,
      ∀ l r M : ℕ, 1 ≤ l + r → 1 ≤ M →
        kernelMarkedFullDens (Icc α (α + w)) ν f β a t l r y z *
          krDens (Icc α (α + w)) ν f β a M z y ≤
          ((D / |a|) * (1 + 3 * Real.sqrt (D * w / a₀))) ^ 2 *
            Real.exp (-(c * (((l : ℝ) + r + M) - 8) / (4 * w ^ 2))) := by
  obtain ⟨c, hc, hb⟩ := kernel_regLaw_density_spectral_slope D θ vlo vhi a₀ hD hθ hvlo hv ha₀
  refine ⟨c, hc, ?_⟩
  intro ν hν f hf hf0 hfD hνf α w β a hw ha t y z l r M hlr hM
  let J := Icc α (α + w)
  let C := (D / |a|) * (1 + 3 * Real.sqrt (D * w / a₀))
  have hC : 0 ≤ C := by positivity
  have ha0 : a ≠ 0 := by intro he; simp [he] at ha; linarith
  have hJfin : volume J ≠ ⊤ := by simp [J]
  have hmark : kernelMarkedFullDens J ν f β a t l r y z ≤
      C * Real.exp (-(c * ((max l r : ℕ) - (2 : ℝ)) / (2 * w ^ 2))) := by
    exact kernelFar_fullDens_le_longer measurableSet_Icc hJfin ν hf hf0 hfD hνf ha0
      (by positivity) l r (fun u v => hb ν hν f hf hf0 hfD α w β a hw ha (max l r)
        (by omega) u v) y z
  have hpin := hb ν hν f hf hf0 hfD α w β a hw ha M hM z y
  have hm : (l : ℝ) + r ≤ 2 * (max l r : ℕ) := by
    exact_mod_cast (show l + r ≤ 2 * max l r by omega)
  have hw0 : 0 < w := by linarith
  have hexp :
      -(c * ((max l r : ℕ) - (2 : ℝ)) / (2 * w ^ 2)) +
        -(c * ((M : ℝ) - 2) / (2 * w ^ 2)) ≤
      -(c * (((l : ℝ) + r + M) - 8) / (4 * w ^ 2)) := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * w ^ 2 by positivity)).mp
    field_simp
    nlinarith [mul_nonneg hc.le (show 0 ≤ (M : ℝ) by positivity)]
  calc
    _ ≤ (C * Real.exp (-(c * ((max l r : ℕ) - (2 : ℝ)) / (2 * w ^ 2)))) *
        (C * Real.exp (-(c * ((M : ℝ) - 2) / (2 * w ^ 2)))) :=
      mul_le_mul hmark hpin (krDens_nonneg ν hf0 _ _ _) (by positivity)
    _ = C ^ 2 * Real.exp (-(c * ((max l r : ℕ) - (2 : ℝ)) / (2 * w ^ 2)) +
        -(c * ((M : ℝ) - 2) / (2 * w ^ 2))) := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (sq_nonneg C)

end
end PGM
