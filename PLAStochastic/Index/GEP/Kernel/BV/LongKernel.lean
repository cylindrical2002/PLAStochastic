import PLAStochastic.Index.GEP.Kernel.BV.LowHighDecomposition
import PLAStochastic.Index.GEP.Kernel.BV.SpectralDecay

/-!
# Small-energy decomposition of actual long killed kernels

The low-frequency state, its two boundary traces, and the Duhamel regular part
are all constructed. The final window estimate retains the explicit spectral
decay and inverse window length from the actual killed-chain energy budget.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory FourierTransform Set Filter

theorem kBVKilledL2_preserves_rep_pow (ν : Measure ℝ) [IsProbabilityMeasure ν] (β a α : ℝ)
    {w b : ℝ} (hw : 0 ≤ w) {U : KernelL2}
    (hU : kBVHasRep (Icc α (α + w)) b U) (n : ℕ) :
    kBVHasRep (Icc α (α + w)) b
      (((kBVKilledL2 (Icc α (α + w)) measurableSet_Icc ν β a) ^ n) U) := by
  induction n with
  | zero => simpa using hU
  | succ n ih =>
    simpa only [pow_succ', mul_apply_eq_comp] using
      kBVKilledL2_preserves_rep ν β a α hw ih

/-- The constructed low-frequency cutoff gives the actual split-state estimate,
including both endpoint traces, in the `L²` quotient space. -/
theorem kBV_split_state_rep {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2)
    {α w : ℝ} (hw : 1 ≤ w) (hsupp : ∀ x, x ∉ Icc α (α + w) → u x = 0) :
    ∃ G R : KernelL2, h2.toLp u = G + R ∧
      kBVHasRep (Icc α (α + w)) (8 * Real.pi * Real.sqrt w * Real.sqrt (kBVEnergy u)) G ∧
      ‖R‖ ≤ Real.sqrt (kBVEnergy u) := by
  let g := kBVRegularPart α w u
  have hg : Measurable g := (kBVLowPass_continuous h1 h2).measurable.indicator measurableSet_Icc
  have hg2 : MemLp g 2 := (kBVLowPass_memLp h1 h2).indicator measurableSet_Icc
  have hgs : ∀ x, x ∉ Icc α (α + w) → g x = 0 := fun _ hx => indicator_of_notMem hx _
  have hg1 : Integrable g := kill_integrable_of_support
    (by simp : volume (Icc α (α + w)) ≠ ⊤) hgs hg2
  refine ⟨hg2.toLp g, h2.toLp u - hg2.toLp g, by abel,
    ⟨g, hg, hg1, hg2, rfl, hgs, kBVRegularPart_variation_le h1 h2 hw hsupp⟩, ?_⟩
  rw [← MemLp.toLp_sub h2 hg2]
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [kBV_toLp_norm_sq, Real.sq_sqrt (kBVEnergy_nonneg u)]
  exact kBVRegularPart_error_le h1 h2 hsupp

/-- Propagating the constructed split-state yields a BV regular part and a
genuinely exponentially small `L²` remainder. -/
theorem kBV_regLaw_propagated_split {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (β : ℝ) {a α w : ℝ} (ha : 1 / 2 ≤ |a|) (hw : 1 ≤ w)
    {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2)
    (hsupp : ∀ x, x ∉ Icc α (α + w) → u x = 0) (n : ℕ) :
    ∃ G R : KernelL2,
      ((kBVKilledL2 (Icc α (α + w)) measurableSet_Icc (ν : Measure ℝ) β a) ^ n)
        (h2.toLp u) = G + R ∧
      kBVHasRep (Icc α (α + w))
        ((8 * Real.pi * Real.sqrt w +
          8 * Real.pi * Real.sqrt w / (1 - Real.sqrt (1 - killCnu D vlo vhi))) *
            Real.sqrt (kBVEnergy u)) G ∧
      ‖R‖ ≤ Real.sqrt (1 - killCnu D vlo vhi) ^ n * Real.sqrt (kBVEnergy u) := by
  let J := Icc α (α + w)
  let Q := kBVKilledL2 J measurableSet_Icc (ν : Measure ℝ) β a
  let H := kBVHighStepL2 J measurableSet_Icc (ν : Measure ℝ) β a
  let ρ := Real.sqrt (1 - killCnu D vlo vhi)
  have hρ1 : ρ < 1 := kBVHighStepL2_regLaw_factor_lt_one hD hvlo
    (hν.var_ge.trans hν.var_le)
  obtain ⟨g, r, hur, hgv, hr⟩ := kBV_split_state_rep h1 h2 hw hsupp
  have hgQ := kBVKilledL2_preserves_rep_pow (ν : Measure ℝ) β a α (by linarith : 0 ≤ w) hgv n
  obtain ⟨hreg, hrem⟩ := kBV_regLaw_long_decomposition hD hθ hvlo hν β α ha hw r n
  have hc : 0 ≤ 8 * Real.pi * Real.sqrt w / (1 - ρ) := by
    apply div_nonneg (by positivity)
    linarith
  have hreg' := kBVHasRep_mono hreg (mul_le_mul_of_nonneg_left hr hc)
  have hadd := kBVHasRep_add hgQ hreg' (by positivity) (mul_nonneg hc (Real.sqrt_nonneg _))
  refine ⟨(Q ^ n) g + ((Q ^ n) r - (H ^ n) r), (H ^ n) r, ?_, ?_, ?_⟩
  · rw [hur, map_add]
    abel
  · convert hadd using 1
    ring
  · exact hrem.trans (mul_le_mul_of_nonneg_left hr (pow_nonneg (Real.sqrt_nonneg _) n))

theorem kBV_kStep_iterate_regular {J : Set ℝ} (hJ : MeasurableSet J) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (β a : ℝ) {u : ℝ → ℂ}
    (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2) (n : ℕ) :
    Measurable ((kStep J ν β a)^[n] u) ∧ Integrable ((kStep J ν β a)^[n] u) ∧
      MemLp ((kStep J ν β a)^[n] u) 2 := by
  have heq : kStepZ J ν ν 0 β a = kStep J ν β a := by
    funext v y
    simp [kStepZ]
  simpa only [heq] using kBV_iterate_regular (ν := ν) (σ := ν) hJ 0 β a hu h1 h2 n

theorem kBV_kStep_iterate_support {J : Set ℝ} (ν : Measure ℝ) (β a : ℝ) {u : ℝ → ℂ}
    (hsupp : ∀ x, x ∉ J → u x = 0) (n : ℕ) :
    ∀ x, x ∉ J → ((kStep J ν β a)^[n] u) x = 0 := by
  cases n with
  | zero => exact hsupp
  | succ n =>
    rw [Function.iterate_succ_apply']
    intro x hx
    exact indicator_of_notMem hx _

/-- Powers of the actual `L²` killed operator are the original killed integral
iterates, with no Fourier multiplier asserted for powers. -/
theorem kBVKilledL2_pow_toLp {J : Set ℝ} (hJ : MeasurableSet J) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (β a : ℝ) {u : ℝ → ℂ}
    (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2)
    (hsupp : ∀ x, x ∉ J → u x = 0) (n : ℕ) :
    ((kBVKilledL2 J hJ ν β a) ^ n) (h2.toLp u) =
      (kBV_kStep_iterate_regular hJ ν β a hu h1 h2 n).2.2.toLp ((kStep J ν β a)^[n] u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih]
    have hreg := kBV_kStep_iterate_regular hJ ν β a hu h1 h2 n
    rw [kBVKilledL2_toLp hJ ν β a hreg.1 hreg.2.1 hreg.2.2
      (kBV_kStep_iterate_support ν β a hsupp n)]
    simp only [Function.iterate_succ_apply']

/-- A fixed final time, with the sharp inverse square-root energy window and
spectral decay. Taking `m` and `N` of order `n / 4`, and `k` of order `n / 2`,
gives the long-kernel BV estimate without changing the original killed chain. -/
theorem kBV_regLaw_window_decomposition {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (β : ℝ) {a α w : ℝ} (ha : 1 / 2 ≤ |a|) (hw : 1 ≤ w)
    {u : ℝ → ℂ} (hu : Measurable u) (h2 : MemLp u 2)
    (hsupp : ∀ x, x ∉ Icc α (α + w) → u x = 0) (m N k : ℕ) (hN : 0 < N) :
    ∃ G R : KernelL2,
      ((kBVKilledL2 (Icc α (α + w)) measurableSet_Icc (ν : Measure ℝ) β a) ^ (m + N + k))
        (h2.toLp u) = G + R ∧
      kBVHasRep (Icc α (α + w))
        ((8 * Real.pi * Real.sqrt w +
          8 * Real.pi * Real.sqrt w / (1 - Real.sqrt (1 - killCnu D vlo vhi))) *
          Real.sqrt (Real.exp (-(killGapConst (killCnu D vlo vhi) (1 / 2) * m / w ^ 2)) *
            kBVNormSq u / (killCnu D vlo vhi * N))) G ∧
      ‖R‖ ≤ Real.sqrt (1 - killCnu D vlo vhi) ^ k *
        Real.sqrt (Real.exp (-(killGapConst (killCnu D vlo vhi) (1 / 2) * m / w ^ 2)) *
          kBVNormSq u / (killCnu D vlo vhi * N)) := by
  let J := Icc α (α + w)
  let Q := kBVKilledL2 J measurableSet_Icc (ν : Measure ℝ) β a
  let ρ := Real.sqrt (1 - killCnu D vlo vhi)
  let B := Real.exp (-(killGapConst (killCnu D vlo vhi) (1 / 2) * m / w ^ 2)) *
    kBVNormSq u / (killCnu D vlo vhi * N)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ < 1 := kBVHighStepL2_regLaw_factor_lt_one hD hvlo
    (hν.var_ge.trans hν.var_le)
  have h1 : Integrable u := kill_integrable_of_support
    (by simp : volume (Icc α (α + w)) ≠ ⊤) hsupp h2
  obtain ⟨j, hj, hE⟩ := kBV_regLaw_exists_small_energy_exp hD hθ hvlo hν hw β ha hu hsupp h2 m N hN
  have hreg := kBV_kStep_iterate_regular (J := Icc α (α + w)) measurableSet_Icc
    (ν : Measure ℝ) β a hu h1 h2 (m + j)
  have hsup := kBV_kStep_iterate_support (ν : Measure ℝ) β a hsupp (m + j)
  obtain ⟨G, R, hGR, hGV, hR⟩ := kBV_regLaw_propagated_split hD hθ hvlo hν β ha hw
    hreg.2.1 hreg.2.2 hsup (N - j + k)
  refine ⟨G, R, ?_, ?_, ?_⟩
  · change (Q ^ (m + N + k)) (h2.toLp u) = G + R
    have hn : m + N + k = (N - j + k) + (m + j) := by omega
    rw [hn, pow_add, mul_apply_eq_comp]
    rw [kBVKilledL2_pow_toLp measurableSet_Icc (ν : Measure ℝ) β a hu h1 h2 hsupp]
    exact hGR
  · apply kBVHasRep_mono hGV
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE)
    apply add_nonneg (by positivity)
    exact div_nonneg (by positivity) (by linarith : 0 ≤ 1 - ρ)
  · have hp : ρ ^ (N - j + k) ≤ ρ ^ k := by
      rw [pow_add]
      exact mul_le_of_le_one_left (pow_nonneg hρ0 k) (pow_le_one₀ hρ0 hρ1.le)
    exact hR.trans (mul_le_mul hp (Real.sqrt_le_sqrt hE)
      (Real.sqrt_nonneg _) (pow_nonneg hρ0 k))

/-- Specialization to every long-chain length. The floor terms are retained so
that all finite-time constants and the geometric remainder are explicit. -/
theorem kBV_regLaw_n_decomposition {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (β : ℝ) {a α w : ℝ} (ha : 1 / 2 ≤ |a|) (hw : 1 ≤ w)
    {u : ℝ → ℂ} (hu : Measurable u) (h2 : MemLp u 2)
    (hsupp : ∀ x, x ∉ Icc α (α + w) → u x = 0) (n : ℕ) (hn : 8 ≤ n) :
    ∃ G R : KernelL2,
      ((kBVKilledL2 (Icc α (α + w)) measurableSet_Icc (ν : Measure ℝ) β a) ^ n)
        (h2.toLp u) = G + R ∧
      kBVHasRep (Icc α (α + w))
        ((8 * Real.pi * Real.sqrt w +
          8 * Real.pi * Real.sqrt w / (1 - Real.sqrt (1 - killCnu D vlo vhi))) *
          Real.sqrt (Real.exp (-(killGapConst (killCnu D vlo vhi) (1 / 2) * (n / 4 : ℕ) / w ^ 2)) *
            kBVNormSq u / (killCnu D vlo vhi * (n / 4 : ℕ)))) G ∧
      ‖R‖ ≤ Real.sqrt (1 - killCnu D vlo vhi) ^ (n / 2) *
        Real.sqrt (Real.exp (-(killGapConst (killCnu D vlo vhi) (1 / 2) * (n / 4 : ℕ) / w ^ 2)) *
          kBVNormSq u / (killCnu D vlo vhi * (n / 4 : ℕ))) := by
  have hN : 0 < n / 4 := by omega
  obtain ⟨G, R, hGR, hG, hR⟩ := kBV_regLaw_window_decomposition hD hθ hvlo hν β ha hw hu h2
    hsupp (n / 4) (n / 4) (n - 2 * (n / 4)) hN
  have hsum : n / 4 + n / 4 + (n - 2 * (n / 4)) = n := by omega
  have hρ1 := kBVHighStepL2_regLaw_factor_lt_one hD hvlo (hν.var_ge.trans hν.var_le)
  refine ⟨G, R, by simpa only [hsum] using hGR, hG, hR.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact pow_le_pow_of_le_one (Real.sqrt_nonneg _) hρ1.le (by omega : n / 2 ≤ n - 2 * (n / 4))

/-- Quotient-space decompositions give exact pointwise decompositions of the
original representative. The remainder retains interval support and both
integrability properties; its norm is the proved `L²` remainder norm. -/
theorem kBV_decomposition_representatives {J : Set ℝ} {b : ℝ} {u : ℝ → ℂ}
    (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2)
    (hsupp : ∀ x, x ∉ J → u x = 0) {G R : KernelL2}
    (hGR : h2.toLp u = G + R) (hG : kBVHasRep J b G) :
    ∃ g r : ℝ → ℂ, Measurable g ∧ Integrable g ∧ MemLp g 2 ∧
      Measurable r ∧ Integrable r ∧ MemLp r 2 ∧
      (∀ x, x ∉ J → g x = 0 ∧ r x = 0) ∧
      (∀ x, u x = g x + r x) ∧ eVariationOn g univ ≤ ENNReal.ofReal b ∧
      kBVNormSq r = ‖R‖ ^ 2 := by
  rcases hG with ⟨g, hg, hg1, hg2, hgG, hgs, hgv⟩
  refine ⟨g, u - g, hg, hg1, hg2, hu.sub hg, h1.sub hg1, h2.sub hg2, ?_, ?_, hgv, ?_⟩
  · intro x hx
    exact ⟨hgs x hx, by simp [hsupp x hx, hgs x hx]⟩
  · intro x
    simp only [Pi.sub_apply]
    abel
  · rw [← kBV_toLp_norm_sq (h2.sub hg2), MemLp.toLp_sub h2 hg2, hGR, hgG]
    congr 2
    abel

end
end PGM
