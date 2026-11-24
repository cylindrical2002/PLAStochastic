import PLAStochastic.Index.GEP.Kernel.Facet.ActiveRoot

/-!
# Distinct effective facets and negligible ties

Effectiveness is proved from actual positive-gap roots in `GEPKernelFacetActive`.
It excludes zero-block degeneracies. Positive tolerance is needed to distinguish
the two orientations of a single triple.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

theorem kernel_facet_coef_left {eps : ℝ} {k j : ℕ} {q : FluxFacetIndex k}
    (hq : fluxFacetValid q) (hrj : (q.1 : ℕ) ≤ j) (hjs : j < q.2.1) :
    fluxFacetCoef eps q j = -fluxFacetSign q *
      (((q.2.2.1 : ℕ) : ℝ) - q.2.1 + 2 * fluxFacetSign q * eps) := by
  have hjt : j < q.2.2.1 := lt_trans hjs hq.2
  have hjr : ¬j < q.1 := by omega
  simp only [fluxFacetCoef, hq, if_true, hjt, hjs, hjr, if_false]
  ring

theorem kernel_facet_coef_right {eps : ℝ} {k j : ℕ} {q : FluxFacetIndex k}
    (hq : fluxFacetValid q) (hsj : (q.2.1 : ℕ) ≤ j) (hjt : j < q.2.2.1) :
    fluxFacetCoef eps q j = fluxFacetSign q *
      (((q.2.1 : ℕ) : ℝ) - q.1 - 2 * fluxFacetSign q * eps) := by
  have hjs : ¬j < q.2.1 := by omega
  have hjr : ¬j < q.1 := by have := hq.1; omega
  simp only [fluxFacetCoef, hq, if_true, hjt, hjs, hjr, if_false]
  ring

theorem kernel_facet_coef_eq_zero_outside {eps : ℝ} {k j : ℕ} {q : FluxFacetIndex k}
    (hj : j < q.1 ∨ (q.2.2.1 : ℕ) ≤ j) : fluxFacetCoef eps q j = 0 := by
  by_cases hq : fluxFacetValid q
  · rcases hj with hj | hj
    · have hjs : j < q.2.1 := lt_trans hj hq.1
      have hjt : j < q.2.2.1 := lt_trans hjs hq.2
      simp [fluxFacetCoef, hq, hj, hjs, hjt]
    · have hjs : ¬j < q.2.1 := by have := hq.2; omega
      have hjr : ¬j < q.1 := by have := hq.1; have := hq.2; omega
      have hjt : ¬j < q.2.2.1 := by omega
      simp [fluxFacetCoef, hq, hjr, hjs, hjt]
  · simp [fluxFacetCoef, hq]

theorem kernel_facet_coef_support {eps : ℝ} {k j : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) :
    fluxFacetCoef eps q j ≠ 0 ↔ (q.1 : ℕ) ≤ j ∧ j < q.2.2.1 := by
  constructor
  · intro hc
    by_contra h
    apply hc
    apply kernel_facet_coef_eq_zero_outside
    omega
  · rintro ⟨hrj, hjt⟩
    by_cases hjs : j < q.2.1
    · rw [kernel_facet_coef_left hq.1 hrj hjs]
      exact mul_ne_zero (neg_ne_zero.mpr (kernel_fluxFacetSign_ne_zero q)) hq.2.2.ne'
    · rw [kernel_facet_coef_right hq.1 (by omega) hjt]
      exact mul_ne_zero (kernel_fluxFacetSign_ne_zero q) hq.2.1.ne'

theorem kernel_facet_coef_jump_ne {eps : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : fluxFacetValid q) :
    fluxFacetCoef eps q q.1 ≠ fluxFacetCoef eps q q.2.1 := by
  rw [kernel_facet_coef_left hq le_rfl hq.1,
    kernel_facet_coef_right hq le_rfl hq.2]
  have hrt : (q.1 : ℝ) < q.2.2.1 := by exact_mod_cast lt_trans hq.1 hq.2
  rcases kernel_fluxFacetSign_cases q with hs | hs <;> rw [hs] <;>
    intro h <;> nlinarith

/-- Proportional effective coefficient vectors have the same support endpoints
and the same unique internal jump. -/
theorem kernel_facet_proportional_indices {eps cScale : ℝ} {k : ℕ}
    {q p : FluxFacetIndex k} (hq : kernelFacetEffective eps q)
    (hp : kernelFacetEffective eps p) (hcScale : cScale ≠ 0)
    (hc : ∀ j < k, fluxFacetCoef eps q j = cScale * fluxFacetCoef eps p j) :
    q.1 = p.1 ∧ q.2.1 = p.2.1 ∧ q.2.2.1 = p.2.2.1 := by
  have hqrs : (q.1 : ℕ) < q.2.1 := hq.1.1
  have hqst : (q.2.1 : ℕ) < q.2.2.1 := hq.1.2
  have hprs : (p.1 : ℕ) < p.2.1 := hp.1.1
  have hpst : (p.2.1 : ℕ) < p.2.2.1 := hp.1.2
  have hsupport (j : ℕ) (hj : j < k) :
      ((q.1 : ℕ) ≤ j ∧ j < q.2.2.1) ↔ ((p.1 : ℕ) ≤ j ∧ j < p.2.2.1) := by
    rw [← kernel_facet_coef_support hq, ← kernel_facet_coef_support hp,
      hc j hj, mul_ne_zero_iff]
    exact and_iff_right hcScale
  have hqrk : (q.1 : ℕ) < k := by have := hq.1; omega
  have hprk : (p.1 : ℕ) < k := by have := hp.1; omega
  have hpr := ((hsupport q.1 hqrk).mp ⟨le_rfl, lt_trans hq.1.1 hq.1.2⟩).1
  have hqr := ((hsupport p.1 hprk).mpr ⟨le_rfl, lt_trans hp.1.1 hp.1.2⟩).1
  have hr : q.1 = p.1 := Fin.ext (by omega)
  have hqt : (q.2.2.1 : ℕ) - 1 < k := by have := hq.1; omega
  have hpt : (p.2.2.1 : ℕ) - 1 < k := by have := hp.1; omega
  have ht₁ := ((hsupport ((q.2.2.1 : ℕ) - 1) hqt).mp (by have := hq.1; omega)).2
  have ht₂ := ((hsupport ((p.2.2.1 : ℕ) - 1) hpt).mpr (by have := hp.1; omega)).2
  have ht : q.2.2.1 = p.2.2.1 := Fin.ext (by omega)
  have heq : fluxFacetCoef eps q q.1 = cScale * fluxFacetCoef eps p p.1 := by
    simpa only [hr] using hc q.1 hqrk
  have hsqk : (q.2.1 : ℕ) < k := by have := hq.1; omega
  have hspk : (p.2.1 : ℕ) < k := by have := hp.1; omega
  have hs : q.2.1 = p.2.1 := by
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hpflat : fluxFacetCoef eps p q.2.1 = fluxFacetCoef eps p p.1 := by
        rw [kernel_facet_coef_left hp.1 (by rw [← hr]; exact hq.1.1.le) hlt,
          kernel_facet_coef_left hp.1 le_rfl hp.1.1]
      have hh := hc q.2.1 hsqk
      rw [hpflat] at hh
      exact kernel_facet_coef_jump_ne hq.1 (heq.trans hh.symm)
    · have hqflat : fluxFacetCoef eps q p.2.1 = fluxFacetCoef eps q q.1 := by
        rw [kernel_facet_coef_left hq.1 (by rw [hr]; exact hp.1.1.le) hlt,
          kernel_facet_coef_left hq.1 le_rfl hq.1.1]
      have hh := hc p.2.1 hspk
      rw [hqflat, heq] at hh
      exact kernel_facet_coef_jump_ne hp.1 ((mul_left_cancel₀ hcScale hh))
  exact ⟨hr, hs, ht⟩

/-- For positive tolerance, distinct effective facets define nonproportional
hyperplanes, including the two orientations of a fixed triple. -/
theorem kernel_facet_proportional_eq {eps cScale : ℝ} {k : ℕ}
    {q p : FluxFacetIndex k} (heps : 0 < eps) (hq : kernelFacetEffective eps q)
    (hp : kernelFacetEffective eps p) (hcScale : cScale ≠ 0)
    (hc : ∀ j < k, fluxFacetCoef eps q j = cScale * fluxFacetCoef eps p j) : q = p := by
  obtain ⟨hr, hs, ht⟩ := kernel_facet_proportional_indices hq hp hcScale hc
  have hqrs : (q.1 : ℕ) < q.2.1 := hq.1.1
  have hqst : (q.2.1 : ℕ) < q.2.2.1 := hq.1.2
  have hqrk : (q.1 : ℕ) < k := by have := hq.1; omega
  have hqsk : (q.2.1 : ℕ) < k := by have := hq.1; omega
  have hl := hc q.1 hqrk
  have hh := hc q.2.1 hqsk
  rw [kernel_facet_coef_left hq.1 le_rfl hq.1.1,
    kernel_facet_coef_left hp.1 (by rw [hr]) (by rw [hr]; exact hp.1.1)] at hl
  rw [kernel_facet_coef_right hq.1 le_rfl hq.1.2,
    kernel_facet_coef_right hp.1 (by rw [hs]) (by rw [hs]; exact hp.1.2)] at hh
  simp only [hr, hs, ht] at hl hh
  have hsig : fluxFacetSign q = fluxFacetSign p := by
    have hrt : (p.1 : ℝ) < p.2.2.1 := by exact_mod_cast lt_trans hp.1.1 hp.1.2
    have hdet : (-fluxFacetSign q *
        (((p.2.2.1 : ℕ) : ℝ) - p.2.1 + 2 * fluxFacetSign q * eps)) *
        (fluxFacetSign p * (((p.2.1 : ℕ) : ℝ) - p.1 - 2 * fluxFacetSign p * eps)) =
        (fluxFacetSign q * (((p.2.1 : ℕ) : ℝ) - p.1 - 2 * fluxFacetSign q * eps)) *
        (-fluxFacetSign p * (((p.2.2.1 : ℕ) : ℝ) - p.2.1 + 2 * fluxFacetSign p * eps)) := by
      rw [hl, hh]
      ring
    rcases kernel_fluxFacetSign_cases q with hqσ | hqσ <;>
      rcases kernel_fluxFacetSign_cases p with hpσ | hpσ <;>
      rw [hqσ, hpσ] at hdet ⊢ <;> nlinarith [mul_pos heps (sub_pos.mpr hrt)]
  have hb : q.2.2.2 = p.2.2.2 := by
    cases hqb : q.2.2.2 <;> cases hpb : p.2.2.2 <;>
      simp_all [fluxFacetSign] <;> norm_num at hsig
  exact Prod.ext hr (Prod.ext hs (Prod.ext ht hb))

/-- Distinct effective roots retain a nonzero coefficient after deleting the
inserted gap. Thus equality of the roots is a genuine remaining-gap hyperplane. -/
theorem kernel_facet_root_difference_nonzero {eps : ℝ} {k i : ℕ}
    {q p : FluxFacetIndex k} (heps : 0 < eps) (hq : kernelFacetEffective eps q)
    (hp : kernelFacetEffective eps p) (hne : q ≠ p)
    (hqi : fluxFacetCoef eps q i ≠ 0) (hpi : fluxFacetCoef eps p i ≠ 0) :
    ∃ j ∈ (range k).erase i,
      kernelFacetRootCoef eps q i j - kernelFacetRootCoef eps p i j ≠ 0 := by
  by_contra h
  have he : ∀ j ∈ (range k).erase i,
      kernelFacetRootCoef eps q i j = kernelFacetRootCoef eps p i j := by
    simpa only [not_exists, not_and, not_not, sub_eq_zero] using h
  apply hne
  apply kernel_facet_proportional_eq heps hq hp (div_ne_zero hqi hpi)
  intro j hj
  by_cases hji : j = i
  · subst j
    field_simp [hpi]
  · have hh := he j (mem_erase.mpr ⟨hji, mem_range.mpr hj⟩)
    unfold kernelFacetRootCoef at hh
    have hh' := (div_eq_div_iff hqi hpi).mp hh
    calc
      fluxFacetCoef eps q j =
          (fluxFacetCoef eps q i * fluxFacetCoef eps p j) / fluxFacetCoef eps p i :=
        (eq_div_iff hpi).mpr (by nlinarith)
      _ = _ := by ring

theorem kernel_iid_linear_zero_mass (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (T : Finset ℕ) (c : ℕ → ℝ) {j : ℕ} (hj : j ∈ T) (hc : c j ≠ 0)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((iidLaw ν).withDensity W) {g | (∑ l ∈ T, c l * g l) = 0} = 0 := by
  have hmap := kernel_iid_linear_map_density ν hf hν T c hj hc hW
  have hnull : (((iidLaw ν).withDensity W).map
      (fun g => ∑ l ∈ T, c l * g l)) {0} = 0 := by
    rw [hmap]
    exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton (a := 0))
  have hm : Measurable (fun g : ℕ → ℝ => ∑ l ∈ T, c l * g l) := by fun_prop
  rw [Measure.map_apply hm (measurableSet_singleton 0)] at hnull
  exact hnull

/-- Full-path measurable weights do not restore mass to simultaneous distinct
effective facet roots. The conclusion allows infinite total weighted mass. -/
theorem kernel_distinct_facet_tie_zero (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i : ℕ} {q p : FluxFacetIndex k} (heps : 0 < eps)
    (hq : kernelFacetEffective eps q) (hp : kernelFacetEffective eps p) (hne : q ≠ p)
    (hqi : fluxFacetCoef eps q i ≠ 0) (hpi : fluxFacetCoef eps p i ≠ 0)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((iidLaw ν).withDensity W) {g |
      fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i =
      fluxPrefixRHS eps k i p g / fluxFacetCoef eps p i} = 0 := by
  obtain ⟨j, hj, hc⟩ := kernel_facet_root_difference_nonzero heps hq hp hne hqi hpi
  have he : {g : ℕ → ℝ |
      fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i =
        fluxPrefixRHS eps k i p g / fluxFacetCoef eps p i} =
      {g | (∑ l ∈ (range k).erase i,
        (kernelFacetRootCoef eps q i l - kernelFacetRootCoef eps p i l) * g l) = 0} := by
    ext g
    simp only [mem_ofPred_eq, kernel_facet_root_eq_sum, sub_mul, sum_sub_distrib,
      sub_eq_zero]
  rw [he]
  exact kernel_iid_linear_zero_mass ν hf hν _ _ hj hc hW

/-- Almost every actual positive-gap section has at most one facet at any
positive root. Effectiveness and nonzero coefficients are derived, not assumed. -/
theorem kernel_positive_root_unique_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i : ℕ} (heps : 0 < eps) (hi : i < k)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ∀ᵐ g ∂(iidLaw ν).withDensity W,
      (∀ j < k, j ≠ i → 0 < g j) → ∀ x : ℝ, 0 < x →
      ∀ q p : FluxFacetIndex k,
        x = fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i →
        x = fluxPrefixRHS eps k i p g / fluxFacetCoef eps p i → q = p := by
  have ha (q p : FluxFacetIndex k) :
      ∀ᵐ g ∂(iidLaw ν).withDensity W,
        kernelFacetEffective eps q → kernelFacetEffective eps p → q ≠ p →
        fluxFacetCoef eps q i ≠ 0 → fluxFacetCoef eps p i ≠ 0 →
        fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i ≠
          fluxPrefixRHS eps k i p g / fluxFacetCoef eps p i := by
    by_cases hq : kernelFacetEffective eps q
    · by_cases hp : kernelFacetEffective eps p
      · by_cases hne : q ≠ p
        · by_cases hqi : fluxFacetCoef eps q i ≠ 0
          · by_cases hpi : fluxFacetCoef eps p i ≠ 0
            · have hz := kernel_distinct_facet_tie_zero ν hf hν heps hq hp hne hqi hpi hW
              exact (measure_eq_zero_iff_ae_notMem.mp hz).mono fun g hg _ _ _ _ _ => hg
            · exact Filter.Eventually.of_forall fun _ _ _ _ _ h => (hpi h).elim
          · exact Filter.Eventually.of_forall fun _ _ _ _ h => (hqi h).elim
        · exact Filter.Eventually.of_forall fun _ _ _ h => (hne h).elim
      · exact Filter.Eventually.of_forall fun _ _ h => (hp h).elim
    · exact Filter.Eventually.of_forall fun _ h => (hq h).elim
  have hall := ae_all_iff.mpr fun q => ae_all_iff.mpr fun p => ha q p
  filter_upwards [hall] with g hg
  intro hpos x hx q p hq hp
  by_contra hne
  have hc (v : FluxFacetIndex k)
      (hv : x = fluxPrefixRHS eps k i v g / fluxFacetCoef eps v i) :
      fluxFacetCoef eps v i ≠ 0 := by
    intro he
    rw [he, div_zero] at hv
    exact (ne_of_gt hx) hv
  exact hg q p (kernel_active_root_effective hi q g hx hpos hq)
    (kernel_active_root_effective hi p g hx hpos hp) hne (hc q hq) (hc p hp)
    (hq.symm.trans hp)

/-- The entire pushforward contribution of a tie is the zero measure. -/
theorem kernel_facet_tie_pushforward_zero (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i : ℕ} {q p : FluxFacetIndex k} (heps : 0 < eps)
    (hq : kernelFacetEffective eps q) (hp : kernelFacetEffective eps p) (hne : q ≠ p)
    (hqi : fluxFacetCoef eps q i ≠ 0) (hpi : fluxFacetCoef eps p i ≠ 0)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) (E : (ℕ → ℝ) → ℝ) :
    (((iidLaw ν).withDensity W).restrict {g |
      fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i =
        fluxPrefixRHS eps k i p g / fluxFacetCoef eps p i}).map E = 0 := by
  rw [Measure.restrict_eq_zero.mpr
    (kernel_distinct_facet_tie_zero ν hf hν heps hq hp hne hqi hpi hW), Measure.map_zero]

def kernelFacetTieSet (eps : ℝ) (k i : ℕ) (q p : FluxFacetIndex k) : Set (ℕ → ℝ) :=
  {g | fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i =
    fluxPrefixRHS eps k i p g / fluxFacetCoef eps p i}

theorem measurableSet_kernelFacetTieSet (eps : ℝ) (k i : ℕ) (q p : FluxFacetIndex k) :
    MeasurableSet (kernelFacetTieSet eps k i q p) :=
  measurableSet_eq_fun ((measurable_fluxPrefixRHS eps k i q).div_const _)
    ((measurable_fluxPrefixRHS eps k i p).div_const _)

/-- The explicit root density of a tie contribution vanishes almost everywhere.
This asserts no arbitrary pointwise value of an RN representative. -/
theorem kernel_facet_tie_density_ae_zero (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i : ℕ} {q p : FluxFacetIndex k} (heps : 0 < eps)
    (hq : kernelFacetEffective eps q) (hp : kernelFacetEffective eps p) (hne : q ≠ p)
    (hqi : fluxFacetCoef eps q i ≠ 0) (hpi : fluxFacetCoef eps p i ≠ 0)
    {m : ℕ} (hm : m ∈ (range k).erase i) (hqm : kernelFacetRootCoef eps q i m ≠ 0)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    kernelFacetRootDensity ν f eps k i q m
      ((kernelFacetTieSet eps k i q p).indicator W) =ᵐ[volume] 0 := by
  have hS := measurableSet_kernelFacetTieSet eps k i q p
  have hmD : Measurable (kernelFacetRootDensity ν f eps k i q m
      ((kernelFacetTieSet eps k i q p).indicator W)) := by
    exact measurable_kernelLinearDensity (iidLaw ν) _
      (by fun_prop) (measurable_kernelIIDRootWeight hf _ (hW.indicator hS))
  apply (withDensity_eq_zero_iff hmD.aemeasurable).mp
  rw [← kernel_facet_root_weighted_density ν hf hν eps k i q hm hqm (hW.indicator hS),
    withDensity_indicator hS, ← restrict_withDensity hS]
  exact kernel_facet_tie_pushforward_zero ν hf hν heps hq hp hne hqi hpi hW _

end
end PGM
