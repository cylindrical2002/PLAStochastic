import PLAStochastic.Index.GEP.Kernel.Flux.Prefix.ThreePointConstraints
import PLAStochastic.Index.GEP.Kernel.Flux.Sections.PolyPrimitive
import PLAStochastic.Index.GEP.PointwiseSmall.LengthKernelBound

/-!
# Actual one-gap prefix probabilities are integral primitives

The affine constraints here are exactly the original prefix feasibility event,
with the original `Function.update` convention.  Their random endpoints are
selected homogeneous linear forms of the other gaps.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset

abbrev FluxFacetIndex (k : ℕ) := Fin (k + 1) × Fin (k + 1) × Fin (k + 1) × Bool

def fluxFacetSign {k : ℕ} (q : FluxFacetIndex k) : ℝ := if q.2.2.2 then 1 else -1

def fluxFacetValid {k : ℕ} (q : FluxFacetIndex k) : Prop := q.1 < q.2.1 ∧ q.2.1 < q.2.2.1

instance {k : ℕ} (q : FluxFacetIndex k) : Decidable (fluxFacetValid q) :=
  inferInstanceAs (Decidable (q.1 < q.2.1 ∧ q.2.1 < q.2.2.1))

/-- The coefficient of one gap in an oriented facet inequality. -/
def fluxFacetCoef (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) (j : ℕ) : ℝ :=
  if fluxFacetValid q then
    fluxFacetSign q *
      ((((q.2.1 : ℕ) : ℝ) - q.1 - 2 * fluxFacetSign q * eps) *
          ((if j < q.2.2.1 then 1 else 0) - (if j < q.2.1 then 1 else 0)) -
        (((q.2.2.1 : ℕ) : ℝ) - q.2.1 + 2 * fluxFacetSign q * eps) *
          ((if j < q.2.1 then 1 else 0) - (if j < q.1 then 1 else 0)))
  else 0

theorem flux_gapKeys_sum (g : ℕ → ℝ) {n k : ℕ} (hn : n ≤ k) :
    gapKeys g n = ∑ j ∈ range k, if j < n then g j else 0 := by
  rw [← sum_filter]
  have he : (range k).filter (fun j => j < n) = range n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]
  rfl

theorem fluxFacetCoef_sum (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (hq : fluxFacetValid q) (g : ℕ → ℝ) :
    (∑ j ∈ range k, fluxFacetCoef eps q j * g j) = fluxFacetSign q *
      fluxFacet ((q.2.1 : ℕ) - (q.1 : ℝ)) ((q.2.2.1 : ℕ) - (q.2.1 : ℝ))
        eps (fluxFacetSign q) (gapKeys g q.2.1 - gapKeys g q.1)
        (gapKeys g q.2.2.1 - gapKeys g q.2.1) := by
  rw [flux_gapKeys_sum g (by omega : (q.1 : ℕ) ≤ k),
    flux_gapKeys_sum g (by omega : (q.2.1 : ℕ) ≤ k),
    flux_gapKeys_sum g (by omega : (q.2.2.1 : ℕ) ≤ k)]
  simp only [fluxFacet, mul_sub, mul_sum]
  simp only [← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  simp only [fluxFacetCoef, hq, if_true]
  split_ifs <;> ring

theorem flux_prefix_iff_constraints {eps : ℝ} {g : ℕ → ℝ} {k : ℕ}
    (hk : 2 ≤ k) (hg : ∀ j < k, 0 < g j) :
    prefixAffineFeasible eps (gapKeys g) (k + 1) ↔
      ∀ q : FluxFacetIndex k, ∑ j ∈ range k, fluxFacetCoef eps q j * g j ≤ 0 := by
  classical
  have hord : ∀ r s, r < s → s < k + 1 → gapKeys g r < gapKeys g s :=
    fun r s hrs hs => cert_gapKeys_lt hg r s hrs (by omega)
  rw [kernel_prefix_feasible_iff_facets (by omega) hord]
  constructor
  · intro hf q
    by_cases hq : fluxFacetValid q
    · rw [fluxFacetCoef_sum eps q hq g]
      obtain ⟨h1, h2⟩ := hf q.1 q.2.1 q.2.2.1 hq.1 hq.2 q.2.2.1.isLt
      cases hb : q.2.2.2
      · simp only [fluxFacetSign, hb, Bool.false_eq_true, if_false, neg_one_mul]
        linarith
      · simpa only [fluxFacetSign, hb, if_true, one_mul] using h1
    · simp only [fluxFacetCoef, hq, if_false, zero_mul, sum_const_zero, le_refl]
  · intro hf r s t hrs hst htk
    let q₁ : FluxFacetIndex k := (⟨r, by omega⟩, ⟨s, by omega⟩, ⟨t, htk⟩, true)
    let q₂ : FluxFacetIndex k := (⟨r, by omega⟩, ⟨s, by omega⟩, ⟨t, htk⟩, false)
    have hv₁ : fluxFacetValid q₁ := ⟨hrs, hst⟩
    have hv₂ : fluxFacetValid q₂ := ⟨hrs, hst⟩
    have h1 := hf q₁
    have h2 := hf q₂
    rw [fluxFacetCoef_sum eps q₁ hv₁ g] at h1
    rw [fluxFacetCoef_sum eps q₂ hv₂ g] at h2
    simpa only [q₁, q₂, fluxFacetSign, if_true, Bool.false_eq_true, if_false,
      one_mul, neg_one_mul, neg_nonpos] using And.intro h1 h2

/-- The actual random right-hand side after removing the inserted gap. -/
def fluxPrefixRHS (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k) (g : ℕ → ℝ) : ℝ :=
  - ∑ j ∈ (range k).erase i, fluxFacetCoef eps q j * g j

theorem measurable_fluxPrefixRHS (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k) :
    Measurable (fluxPrefixRHS eps k i q) :=
  (Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_pi_apply j)).neg

theorem flux_prefix_update_iff {eps x : ℝ} {g : ℕ → ℝ} {k i : ℕ}
    (hk : 2 ≤ k) (hi : i < k) (hx : 0 < x) (hg : ∀ j < k, j ≠ i → 0 < g j) :
    prefixAffineFeasible eps (gapKeys (Function.update g i x)) (k + 1) ↔
      ∀ q : FluxFacetIndex k, fluxFacetCoef eps q i * x ≤ fluxPrefixRHS eps k i q g := by
  classical
  have hpos : ∀ j < k, 0 < Function.update g i x j := by
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa using hx
    · simpa only [Function.update_of_ne hji] using hg j hj hji
  rw [flux_prefix_iff_constraints hk hpos]
  apply forall_congr'
  intro q
  rw [← Finset.sum_erase_add (range k) (fun j => fluxFacetCoef eps q j * Function.update g i x j)
    (mem_range.mpr hi), Function.update_self]
  have he : (∑ j ∈ (range k).erase i, fluxFacetCoef eps q j * Function.update g i x j) =
      ∑ j ∈ (range k).erase i, fluxFacetCoef eps q j * g j := by
    apply sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [he]
  unfold fluxPrefixRHS
  constructor <;> intro h <;> linarith

/-- Each actual facet root has a positive-local density, including the possible
identically zero root. No nondegeneracy assumption is added to the gap model. -/
theorem fluxPrefixRHS_root_ac {ν : ProbabilityMeasure ℝ} (hν : (ν : Measure ℝ) ≪ volume)
    (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k) :
    ((iidLaw ν).map (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)).restrict
      (Ioi 0) ≪ volume := by
  have he : (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i) =
      fun g => ∑ j ∈ (range k).erase i, (-fluxFacetCoef eps q j / fluxFacetCoef eps q i) * g j := by
    funext g
    simp only [fluxPrefixRHS, neg_div, sum_div, ← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    ring
  rw [he]
  exact flux_infinitePi_linear_ac_positive _ _ (fun _ _ => hν)

/-- The actual finite-prefix section under any finite measure dominated by
the original iid law. Restriction to a survival window is allowed. -/
theorem flux_prefix_measure_aePrimitive {ν : ProbabilityMeasure ℝ}
    (hac : (ν : Measure ℝ) ≪ volume) (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    (P : Measure (ℕ → ℝ)) [IsFiniteMeasure P] (hP : P ≪ iidLaw ν)
    (eps : ℝ) {k i : ℕ} (hk : 2 ≤ k) (hi : i < k) :
    ∃ j : ℝ → ℝ,
      AEPrimitive (fun x => P.real {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}) j ∧
      Integrable j ∧ (∫ x, ‖j x‖) ≤ 2 * P.real univ := by
  have hgs : ∀ᵐ g ∂iidLaw ν, ∀ l, 0 < g l := by
    rw [ae_all_iff]
    intro l
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) l).quasiMeasurePreserving
      |>.ae hpos
  have hgsP : ∀ᵐ g ∂P, ∀ l, 0 < g l := hP hgs
  have hroot (q : FluxFacetIndex k) :
      (P.map (fun g => fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)).restrict (Ioi 0) ≪ volume :=
    ((hP.map ((measurable_fluxPrefixRHS eps k i q).div_const _)).restrict (Ioi 0)).trans
      (fluxPrefixRHS_root_ac hac eps k i q)
  obtain ⟨j, hj, hiJ, hb⟩ := fluxPoly_aePrimitive P (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)
    (fun q => measurable_fluxPrefixRHS eps k i q) hroot
  obtain ⟨hI, a, ha⟩ := hj
  refine ⟨j, ⟨hI, a, ?_⟩, hiJ, hb⟩
  filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
  have he : P.real {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)} =
      P.real {g | ∀ q : FluxFacetIndex k, fluxFacetCoef eps q i * x ≤ fluxPrefixRHS eps k i q g} := by
    apply measureReal_congr
    refine hgsP.mono fun g hg => ?_
    change ((k : ℕ∞) < gapSegLen eps (Function.update g i x)) = _
    apply propext
    rw [gapSegLen, lt_segLen_iff]
    exact flux_prefix_update_iff hk hi hx (fun l _ _ => hg l)
  rw [he]
  exact hax

/-- The finite, actual one-gap survival probability has an integrable a.e.
derivative. This is the original `pwQ`, not a substituted influence kernel. -/
theorem flux_pwQ_aePrimitive {ν : ProbabilityMeasure ℝ}
    (hac : (ν : Measure ℝ) ≪ volume) (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    (eps : ℝ) {k i : ℕ} (hk : 2 ≤ k) (hi : i < k) :
    ∃ j : ℝ → ℝ, AEPrimitive (pwQ eps ν k i) j ∧ Integrable j ∧ (∫ x, ‖j x‖) ≤ 2 := by
  change ∃ j : ℝ → ℝ,
    AEPrimitive (fun x => (iidLaw ν).real {g | (k : ℕ∞) < gapSegLen eps (Function.update g i x)}) j ∧
      Integrable j ∧ (∫ x, ‖j x‖) ≤ 2
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
    flux_prefix_measure_aePrimitive hac hpos (iidLaw ν) Measure.AbsolutelyContinuous.rfl eps hk hi

end

end PGM
