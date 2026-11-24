import PLAStochastic.Index.GEP.LayerLaw.ActualLayers
import Mathlib.Probability.Independence.Integration

/-!
# WP4 leaf 4A-S, part 1: change of measure and single-gap insertion on the iid space

Measure-theoretic tools for the score calculus along mixture paths
(`research/2026-09-28-gep-closure/joint-response.md` §5, `influence-lipschitz.md` §8 (mix),
`positive-direction-response.md` §8.3 (33)–(35)).  Everything is stated on the canonical iid
space `iidLaw ν` of `PLAStochastic/Index/GEP/LayerLaw/Defs.lean`.

* `DepPrefix t G`: `G` reads only `g 0, …, g (t-1)`.
* `iidLaw_withDensity_prod`: if `μ = r · ν`, then `(∏_{j<t} r(g_j)) · iidLaw ν` is the
  product law with `μ` in the first `t` coordinates and `ν` afterwards (`eq_infinitePi` and
  independence of the coordinates).
* `lintegral_iidLaw_prefix`, `integral_iidLaw_prefix`: the finite-dimensional likelihood ratio,
  `E_μ[G] = E_ν[G ∏_{j<t} r(g_j)]` for `G` reading the first `t` coordinates.
* `map_update_iidLaw`, `lintegral_update`, `integral_update`: inserting an independent
  `ν`-distributed value at coordinate `i` does not change the law, hence
  `E[G] = ∫ E[G(g with g_i := y)] ν(dy)` (the single-gap insertion of PD (33)).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-- `G` reads only the first `t` coordinates `g 0, …, g (t-1)`. -/
def DepPrefix {β : Type*} (t : ℕ) (G : (ℕ → ℝ) → β) : Prop :=
  ∀ g g' : ℕ → ℝ, (∀ i < t, g i = g' i) → G g = G g'

/-- The coordinates of the canonical space are independent. -/
theorem iIndepFun_coord (ν : ProbabilityMeasure ℝ) :
    iIndepFun (fun (i : ℕ) (g : ℕ → ℝ) => g i) (iidLaw ν) :=
  (iidSeq_gapCoord ν).indep

theorem lintegral_coord (ν : ProbabilityMeasure ℝ) (i : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f (g i) ∂(iidLaw ν) = ∫⁻ y, f y ∂(ν : Measure ℝ) := by
  have h : (iidLaw ν).map (fun g : ℕ → ℝ => g i) = (ν : Measure ℝ) :=
    Measure.infinitePi_map_eval _ i
  rw [← h, lintegral_map hf (measurable_pi_apply i)]

/-! ## The likelihood ratio of the first `t` coordinates -/

/-- The indicator of a box is the product of the coordinate indicators. -/
theorem indicator_pi_one (s : Finset ℕ) (A : ℕ → Set ℝ) (g : ℕ → ℝ) :
    (Set.pi (s : Set ℕ) A).indicator (fun _ => (1 : ℝ≥0∞)) g =
      ∏ i ∈ s, (A i).indicator (fun _ => (1 : ℝ≥0∞)) (g i) := by
  classical
  by_cases hg : g ∈ Set.pi (s : Set ℕ) A
  · rw [Set.indicator_of_mem hg]
    refine (Finset.prod_eq_one fun i hi => ?_).symm
    exact Set.indicator_of_mem (hg i hi) _
  · rw [Set.indicator_of_notMem hg]
    simp only [Set.mem_pi, Finset.mem_coe, not_forall] at hg
    obtain ⟨i, hi, hgi⟩ := hg
    exact (Finset.prod_eq_zero hi (Set.indicator_of_notMem hgi _)).symm

/-- **The finite-dimensional likelihood ratio.**  If `μ = r · ν`, weighting `iidLaw ν` by
`∏_{j<t} r(g_j)` gives the product law with `μ` in the first `t` coordinates. -/
theorem iidLaw_withDensity_prod (ν μ : ProbabilityMeasure ℝ) {r : ℝ → ℝ≥0∞} (hr : Measurable r)
    (hμ : (μ : Measure ℝ) = (ν : Measure ℝ).withDensity r) (t : ℕ) :
    (iidLaw ν).withDensity (fun g => ∏ j ∈ Finset.range t, r (g j)) =
      Measure.infinitePi (fun j : ℕ => if j < t then (μ : Measure ℝ) else ν) := by
  classical
  have : ∀ j : ℕ, IsProbabilityMeasure (if j < t then (μ : Measure ℝ) else ν) := fun j => by
    split_ifs <;> infer_instance
  refine Measure.eq_infinitePi _ fun s A hA => ?_
  set Y : ℕ → ℝ → ℝ≥0∞ := fun i y =>
    (if i ∈ s then (A i).indicator (fun _ => (1 : ℝ≥0∞)) y else 1) *
      (if i ∈ Finset.range t then r y else 1) with hY
  have hYm : ∀ i, Measurable (Y i) := fun i => by
    refine Measurable.mul ?_ ?_
    · split_ifs
      · exact measurable_const.indicator (hA i)
      · exact measurable_const
    · split_ifs
      · exact hr
      · exact measurable_const
  have hset : MeasurableSet (Set.pi (s : Set ℕ) A) :=
    MeasurableSet.pi s.countable_toSet fun i _ => hA i
  have hpt : ∀ g : ℕ → ℝ, (Set.pi (s : Set ℕ) A).indicator
      (fun g => ∏ j ∈ Finset.range t, r (g j)) g = ∏ i ∈ s ∪ Finset.range t, Y i (g i) := by
    intro g
    rw [hY]
    simp only
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, ← indicator_pi_one]
    by_cases hg : g ∈ Set.pi (s : Set ℕ) A
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, one_mul]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
  have hind : iIndepFun (fun i (g : ℕ → ℝ) => Y i (g i)) (iidLaw ν) :=
    (iIndepFun_coord ν).comp (fun i => Y i) hYm
  rw [withDensity_apply _ hset, ← lintegral_indicator hset]
  simp_rw [hpt]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hind
    (fun i => (hYm i).comp (measurable_pi_apply i))]
  simp_rw [lintegral_coord ν _ (hYm _)]
  have hdisj : Disjoint s (Finset.range t \ s) := Finset.disjoint_sdiff
  rw [show s ∪ Finset.range t = s ∪ (Finset.range t \ s) by simp,
    Finset.prod_union hdisj]
  have h2 : ∏ i ∈ Finset.range t \ s, ∫⁻ y, Y i y ∂(ν : Measure ℝ) = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    rw [Finset.mem_sdiff] at hi
    simp only [hY, if_neg hi.2, if_pos hi.1, one_mul]
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hμ, measure_univ]
  rw [h2, mul_one]
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [hY, if_pos hi]
  by_cases hit : i < t
  · have hit' : i ∈ Finset.range t := Finset.mem_range.2 hit
    simp only [if_pos hit', if_pos hit]
    rw [hμ, withDensity_apply _ (hA i), ← lintegral_indicator (hA i)]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ A i
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  · have hit' : i ∉ Finset.range t := fun h => hit (Finset.mem_range.1 h)
    simp only [if_neg hit', if_neg hit, mul_one]
    rw [lintegral_indicator (hA i), setLIntegral_const, one_mul]

/-- Extension of a vector on `Finset.range t` by zero. -/
def prefixExt (t : ℕ) (v : Finset.range t → ℝ) : ℕ → ℝ :=
  fun j => if h : j ∈ Finset.range t then v ⟨j, h⟩ else 0

theorem measurable_prefixExt (t : ℕ) : Measurable (prefixExt t) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases h : j ∈ Finset.range t
  · simp only [prefixExt, h, dif_pos]
    exact measurable_pi_apply _
  · simp only [prefixExt, h, dif_neg, not_false_eq_true]
    exact measurable_const

theorem DepPrefix.eq_comp {β : Type*} {t : ℕ} {G : (ℕ → ℝ) → β} (hG : DepPrefix t G) :
    G = (G ∘ prefixExt t) ∘ (Finset.range t).restrict := by
  funext g
  refine hG _ _ fun i hi => ?_
  simp [prefixExt, Finset.mem_range.2 hi]

/-- Two product laws that agree on the first `t` coordinates have the same law of the first `t`
coordinates. -/
theorem map_restrict_infinitePi_eq {μ₁ μ₂ : ℕ → Measure ℝ} [∀ i, IsProbabilityMeasure (μ₁ i)]
    [∀ i, IsProbabilityMeasure (μ₂ i)] {t : ℕ} (h : ∀ i < t, μ₁ i = μ₂ i) :
    (Measure.infinitePi μ₁).map (Finset.range t).restrict =
      (Measure.infinitePi μ₂).map (Finset.range t).restrict := by
  rw [Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  congr 1
  funext i
  exact h i (Finset.mem_range.1 i.2)

theorem lintegral_infinitePi_prefix {μ₁ μ₂ : ℕ → Measure ℝ} [∀ i, IsProbabilityMeasure (μ₁ i)]
    [∀ i, IsProbabilityMeasure (μ₂ i)] {t : ℕ} (h : ∀ i < t, μ₁ i = μ₂ i)
    {G : (ℕ → ℝ) → ℝ≥0∞} (hG : Measurable G) (hdep : DepPrefix t G) :
    ∫⁻ g, G g ∂(Measure.infinitePi μ₁) = ∫⁻ g, G g ∂(Measure.infinitePi μ₂) := by
  have hm : Measurable (G ∘ prefixExt t) := hG.comp (measurable_prefixExt t)
  have e : ∀ m : Measure (ℕ → ℝ), ∫⁻ g, G g ∂m =
      ∫⁻ v, (G ∘ prefixExt t) v ∂(m.map (Finset.range t).restrict) := fun m => by
    rw [lintegral_map hm (Finset.measurable_restrict _)]
    conv_lhs => rw [hdep.eq_comp]
    rfl
  rw [e, e, map_restrict_infinitePi_eq h]

theorem integral_infinitePi_prefix {μ₁ μ₂ : ℕ → Measure ℝ} [∀ i, IsProbabilityMeasure (μ₁ i)]
    [∀ i, IsProbabilityMeasure (μ₂ i)] {t : ℕ} (h : ∀ i < t, μ₁ i = μ₂ i)
    {G : (ℕ → ℝ) → ℝ} (hG : Measurable G) (hdep : DepPrefix t G) :
    ∫ g, G g ∂(Measure.infinitePi μ₁) = ∫ g, G g ∂(Measure.infinitePi μ₂) := by
  have hm : Measurable (G ∘ prefixExt t) := hG.comp (measurable_prefixExt t)
  have e : ∀ m : Measure (ℕ → ℝ), ∫ g, G g ∂m =
      ∫ v, (G ∘ prefixExt t) v ∂(m.map (Finset.range t).restrict) := fun m => by
    rw [integral_map (Finset.measurable_restrict _).aemeasurable hm.aestronglyMeasurable]
    conv_lhs => rw [hdep.eq_comp]
    rfl
  rw [e, e, map_restrict_infinitePi_eq h]

/-- **Likelihood ratio of a prefix functional** (lintegral form). -/
theorem lintegral_iidLaw_prefix (ν μ : ProbabilityMeasure ℝ) {r : ℝ → ℝ≥0∞} (hr : Measurable r)
    (hμ : (μ : Measure ℝ) = (ν : Measure ℝ).withDensity r) {t : ℕ} {G : (ℕ → ℝ) → ℝ≥0∞}
    (hG : Measurable G) (hdep : DepPrefix t G) :
    ∫⁻ g, G g ∂(iidLaw μ) = ∫⁻ g, (∏ j ∈ Finset.range t, r (g j)) * G g ∂(iidLaw ν) := by
  have : ∀ j : ℕ, IsProbabilityMeasure (if j < t then (μ : Measure ℝ) else ν) := fun j => by
    split_ifs <;> infer_instance
  have hD : Measurable fun g : ℕ → ℝ => ∏ j ∈ Finset.range t, r (g j) :=
    Finset.measurable_prod _ fun j _ => hr.comp (measurable_pi_apply j)
  have e := lintegral_withDensity_eq_lintegral_mul (iidLaw ν) hD hG
  simp only [Pi.mul_apply] at e
  rw [← e, iidLaw_withDensity_prod ν μ hr hμ t, iidLaw]
  exact lintegral_infinitePi_prefix (fun i hi => by simp [hi]) hG hdep

/-- **Likelihood ratio of a prefix functional** (integral form, `NNReal` density). -/
theorem integral_iidLaw_prefix (ν μ : ProbabilityMeasure ℝ) {r : ℝ → ℝ≥0} (hr : Measurable r)
    (hμ : (μ : Measure ℝ) = (ν : Measure ℝ).withDensity (fun y => (r y : ℝ≥0∞))) {t : ℕ}
    {G : (ℕ → ℝ) → ℝ} (hG : Measurable G) (hdep : DepPrefix t G) :
    ∫ g, G g ∂(iidLaw μ) = ∫ g, (∏ j ∈ Finset.range t, (r (g j) : ℝ)) * G g ∂(iidLaw ν) := by
  have : ∀ j : ℕ, IsProbabilityMeasure (if j < t then (μ : Measure ℝ) else ν) := fun j => by
    split_ifs <;> infer_instance
  have hD : Measurable fun g : ℕ → ℝ => ∏ j ∈ Finset.range t, r (g j) :=
    Finset.measurable_prod _ fun j _ => hr.comp (measurable_pi_apply j)
  have hW := iidLaw_withDensity_prod ν μ (r := fun y => (r y : ℝ≥0∞)) hr.coe_nnreal_ennreal hμ t
  have hW' : (iidLaw ν).withDensity (fun g => ((∏ j ∈ Finset.range t, r (g j) : ℝ≥0) : ℝ≥0∞)) =
      Measure.infinitePi (fun j : ℕ => if j < t then (μ : Measure ℝ) else ν) := by
    rw [← hW]
    congr 1
    funext g
    push_cast
    rfl
  have e := integral_withDensity_eq_integral_smul hD (μ := iidLaw ν) G
  rw [hW', ← integral_infinitePi_prefix (μ₁ := fun _ : ℕ => (μ : Measure ℝ))
    (fun i hi => by simp [hi]) hG hdep] at e
  rw [iidLaw, e]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, NNReal.coe_prod]

/-! ## Single-gap insertion -/

/-- **Insertion does not change the law**: `update g i y` with `y ~ ν` independent of
`g ~ iidLaw ν` is again `iidLaw ν`. -/
theorem map_update_iidLaw (ν : ProbabilityMeasure ℝ) (i : ℕ) :
    ((ν : Measure ℝ).prod (iidLaw ν)).map
      (fun p : ℝ × (ℕ → ℝ) => Function.update p.2 i p.1) = iidLaw ν := by
  classical
  have hU : Measurable fun p : ℝ × (ℕ → ℝ) => Function.update p.2 i p.1 :=
    measurable_update'.comp measurable_swap
  have : IsProbabilityMeasure (((ν : Measure ℝ).prod (iidLaw ν)).map
      (fun p : ℝ × (ℕ → ℝ) => Function.update p.2 i p.1)) :=
    Measure.isProbabilityMeasure_map hU.aemeasurable
  refine Measure.eq_infinitePi _ fun s A hA => ?_
  have hset : MeasurableSet (Set.pi (s : Set ℕ) A) :=
    MeasurableSet.pi s.countable_toSet fun i _ => hA i
  have hpre : (fun p : ℝ × (ℕ → ℝ) => Function.update p.2 i p.1) ⁻¹' Set.pi (s : Set ℕ) A =
      (if i ∈ s then A i else univ) ×ˢ Set.pi ((s.erase i : Finset ℕ) : Set ℕ) A := by
    ext ⟨y, g⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
    constructor
    · intro h
      refine ⟨?_, fun j ⟨hji, hj⟩ => ?_⟩
      · split_ifs with hi
        · simpa using h i hi
        · exact mem_univ _
      · simpa [Function.update_of_ne hji] using h j hj
    · rintro ⟨h1, h2⟩ j hj
      by_cases hji : j = i
      · subst hji
        simpa [if_pos hj] using h1
      · simpa [Function.update_of_ne hji] using h2 j ⟨hji, hj⟩
  rw [Measure.map_apply hU hset, hpre, Measure.prod_prod, iidLaw,
    Measure.infinitePi_pi _ (fun j _ => hA j)]
  by_cases hi : i ∈ s
  · rw [if_pos hi, Finset.mul_prod_erase s (fun j => (ν : Measure ℝ) (A j)) hi]
  · rw [if_neg hi, measure_univ, one_mul, Finset.erase_eq_of_notMem hi]

theorem measurable_update_pair (i : ℕ) :
    Measurable fun p : ℝ × (ℕ → ℝ) => Function.update p.2 i p.1 := by
  classical
  exact measurable_update'.comp measurable_swap

/-- **Single-gap insertion** (lintegral form): `E[G] = ∫ E[G(g_i := y)] ν(dy)`. -/
theorem lintegral_update (ν : ProbabilityMeasure ℝ) (i : ℕ) {G : (ℕ → ℝ) → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ g, G g ∂(iidLaw ν) =
      ∫⁻ y, ∫⁻ g, G (Function.update g i y) ∂(iidLaw ν) ∂(ν : Measure ℝ) := by
  conv_lhs => rw [← map_update_iidLaw ν i]
  rw [lintegral_map hG (measurable_update_pair i),
    lintegral_prod (fun p : ℝ × (ℕ → ℝ) => G (Function.update p.2 i p.1))
      (hG.comp (measurable_update_pair i)).aemeasurable]

/-- **Single-gap insertion** (integral form). -/
theorem integral_update (ν : ProbabilityMeasure ℝ) (i : ℕ) {G : (ℕ → ℝ) → ℝ}
    (hGm : Measurable G) (hG : Integrable G (iidLaw ν)) :
    ∫ g, G g ∂(iidLaw ν) =
      ∫ y, ∫ g, G (Function.update g i y) ∂(iidLaw ν) ∂(ν : Measure ℝ) := by
  have hU := measurable_update_pair i
  have hG' : Integrable (G ∘ fun p : ℝ × (ℕ → ℝ) => Function.update p.2 i p.1)
      ((ν : Measure ℝ).prod (iidLaw ν)) := by
    rw [← integrable_map_measure hGm.aestronglyMeasurable hU.aemeasurable, map_update_iidLaw]
    exact hG
  conv_lhs => rw [← map_update_iidLaw ν i]
  rw [integral_map hU.aemeasurable hGm.aestronglyMeasurable]
  exact integral_prod _ hG'

/-- Integrability of the inserted functional in the inserted value. -/
theorem integrable_update (ν : ProbabilityMeasure ℝ) (i : ℕ) {G : (ℕ → ℝ) → ℝ}
    (hGm : Measurable G) (hG : Integrable G (iidLaw ν)) :
    Integrable (fun y => ∫ g, G (Function.update g i y) ∂(iidLaw ν)) (ν : Measure ℝ) := by
  have hU := measurable_update_pair i
  have hG' : Integrable (G ∘ fun p : ℝ × (ℕ → ℝ) => Function.update p.2 i p.1)
      ((ν : Measure ℝ).prod (iidLaw ν)) := by
    rw [← integrable_map_measure hGm.aestronglyMeasurable hU.aemeasurable, map_update_iidLaw]
    exact hG
  exact hG'.integral_prod_left

theorem measurable_integral_update (ν : ProbabilityMeasure ℝ) (i : ℕ) {G : (ℕ → ℝ) → ℝ}
    (hGm : Measurable G) :
    Measurable (fun y => ∫ g, G (Function.update g i y) ∂(iidLaw ν)) :=
  ((hGm.comp (measurable_update_pair i)).stronglyMeasurable.integral_prod_right'
    (ν := iidLaw ν)).measurable

/-! ## Functionals of the stopped path -/

/-- `Φ` is a functional of the stopped path: on `{T = t}` it reads only `g 0, …, g (t-1)`. -/
def IsStoppedFn {β : Type*} (eps : ℝ) (Φ : (ℕ → ℝ) → β) : Prop :=
  ∀ (t : ℕ) (g g' : ℕ → ℝ), gapSegLen eps g = t → (∀ i < t, g i = g' i) → Φ g = Φ g'

/-- `{t < T}` reads only the first `t` gaps. -/
theorem lt_gapSegLen_congr {eps : ℝ} {t : ℕ} {g g' : ℕ → ℝ} (h : ∀ i < t, g i = g' i) :
    (t : ℕ∞) < gapSegLen eps g ↔ (t : ℕ∞) < gapSegLen eps g' :=
  mem_iff_of_measurableSet_comap_seqPrefix (isStoppingRule_gapSegLen eps t) h

/-- `{T = t}` reads only the first `t` gaps. -/
theorem gapSegLen_eq_congr {eps : ℝ} {t : ℕ} {g g' : ℕ → ℝ} (h : ∀ i < t, g i = g' i) :
    gapSegLen eps g = t ↔ gapSegLen eps g' = t :=
  mem_iff_of_measurableSet_comap_seqPrefix ((isStoppingRule_gapSegLen eps).measurableSet_eq t) h

theorem measurableSet_gapSegLen_eq (eps : ℝ) (t : ℕ) :
    MeasurableSet {g : ℕ → ℝ | gapSegLen eps g = t} :=
  (isStoppingRule_gapSegLen eps).measurable (measurableSet_singleton (t : ℕ∞))

theorem measurableSet_lt_gapSegLen (eps : ℝ) (t : ℕ) :
    MeasurableSet {g : ℕ → ℝ | (t : ℕ∞) < gapSegLen eps g} :=
  (isStoppingRule_gapSegLen eps).measurableSet_lt t

theorem measurable_gapSegLen_toNat (eps : ℝ) :
    Measurable fun g : ℕ → ℝ => (gapSegLen eps g).toNat :=
  (Measurable.of_discrete (f := ENat.toNat)).comp (isStoppingRule_gapSegLen eps).measurable

theorem IsStoppedFn.depPrefix_indicator {β : Type*} [Zero β] {eps : ℝ} {Φ : (ℕ → ℝ) → β}
    (hΦ : IsStoppedFn eps Φ) (t : ℕ) :
    DepPrefix t ({g | gapSegLen eps g = t}.indicator Φ) := by
  intro g g' h
  by_cases hg : gapSegLen eps g = t
  · have hg' : gapSegLen eps g' = t := (gapSegLen_eq_congr h).1 hg
    rw [Set.indicator_of_mem (show g ∈ {g | gapSegLen eps g = t} from hg),
      Set.indicator_of_mem (show g' ∈ {g | gapSegLen eps g = t} from hg'), hΦ t g g' hg h]
  · have hg' : ¬ gapSegLen eps g' = t := fun h' => hg ((gapSegLen_eq_congr h).2 h')
    rw [Set.indicator_of_notMem (show g ∉ {g | gapSegLen eps g = t} from hg),
      Set.indicator_of_notMem (show g' ∉ {g | gapSegLen eps g = t} from hg')]

theorem IsStoppedFn.comp {β γ : Type*} {eps : ℝ} {Φ : (ℕ → ℝ) → β} (hΦ : IsStoppedFn eps Φ)
    (f : β → γ) : IsStoppedFn eps (fun g => f (Φ g)) := fun t g g' hT h => by
  simp only [hΦ t g g' hT h]

/-- The likelihood ratio of the stopped path, `∏_{j < T} r(g_j)`. -/
def stopLik (eps : ℝ) {β : Type*} [CommMonoid β] (r : ℝ → β) (g : ℕ → ℝ) : β :=
  ∏ j ∈ Finset.range (gapSegLen eps g).toNat, r (g j)

/-- An a.s. finite stopping time: `Φ` is the sum of its pieces on `{T = t}`. -/
theorem tsum_indicator_gapSegLen_eq {eps : ℝ} {Φ : (ℕ → ℝ) → ℝ≥0∞} {g : ℕ → ℝ}
    (hg : gapSegLen eps g ≠ ⊤) (w : ℕ → ℝ≥0∞) :
    ∑' t, w t * {g | gapSegLen eps g = t}.indicator Φ g = w (gapSegLen eps g).toNat * Φ g := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
  rw [tsum_eq_single n]
  · rw [Set.indicator_of_mem (show g ∈ {g | gapSegLen eps g = n} from hn.symm), ← hn,
      ENat.toNat_natCast]
  · intro t ht
    rw [Set.indicator_of_notMem (show g ∉ {g | gapSegLen eps g = t} by
      simp only [Set.mem_ofPred_eq, ← hn, Nat.cast_inj]; exact fun h => ht h.symm), mul_zero]

/-- **Change of measure for stopped functionals** (lintegral form): if `μ = r · ν` and `T` is
a.s. finite under both laws, `E_μ[Φ] = E_ν[Φ ∏_{j<T} r(g_j)]`. -/
theorem lintegral_stopped (eps : ℝ) (ν μ : ProbabilityMeasure ℝ) {r : ℝ → ℝ≥0∞}
    (hr : Measurable r) (hμ : (μ : Measure ℝ) = (ν : Measure ℝ).withDensity r)
    (hfinμ : ∀ᵐ g ∂(iidLaw μ), gapSegLen eps g ≠ ⊤)
    (hfinν : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    {Φ : (ℕ → ℝ) → ℝ≥0∞} (hΦm : Measurable Φ) (hΦ : IsStoppedFn eps Φ) :
    ∫⁻ g, Φ g ∂(iidLaw μ) = ∫⁻ g, stopLik eps r g * Φ g ∂(iidLaw ν) := by
  have hIm : ∀ t : ℕ, Measurable ({g : ℕ → ℝ | gapSegLen eps g = t}.indicator Φ) := fun t =>
    hΦm.indicator (measurableSet_gapSegLen_eq eps t)
  have hD : ∀ t, Measurable fun g : ℕ → ℝ => ∏ j ∈ Finset.range t, r (g j) := fun t =>
    Finset.measurable_prod _ fun j _ => hr.comp (measurable_pi_apply j)
  calc ∫⁻ g, Φ g ∂(iidLaw μ)
      = ∫⁻ g, ∑' t : ℕ, (1 : ℝ≥0∞) * {g | gapSegLen eps g = t}.indicator Φ g ∂(iidLaw μ) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfinμ] with g hg
        rw [tsum_indicator_gapSegLen_eq hg (fun _ => 1), one_mul]
    _ = ∑' t : ℕ, ∫⁻ g, {g | gapSegLen eps g = t}.indicator Φ g ∂(iidLaw μ) := by
        simp_rw [one_mul]
        exact lintegral_tsum fun t => (hIm t).aemeasurable
    _ = ∑' t : ℕ, ∫⁻ g, (∏ j ∈ Finset.range t, r (g j)) *
          {g | gapSegLen eps g = t}.indicator Φ g ∂(iidLaw ν) := by
        congr 1
        funext t
        exact lintegral_iidLaw_prefix ν μ hr hμ (hIm t) (hΦ.depPrefix_indicator t)
    _ = ∫⁻ g, ∑' t : ℕ, (∏ j ∈ Finset.range t, r (g j)) *
          {g | gapSegLen eps g = t}.indicator Φ g ∂(iidLaw ν) :=
        (lintegral_tsum fun t => ((hD t).mul (hIm t)).aemeasurable).symm
    _ = ∫⁻ g, stopLik eps r g * Φ g ∂(iidLaw ν) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfinν] with g hg
        rw [tsum_indicator_gapSegLen_eq hg (fun t => ∏ j ∈ Finset.range t, r (g j)), stopLik]

theorem measurable_stopLik (eps : ℝ) {r : ℝ → ℝ} (hr : Measurable r) :
    Measurable (stopLik eps r) := by
  have hm : Measurable fun p : (ℕ → ℝ) × ℕ => ∏ j ∈ Finset.range p.2, r (p.1 j) :=
    measurable_from_prod_countable_left fun n => by
      change Measurable fun x : ℕ → ℝ => ∏ j ∈ Finset.range n, r (x j)
      exact Finset.measurable_prod _ fun j _ => hr.comp (measurable_pi_apply j)
  exact hm.comp (measurable_id.prodMk (measurable_gapSegLen_toNat eps))

/-- **Change of measure for stopped functionals** (integral form, `NNReal` density). -/
theorem integral_stopped (eps : ℝ) (ν μ : ProbabilityMeasure ℝ) {r : ℝ → ℝ≥0}
    (hr : Measurable r) (hμ : (μ : Measure ℝ) = (ν : Measure ℝ).withDensity (fun y => (r y : ℝ≥0∞)))
    (hfinμ : ∀ᵐ g ∂(iidLaw μ), gapSegLen eps g ≠ ⊤)
    (hfinν : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    {Φ : (ℕ → ℝ) → ℝ} (hΦm : Measurable Φ) (hΦ : IsStoppedFn eps Φ) :
    (Integrable Φ (iidLaw μ) ↔
      Integrable (fun g => stopLik eps (fun y => (r y : ℝ)) g * Φ g) (iidLaw ν)) ∧
    ∫ g, Φ g ∂(iidLaw μ) = ∫ g, stopLik eps (fun y => (r y : ℝ)) g * Φ g ∂(iidLaw ν) := by
  have hr' : Measurable fun y => (r y : ℝ≥0∞) := hr.coe_nnreal_ennreal
  have hL : ∀ g, ENNReal.ofReal (stopLik eps (fun y => (r y : ℝ)) g) =
      stopLik eps (fun y => (r y : ℝ≥0∞)) g := fun g => by
    simp only [stopLik]
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => NNReal.coe_nonneg (r (g j)))]
    exact Finset.prod_congr rfl fun j _ => ENNReal.ofReal_coe_nnreal
  have hL0 : ∀ g, 0 ≤ stopLik eps (fun y => (r y : ℝ)) g := fun g =>
    Finset.prod_nonneg fun j _ => NNReal.coe_nonneg (r (g j))
  have hLm : Measurable (stopLik eps (fun y => (r y : ℝ))) :=
    measurable_stopLik eps hr.coe_nnreal_real
  -- the transfer of a real stopped functional through `ofReal`
  have htr : ∀ {Ψ : (ℕ → ℝ) → ℝ}, Measurable Ψ → IsStoppedFn eps Ψ →
      ∫⁻ g, ENNReal.ofReal (Ψ g) ∂(iidLaw μ) =
        ∫⁻ g, ENNReal.ofReal (stopLik eps (fun y => (r y : ℝ)) g * Ψ g) ∂(iidLaw ν) := by
    intro Ψ hΨm hΨ
    rw [lintegral_stopped eps ν μ hr' hμ hfinμ hfinν hΨm.ennreal_ofReal
      (hΨ.comp ENNReal.ofReal)]
    refine lintegral_congr fun g => ?_
    rw [ENNReal.ofReal_mul (hL0 g), hL]
  have hnorm : ∫⁻ g, ‖Φ g‖ₑ ∂(iidLaw μ) =
      ∫⁻ g, ‖stopLik eps (fun y => (r y : ℝ)) g * Φ g‖ₑ ∂(iidLaw ν) := by
    simp_rw [← ofReal_norm]
    rw [htr hΦm.norm (hΦ.comp (fun x => ‖x‖))]
    refine lintegral_congr fun g => ?_
    rw [norm_mul, Real.norm_of_nonneg (hL0 g)]
  have hiff : Integrable Φ (iidLaw μ) ↔
      Integrable (fun g => stopLik eps (fun y => (r y : ℝ)) g * Φ g) (iidLaw ν) := by
    rw [Integrable, Integrable, hasFiniteIntegral_iff_enorm, hasFiniteIntegral_iff_enorm, hnorm]
    exact ⟨fun h => ⟨(hLm.mul hΦm).aestronglyMeasurable, h.2⟩,
      fun h => ⟨hΦm.aestronglyMeasurable, h.2⟩⟩
  refine ⟨hiff, ?_⟩
  by_cases hint : Integrable Φ (iidLaw μ)
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hiff.1 hint),
      htr hΦm hΦ, htr (Ψ := fun g => -Φ g) hΦm.neg (hΦ.comp (fun x => -x))]
    congr 3
    funext g
    rw [mul_neg]
  · rw [integral_undef hint, integral_undef (fun h => hint (hiff.2 h))]

/-- Change of measure for sums of prefix functionals (lintegral form). -/
theorem lintegral_tsum_prefix (ν μ : ProbabilityMeasure ℝ) {r : ℝ → ℝ≥0∞} (hr : Measurable r)
    (hμ : (μ : Measure ℝ) = (ν : Measure ℝ).withDensity r) {G : ℕ → (ℕ → ℝ) → ℝ≥0∞}
    (hGm : ∀ k, Measurable (G k)) (hG : ∀ k, DepPrefix k (G k)) :
    ∫⁻ g, ∑' k, G k g ∂(iidLaw μ) =
      ∫⁻ g, ∑' k, (∏ j ∈ Finset.range k, r (g j)) * G k g ∂(iidLaw ν) := by
  have hD : ∀ t, Measurable fun g : ℕ → ℝ => ∏ j ∈ Finset.range t, r (g j) := fun t =>
    Finset.measurable_prod _ fun j _ => hr.comp (measurable_pi_apply j)
  rw [lintegral_tsum fun k => (hGm k).aemeasurable,
    lintegral_tsum (f := fun k g => (∏ j ∈ Finset.range k, r (g j)) * G k g)
      fun k => ((hD k).mul (hGm k)).aemeasurable]
  congr 1
  funext k
  exact lintegral_iidLaw_prefix ν μ hr hμ (hGm k) (hG k)

end

end PGM
