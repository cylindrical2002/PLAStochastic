import PLAStochastic.ForMathlib.MeasureTheory.Constructions.Projective.CountableExtension
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic

/-!
# Projective extension for arbitrary families of real coordinates

First realize every countable restriction by conditional kernels. A decreasing
sequence of cylinder sets depends on only countably many coordinates, so its
content is continuous from above. Carathéodory then produces the actual global
probability measure with the prescribed finite-dimensional laws.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Classical
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {ι κ : Type*}

def realReindexMap (f : ι ↪ κ) (I : Finset ι) : (I.map f → ℝ) → (I → ℝ) :=
  fun x i => x ⟨f i, Finset.mem_map.mpr ⟨i, i.property, rfl⟩⟩

theorem measurable_realReindexMap (f : ι ↪ κ) (I : Finset ι) :
    Measurable (realReindexMap f I) := by
  unfold realReindexMap
  fun_prop

def realReindexedFamily (f : ι ↪ κ) (P : (I : Finset κ) → Measure (I → ℝ))
    (I : Finset ι) : Measure (I → ℝ) :=
  (P (I.map f)).map (realReindexMap f I)

instance (f : ι ↪ κ) (P : (I : Finset κ) → Measure (I → ℝ))
    [∀ I, IsProbabilityMeasure (P I)] (I : Finset ι) :
    IsProbabilityMeasure (realReindexedFamily f P I) := by
  unfold realReindexedFamily
  exact Measure.isProbabilityMeasure_map (measurable_realReindexMap f I).aemeasurable

theorem realReindexedFamily_projective (f : ι ↪ κ)
    (P : (I : Finset κ) → Measure (I → ℝ))
    (hP : IsProjectiveMeasureFamily (α := fun _ : κ => ℝ) P) :
    IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) (realReindexedFamily f P) := by
  intro I J hJI
  unfold realReindexedFamily
  rw [hP (I.map f) (J.map f) (Finset.map_subset_map.mpr hJI)]
  rw [Measure.map_map (measurable_realReindexMap f J) (Finset.measurable_restrict₂ _),
    Measure.map_map (Finset.measurable_restrict₂ _) (measurable_realReindexMap f I)]
  rfl

private theorem map_real_finset_transport (P : (I : Finset ι) → Measure (I → ℝ))
    {I J : Finset ι} (h : I = J) :
    (P I).map (fun x => fun i : J => x ⟨i, h.symm ▸ i.property⟩) = P J := by
  subst J
  exact Measure.map_id

/-- A projective probability family on any countable set of real coordinates has a limit. -/
theorem exists_countable_real_projectiveLimit [Countable ι]
    (P : (I : Finset ι) → Measure (I → ℝ)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) P) :
    ∃ ν : Measure (ι → ℝ), IsProbabilityMeasure ν ∧
      IsProjectiveLimit (α := fun _ : ι => ℝ) ν P := by
  classical
  cases finite_or_infinite ι with
  | inl hf =>
    let := Fintype.ofFinite ι
    let f : (Finset.univ (α := ι) → ℝ) → (ι → ℝ) := fun x i => x ⟨i, Finset.mem_univ i⟩
    have hm : Measurable f := by fun_prop
    refine ⟨(P Finset.univ).map f, Measure.isProbabilityMeasure_map hm.aemeasurable, ?_⟩
    intro I
    rw [Measure.map_map (Finset.measurable_restrict _) hm]
    exact (hP Finset.univ I (Finset.subset_univ _)).symm
  | inr hi =>
    obtain ⟨e, _⟩ := Classical.exists_true_of_nonempty (α := ℕ ≃ ι) nonempty_equiv_of_countable
    obtain ⟨μ, hμ, hlim⟩ := exists_real_nat_projectiveLimit (realReindexedFamily e.toEmbedding P)
      (realReindexedFamily_projective e.toEmbedding P hP)
    let := hμ
    let f : (ℕ → ℝ) → (ι → ℝ) := fun x i => x (e.symm i)
    have hm : Measurable f := by fun_prop
    refine ⟨μ.map f, Measure.isProbabilityMeasure_map hm.aemeasurable, ?_⟩
    intro I
    let J := I.preimage e e.injective.injOn
    have hJI : J.map e.toEmbedding = I := by
      ext i
      simp [J]
    let g : (J → ℝ) → (I → ℝ) :=
      fun x i => x ⟨e.symm i, by simp [J]⟩
    have hg : Measurable g := by fun_prop
    have heq : I.restrict ∘ f = g ∘ J.restrict := rfl
    rw [Measure.map_map (Finset.measurable_restrict I) hm, heq,
      ← Measure.map_map hg (Finset.measurable_restrict J), hlim J]
    unfold realReindexedFamily
    rw [Measure.map_map hg (measurable_realReindexMap e.toEmbedding J)]
    have hg' : g ∘ realReindexMap e.toEmbedding J =
        fun x => fun i => x ⟨i, by rw [hJI]; exact i.property⟩ := by
      funext x i
      simp only [Function.comp_def, g, realReindexMap, Equiv.toEmbedding_apply, Equiv.apply_symm_apply]
    rw [hg']
    exact map_real_finset_transport P hJI

/-- Extending a coordinate family by zero outside its index set. -/
def realCoordinateExtension (u : Set ι) (x : u → ℝ) (i : ι) : ℝ :=
  if hi : i ∈ u then x ⟨i, hi⟩ else 0

theorem measurable_realCoordinateExtension (u : Set ι) : Measurable (realCoordinateExtension u) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ u
  · simpa only [realCoordinateExtension, dif_pos hi] using measurable_pi_apply (⟨i, hi⟩ : u)
  · simpa only [realCoordinateExtension, dif_neg hi] using (measurable_const : Measurable (fun _ : u → ℝ => (0 : ℝ)))

private theorem realCoordinateExtension_map_restrict
    (P : (I : Finset ι) → Measure (I → ℝ)) {u : Set ι}
    {ν : Measure (u → ℝ)}
    (hν : IsProjectiveLimit (α := fun _ : u => ℝ) ν
      (realReindexedFamily (Function.Embedding.subtype fun i => i ∈ u) P))
    (I : Finset ι) (hI : (I : Set ι) ⊆ u) :
    (ν.map (realCoordinateExtension u)).map I.restrict = P I := by
  classical
  let J : Finset u := I.preimage Subtype.val Subtype.val_injective.injOn
  have hJI : J.map (Function.Embedding.subtype fun i => i ∈ u) = I := by
    ext i
    simp only [Finset.mem_map, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact Finset.mem_preimage.mp hj
    · intro hi
      exact ⟨⟨i, hI hi⟩, Finset.mem_preimage.mpr hi, rfl⟩
  let g : (J → ℝ) → (I → ℝ) := fun x i => x ⟨⟨i, hI i.property⟩,
    Finset.mem_preimage.mpr i.property⟩
  have hg : Measurable g := by fun_prop
  have heq : I.restrict ∘ realCoordinateExtension u = g ∘ J.restrict := by
    funext x i
    simp only [Function.comp_def, Finset.restrict, realCoordinateExtension, dif_pos (hI i.property), g]
  rw [Measure.map_map (Finset.measurable_restrict I) (measurable_realCoordinateExtension u),
    heq, ← Measure.map_map hg (Finset.measurable_restrict J), hν J]
  unfold realReindexedFamily
  rw [Measure.map_map hg (measurable_realReindexMap _ J)]
  have hg' : g ∘ realReindexMap (Function.Embedding.subtype fun i => i ∈ u) J =
      fun x => fun i => x ⟨i, by rw [hJI]; exact i.property⟩ := rfl
  rw [hg']
  exact map_real_finset_transport P hJI

/-- The cylinder content of real projective probability laws is continuous from above. -/
theorem realProjectiveContent_tendsto_zero
    (P : (I : Finset ι) → Measure (I → ℝ)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) P)
    {A : ℕ → Set (ι → ℝ)} (hA : ∀ n, A n ∈ measurableCylinders (fun _ : ι => ℝ))
    (hanti : Antitone A) (hempty : ⋂ n, A n = ∅) :
    Tendsto (fun n => projectiveFamilyContent hP (A n)) atTop (𝓝 0) := by
  classical
  have hc n : ∃ I S, MeasurableSet S ∧ A n = cylinder I S :=
    (mem_measurableCylinders _).mp (hA n)
  choose I S hS heq using hc
  let u : Set ι := ⋃ n, (I n : Set ι)
  have hu : Countable u := Set.countable_iUnion (fun n => (I n).countable_toSet)
  obtain ⟨ν, hνprob, hν⟩ := exists_countable_real_projectiveLimit
    (realReindexedFamily (Function.Embedding.subtype fun i => i ∈ u) P)
    (realReindexedFamily_projective _ P hP)
  let := hνprob
  let μ := ν.map (realCoordinateExtension u)
  have hμ : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (measurable_realCoordinateExtension u).aemeasurable
  have hmass n : projectiveFamilyContent hP (A n) = μ (A n) := by
    rw [heq n, projectiveFamilyContent_cylinder _ (hS n), cylinder,
      ← Measure.map_apply (Finset.measurable_restrict _) (hS n)]
    rw [realCoordinateExtension_map_restrict P hν (I n)
      (fun i hi => Set.mem_iUnion.mpr ⟨n, hi⟩)]
  simp_rw [hmass]
  simpa only [hempty, measure_empty, Function.comp_def] using
    tendsto_measure_iInter_atTop
      (fun n => (MeasurableSet.of_mem_measurableCylinders (hA n)).nullMeasurableSet)
      hanti ⟨0, measure_ne_top μ _⟩

theorem realProjectiveContent_isSigmaSubadditive
    (P : (I : Finset ι) → Measure (I → ℝ)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) P) :
    (projectiveFamilyContent hP).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hUnion hdisj => ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (projectiveFamilyContent hP) (fun s hs => projectiveFamilyContent_ne_top hP)
    (fun _ => realProjectiveContent_tendsto_zero P hP) hf hUnion hdisj

/-- Carathéodory extension of a real projective probability family. -/
def realProjectiveMeasure
    (P : (I : Finset ι) → Measure (I → ℝ)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) P) : Measure (ι → ℝ) :=
  (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge (realProjectiveContent_isSigmaSubadditive P hP)

/-- The constructed measure has every specified finite-dimensional marginal. -/
theorem realProjectiveMeasure_isProjectiveLimit
    (P : (I : Finset ι) → Measure (I → ℝ)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) P) :
    IsProjectiveLimit (α := fun _ : ι => ℝ) (realProjectiveMeasure P hP) P := by
  intro I
  ext S hS
  rw [Measure.map_apply (Finset.measurable_restrict I) hS, realProjectiveMeasure,
    AddContent.measure_eq, ← cylinder, projectiveFamilyContent_cylinder hP hS]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hS

instance (P : (I : Finset ι) → Measure (I → ℝ)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) P) :
    IsProbabilityMeasure (realProjectiveMeasure P hP) :=
  (realProjectiveMeasure_isProjectiveLimit P hP).isProbabilityMeasure

end BrownianAffine
