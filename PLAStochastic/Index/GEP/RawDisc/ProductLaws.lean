import PLAStochastic.Index.GEP.RawDisc.Defs
import PLAStochastic.Index.GEP.Response.Score.ChangeOfMeasure

/-!
# WP4 `RawDisc` assembly, part 1: product laws with varying coordinate laws

Tools on the product laws `piLaw ρ = ⊗_i ρ i` (so `iidLaw ν = piLaw (fun _ => ν)` and
`wordLaw ν σ S = piLaw (fun i => if i ∈ S then σ else ν)`):

* `map_update_piLaw`: inserting an independent `α`-value at coordinate `i` of a `piLaw ρ` path
  gives `piLaw (update ρ i α)` (the general form of `map_update_iidLaw`); hence
  `lintegral_piLaw_update`, `integral_piLaw_update`, `integral_piLaw_insert` (Fubini in the
  inserted coordinate) and `lintegral_mul_coord` (a coordinate is independent of every functional
  that does not read it);
* `lintegral_exp_gapKeys`: `E e^{l S_k} = ∏_{j<k} E_{ρ j} e^{l x}`;
* `piLaw_mix_update`, `iidLaw_mix_expand`, `integral_iidLaw_mix`: the word expansion
  `((1-t) ν + t σ)^{⊗k} = ∑_{S ⊆ {0,…,k-1}} (1-t)^{k-|S|} t^{|S|} wordLaw ν σ S` on functionals of
  the first `k` coordinates (`RawDisc` design note §0);
* the survival event `survSet eps k = {k < T}` and the survival integral `survInt`, the real
  integrals that `cSurv` combines.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-! ## Product laws -/

/-- The product law with coordinate laws `ρ i`. -/
def piLaw (ρ : ℕ → ProbabilityMeasure ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun i => (ρ i : Measure ℝ))

instance (ρ : ℕ → ProbabilityMeasure ℝ) : IsProbabilityMeasure (piLaw ρ) := by
  unfold piLaw; infer_instance

theorem iidLaw_eq_piLaw (ν : ProbabilityMeasure ℝ) : iidLaw ν = piLaw (fun _ => ν) := rfl

theorem wordLaw_eq_piLaw (ν σ : ProbabilityMeasure ℝ) (S : Finset ℕ) :
    wordLaw ν σ S = piLaw (fun i => if i ∈ S then σ else ν) := rfl

theorem piLaw_congr {ρ₁ ρ₂ : ℕ → ProbabilityMeasure ℝ} (h : ∀ i, ρ₁ i = ρ₂ i) :
    piLaw ρ₁ = piLaw ρ₂ := by
  rw [funext h]

/-- **Insertion of an independent coordinate**: `update g i y` with `y ~ α` independent of
`g ~ piLaw ρ` has law `piLaw (update ρ i α)`. -/
theorem map_update_piLaw (ρ : ℕ → ProbabilityMeasure ℝ) (i : ℕ) (α : ProbabilityMeasure ℝ) :
    ((α : Measure ℝ).prod (piLaw ρ)).map
      (fun p : ℝ × (ℕ → ℝ) => Function.update p.2 i p.1) = piLaw (Function.update ρ i α) := by
  classical
  have hU := measurable_update_pair i
  unfold piLaw
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
  rw [Measure.map_apply hU hset, hpre, Measure.prod_prod,
    Measure.infinitePi_pi _ (fun j _ => hA j)]
  have hprod : ∏ j ∈ s.erase i, (ρ j : Measure ℝ) (A j) =
      ∏ j ∈ s.erase i, ((Function.update ρ i α j : ProbabilityMeasure ℝ) : Measure ℝ) (A j) :=
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  by_cases hi : i ∈ s
  · rw [if_pos hi, hprod, ← Finset.mul_prod_erase s
      (fun j => ((Function.update ρ i α j : ProbabilityMeasure ℝ) : Measure ℝ) (A j)) hi,
      Function.update_self]
  · rw [if_neg hi, measure_univ, one_mul, Finset.erase_eq_of_notMem hi]
    exact Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (by rintro rfl; exact hi hj)]

/-- Insertion in lintegral form. -/
theorem lintegral_piLaw_update (ρ : ℕ → ProbabilityMeasure ℝ) (i : ℕ) (α : ProbabilityMeasure ℝ)
    {H : (ℕ → ℝ) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ g, H g ∂(piLaw (Function.update ρ i α)) =
      ∫⁻ y, ∫⁻ g, H (Function.update g i y) ∂(piLaw ρ) ∂(α : Measure ℝ) := by
  rw [← map_update_piLaw ρ i α, lintegral_map hH (measurable_update_pair i),
    lintegral_prod (fun p : ℝ × (ℕ → ℝ) => H (Function.update p.2 i p.1))
      (hH.comp (measurable_update_pair i)).aemeasurable]

/-- Integrability transfers through the insertion map. -/
theorem integrable_prod_update {ρ : ℕ → ProbabilityMeasure ℝ} {i : ℕ} {α : ProbabilityMeasure ℝ}
    {H : (ℕ → ℝ) → ℝ} (hHm : Measurable H) (hH : Integrable H (piLaw (Function.update ρ i α))) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => H (Function.update p.2 i p.1))
      ((α : Measure ℝ).prod (piLaw ρ)) := by
  have hU := measurable_update_pair i
  rw [← map_update_piLaw ρ i α] at hH
  exact (integrable_map_measure hHm.aestronglyMeasurable hU.aemeasurable).1 hH

/-- Insertion in integral form (inserted coordinate outside). -/
theorem integral_piLaw_update (ρ : ℕ → ProbabilityMeasure ℝ) (i : ℕ) (α : ProbabilityMeasure ℝ)
    {H : (ℕ → ℝ) → ℝ} (hHm : Measurable H) (hH : Integrable H (piLaw (Function.update ρ i α))) :
    ∫ g, H g ∂(piLaw (Function.update ρ i α)) =
      ∫ y, ∫ g, H (Function.update g i y) ∂(piLaw ρ) ∂(α : Measure ℝ) := by
  have hU := measurable_update_pair i
  have h' := integrable_prod_update hHm hH
  rw [← map_update_piLaw ρ i α, integral_map hU.aemeasurable hHm.aestronglyMeasurable]
  exact integral_prod _ h'

/-- Insertion in integral form (inserted coordinate inside). -/
theorem integral_piLaw_update_swap (ρ : ℕ → ProbabilityMeasure ℝ) (i : ℕ)
    (α : ProbabilityMeasure ℝ) {H : (ℕ → ℝ) → ℝ} (hHm : Measurable H)
    (hH : Integrable H (piLaw (Function.update ρ i α))) :
    ∫ g, H g ∂(piLaw (Function.update ρ i α)) =
      ∫ g, ∫ y, H (Function.update g i y) ∂(α : Measure ℝ) ∂(piLaw ρ) := by
  have hU := measurable_update_pair i
  have h' := integrable_prod_update hHm hH
  rw [← map_update_piLaw ρ i α, integral_map hU.aemeasurable hHm.aestronglyMeasurable]
  exact integral_prod_symm _ h'

theorem piLaw_update_self (ρ : ℕ → ProbabilityMeasure ℝ) (i : ℕ) :
    piLaw (Function.update ρ i (ρ i)) = piLaw ρ := by
  rw [Function.update_eq_self]

/-- **Fubini in one coordinate** of a product law. -/
theorem integral_piLaw_insert (ρ : ℕ → ProbabilityMeasure ℝ) (i : ℕ) {H : (ℕ → ℝ) → ℝ}
    (hHm : Measurable H) (hH : Integrable H (piLaw ρ)) :
    ∫ g, H g ∂(piLaw ρ) =
      ∫ g, ∫ y, H (Function.update g i y) ∂(ρ i : Measure ℝ) ∂(piLaw ρ) := by
  have e := integral_piLaw_update_swap ρ i (ρ i) hHm (by rw [piLaw_update_self]; exact hH)
  rwa [piLaw_update_self] at e

theorem lintegral_piLaw_insert (ρ : ℕ → ProbabilityMeasure ℝ) (i : ℕ) {H : (ℕ → ℝ) → ℝ≥0∞}
    (hH : Measurable H) :
    ∫⁻ g, H g ∂(piLaw ρ) =
      ∫⁻ y, ∫⁻ g, H (Function.update g i y) ∂(piLaw ρ) ∂(ρ i : Measure ℝ) := by
  have e := lintegral_piLaw_update ρ i (ρ i) hH
  rwa [piLaw_update_self] at e

/-- **Independence of a coordinate** from every functional that does not read it. -/
theorem lintegral_mul_coord (ρ : ℕ → ProbabilityMeasure ℝ) (i : ℕ) {A : (ℕ → ℝ) → ℝ≥0∞}
    (hA : Measurable A) (hAi : ∀ g y, A (Function.update g i y) = A g) {B : ℝ → ℝ≥0∞}
    (hB : Measurable B) :
    ∫⁻ g, A g * B (g i) ∂(piLaw ρ) =
      (∫⁻ g, A g ∂(piLaw ρ)) * ∫⁻ y, B y ∂(ρ i : Measure ℝ) := by
  rw [lintegral_piLaw_insert ρ i (H := fun g => A g * B (g i))
    (hA.mul (hB.comp (measurable_pi_apply i)))]
  simp only [hAi, Function.update_self]
  rw [← lintegral_const_mul _ hB]
  refine lintegral_congr fun y => ?_
  rw [lintegral_mul_const _ hA]

/-- The coordinates of a product law are a.s. positive if every coordinate law is. -/
theorem ae_pos_piLaw {ρ : ℕ → ProbabilityMeasure ℝ} (h : ∀ j, (ρ j : Measure ℝ) (Iic 0) = 0) :
    ∀ᵐ g ∂(piLaw ρ), ∀ j, 0 < g j :=
  ae_all_iff.2 fun j => by
    have hm := (measurePreserving_eval_infinitePi (fun i : ℕ => (ρ i : Measure ℝ))
      j).measure_preimage (s := Iic 0) measurableSet_Iic.nullMeasurableSet
    rw [h j] at hm
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hm] with g hg
    simpa using hg

theorem lintegral_piLaw_prefix {ρ₁ ρ₂ : ℕ → ProbabilityMeasure ℝ} {t : ℕ}
    (h : ∀ i < t, ρ₁ i = ρ₂ i) {G : (ℕ → ℝ) → ℝ≥0∞} (hG : Measurable G) (hdep : DepPrefix t G) :
    ∫⁻ g, G g ∂(piLaw ρ₁) = ∫⁻ g, G g ∂(piLaw ρ₂) :=
  lintegral_infinitePi_prefix (fun i hi => by rw [h i hi]) hG hdep

theorem integral_piLaw_prefix {ρ₁ ρ₂ : ℕ → ProbabilityMeasure ℝ} {t : ℕ}
    (h : ∀ i < t, ρ₁ i = ρ₂ i) {G : (ℕ → ℝ) → ℝ} (hG : Measurable G) (hdep : DepPrefix t G) :
    ∫ g, G g ∂(piLaw ρ₁) = ∫ g, G g ∂(piLaw ρ₂) :=
  integral_infinitePi_prefix (fun i hi => by rw [h i hi]) hG hdep

theorem integrable_piLaw_prefix {ρ₁ ρ₂ : ℕ → ProbabilityMeasure ℝ} {t : ℕ}
    (h : ∀ i < t, ρ₁ i = ρ₂ i) {G : (ℕ → ℝ) → ℝ} (hG : Measurable G) (hdep : DepPrefix t G)
    (hint : Integrable G (piLaw ρ₁)) : Integrable G (piLaw ρ₂) := by
  refine ⟨hG.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hdep' : DepPrefix t (fun g => ‖G g‖ₑ) := fun g g' hgg => by
    show ‖G g‖ₑ = ‖G g'‖ₑ
    rw [hdep g g' hgg]
  rw [← lintegral_piLaw_prefix h hG.enorm hdep']
  exact hint.2

/-! ## Exponential moments of the keys -/

theorem gapKeys_update_self (g : ℕ → ℝ) (k : ℕ) (y : ℝ) :
    gapKeys (Function.update g k y) k = gapKeys g k :=
  Finset.sum_congr rfl fun _ hj =>
    Function.update_of_ne (Finset.mem_range.1 hj).ne _ _

theorem gapKeys_update_succ (g : ℕ → ℝ) (k : ℕ) (y : ℝ) :
    gapKeys (Function.update g k y) (k + 1) = gapKeys g k + y := by
  rw [gapKeys, Finset.sum_range_succ, Function.update_self]
  exact congrArg (· + y) (gapKeys_update_self g k y)

theorem gapKeys_succ (g : ℕ → ℝ) (k : ℕ) : gapKeys g (k + 1) = gapKeys g k + g k :=
  Finset.sum_range_succ _ _

theorem rawAsm_measurable_gapKeys (k : ℕ) : Measurable fun g : ℕ → ℝ => gapKeys g k :=
  (measurable_pi_apply k).comp measurable_gapKeys

/-- **Exponential moment of the keys** under a product law. -/
theorem lintegral_exp_gapKeys (ρ : ℕ → ProbabilityMeasure ℝ) (l : ℝ) (k : ℕ) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (l * gapKeys g k)) ∂(piLaw ρ) =
      ∏ j ∈ Finset.range k, ∫⁻ y, ENNReal.ofReal (Real.exp (l * y)) ∂(ρ j : Measure ℝ) := by
  induction k with
  | zero => simp [gapKeys_zero]
  | succ k ih =>
    have hA : Measurable fun g : ℕ → ℝ => ENNReal.ofReal (Real.exp (l * gapKeys g k)) :=
      ((rawAsm_measurable_gapKeys k).const_mul l).exp.ennreal_ofReal
    have hB : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (l * y)) :=
      ((measurable_id.const_mul l).exp).ennreal_ofReal
    have e : ∀ g : ℕ → ℝ, ENNReal.ofReal (Real.exp (l * gapKeys g (k + 1))) =
        ENNReal.ofReal (Real.exp (l * gapKeys g k)) * ENNReal.ofReal (Real.exp (l * g k)) := by
      intro g
      rw [gapKeys_succ, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp_rw [e]
    rw [lintegral_mul_coord ρ k hA (fun g y => by rw [gapKeys_update_self]) hB, ih,
      Finset.prod_range_succ]

theorem lintegral_exp_gapKeys_le {ρ : ℕ → ProbabilityMeasure ℝ} {l : ℝ} {M : ℝ≥0∞}
    (h : ∀ j, ∫⁻ y, ENNReal.ofReal (Real.exp (l * y)) ∂(ρ j : Measure ℝ) ≤ M) (k : ℕ) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (l * gapKeys g k)) ∂(piLaw ρ) ≤ M ^ k := by
  rw [lintegral_exp_gapKeys]
  calc ∏ j ∈ Finset.range k, ∫⁻ y, ENNReal.ofReal (Real.exp (l * y)) ∂(ρ j : Measure ℝ)
      ≤ ∏ _j ∈ Finset.range k, M := Finset.prod_le_prod' fun j _ => h j
    _ = M ^ k := by rw [Finset.prod_const, Finset.card_range]

theorem rawAsm_integrable_exp_gapKeys {ρ : ℕ → ProbabilityMeasure ℝ} {l : ℝ}
    (h : ∀ j, ∫⁻ y, ENNReal.ofReal (Real.exp (l * y)) ∂(ρ j : Measure ℝ) ≤ 2) (k : ℕ) :
    Integrable (fun g => Real.exp (l * gapKeys g k)) (piLaw ρ) := by
  refine ⟨((rawAsm_measurable_gapKeys k).const_mul l).exp.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  exact lt_of_le_of_lt (lintegral_exp_gapKeys_le h k)
    (ENNReal.pow_lt_top (by norm_num))

/-! ## The survival event and the survival integrals -/

/-- The survival event `{k < T}`. -/
def survSet (eps : ℝ) (k : ℕ) : Set (ℕ → ℝ) := {g | (k : ℕ∞) < gapSegLen eps g}

theorem measurableSet_survSet (eps : ℝ) (k : ℕ) : MeasurableSet (survSet eps k) :=
  measurableSet_lt_gapSegLen eps k

theorem mem_survSet_update {eps : ℝ} {k i : ℕ} (hik : k ≤ i) (g : ℕ → ℝ) (y : ℝ) :
    Function.update g i y ∈ survSet eps k ↔ g ∈ survSet eps k :=
  lt_gapSegLen_congr fun j hj => Function.update_of_ne (by omega) _ _

/-- The survival integral `∫ G(S_k) 1{k < T} dμ`. -/
def survInt (eps : ℝ) (μ : Measure (ℕ → ℝ)) (k : ℕ) (G : ℝ → ℝ) : ℝ :=
  ∫ g, (survSet eps k).indicator (fun g => G (gapKeys g k)) g ∂μ

theorem cSurv_eq (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (k : ℕ) (G : ℝ → ℝ) :
    cSurv eps ν σ z k G = ∑ S ∈ (Finset.range k).powerset,
      (1 - z) ^ (k - S.card) * z ^ S.card * ((survInt eps (wordLaw ν σ S) k G : ℝ) : ℂ) := rfl

theorem measurable_survInd (eps : ℝ) (k : ℕ) {G : ℝ → ℝ} (hG : Measurable G) :
    Measurable ((survSet eps k).indicator (fun g => G (gapKeys g k))) :=
  (hG.comp (rawAsm_measurable_gapKeys k)).indicator (measurableSet_survSet eps k)

theorem depPrefix_survInd (eps : ℝ) (k : ℕ) (G : ℝ → ℝ) :
    DepPrefix k ((survSet eps k).indicator (fun g => G (gapKeys g k))) := by
  intro g g' h
  have hS : g ∈ survSet eps k ↔ g' ∈ survSet eps k := lt_gapSegLen_congr h
  have hK : gapKeys g k = gapKeys g' k := gapKeys_congr h k le_rfl
  by_cases hg : g ∈ survSet eps k
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hS.1 hg), hK]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h' => hg (hS.2 h'))]

/-- `survInt` is linear in the test. -/
theorem survInt_const_mul (eps : ℝ) (μ : Measure (ℕ → ℝ)) (k : ℕ) (c : ℝ) (G : ℝ → ℝ) :
    survInt eps μ k (fun s => c * G s) = c * survInt eps μ k G := by
  unfold survInt
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  by_cases hg : g ∈ survSet eps k
  · simp only [Set.indicator_of_mem hg]
  · simp only [Set.indicator_of_notMem hg, mul_zero]

theorem cSurv_const_mul (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (k : ℕ) (c : ℝ)
    (G : ℝ → ℝ) : cSurv eps ν σ z k (fun s => c * G s) = c * cSurv eps ν σ z k G := by
  rw [cSurv_eq, cSurv_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [survInt_const_mul]
  push_cast
  ring

/-- Integrability of a survival integrand with an exponentially bounded test. -/
theorem integrable_survInd {ρ : ℕ → ProbabilityMeasure ℝ} {l C : ℝ} (eps : ℝ) (k : ℕ)
    (hρ : ∀ j, (ρ j : Measure ℝ) (Iic 0) = 0)
    (hm : ∀ j, ∫⁻ y, ENNReal.ofReal (Real.exp (l * y)) ∂(ρ j : Measure ℝ) ≤ 2)
    {G : ℝ → ℝ} (hG : Measurable G) (hGb : ∀ y, 0 ≤ y → |G y| ≤ C * Real.exp (l * y)) :
    Integrable ((survSet eps k).indicator (fun g => G (gapKeys g k))) (piLaw ρ) := by
  refine ((rawAsm_integrable_exp_gapKeys hm k).const_mul C).mono'
    (measurable_survInd eps k hG).aestronglyMeasurable ?_
  filter_upwards [ae_pos_piLaw hρ] with g hg
  have hk : 0 ≤ gapKeys g k := Finset.sum_nonneg fun j _ => (hg j).le
  by_cases hs : g ∈ survSet eps k
  · rw [Set.indicator_of_mem hs, Real.norm_eq_abs]
    exact hGb _ hk
  · rw [Set.indicator_of_notMem hs, norm_zero]
    have := hGb _ hk
    exact (abs_nonneg _).trans this

/-! ## The word expansion of the mixture product -/

/-- The mixture product splits linearly in one coordinate. -/
theorem piLaw_mix_update (R : ℕ → ProbabilityMeasure ℝ) (k : ℕ) (ν σ : ProbabilityMeasure ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    piLaw (Function.update R k (mixPM ν σ t)) =
      ENNReal.ofReal (1 - t) • piLaw (Function.update R k ν) +
        ENNReal.ofReal t • piLaw (Function.update R k σ) := by
  have hU := measurable_update_pair k
  rw [← map_update_piLaw R k, ← map_update_piLaw R k, ← map_update_piLaw R k, coe_mixPM,
    mixParam_of_mem ht, Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.map_add _ _ hU, Measure.map_smul, Measure.map_smul]

/-- The coordinate laws of the word `S` on the first `k` coordinates, the mixture afterwards. -/
def wordMixFam (ν σ : ProbabilityMeasure ℝ) (t : ℝ) (k : ℕ) (S : Finset ℕ) :
    ℕ → ProbabilityMeasure ℝ :=
  fun j => if j ∈ S then σ else if j < k then ν else mixPM ν σ t

/-- The weight `(1-t)^{k-|S|} t^{|S|}` of the word `S`. -/
def wordCoef (t : ℝ) (k : ℕ) (S : Finset ℕ) : ℝ := (1 - t) ^ (k - S.card) * t ^ S.card

theorem wordCoef_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (k : ℕ) (S : Finset ℕ) :
    0 ≤ wordCoef t k S :=
  mul_nonneg (pow_nonneg (by linarith [ht.2]) _) (pow_nonneg ht.1 _)

/-- **Word expansion** of the mixture product on the first `k` coordinates. -/
theorem iidLaw_mix_expand (ν σ : ProbabilityMeasure ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (k : ℕ) :
    iidLaw (mixPM ν σ t) = ∑ S ∈ (Finset.range k).powerset,
      ENNReal.ofReal (wordCoef t k S) • piLaw (wordMixFam ν σ t k S) := by
  classical
  induction k with
  | zero =>
    rw [Finset.range_zero, Finset.powerset_empty, Finset.sum_singleton]
    simp only [wordCoef, Finset.card_empty, Nat.sub_zero, pow_zero, mul_one, ENNReal.ofReal_one,
      one_smul]
    exact piLaw_congr fun j => by simp [wordMixFam]
  | succ k ih =>
    rw [ih, Finset.range_add_one, Finset.sum_powerset_insert Finset.notMem_range_self,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hSk : S ⊆ Finset.range k := Finset.mem_powerset.1 hS
    have hkS : k ∉ S := fun h => Finset.notMem_range_self (hSk h)
    set R := wordMixFam ν σ t (k + 1) S with hR
    have e0 : wordMixFam ν σ t k S = Function.update R k (mixPM ν σ t) := by
      funext j
      by_cases hj : j = k
      · subst hj; simp [wordMixFam, hkS]
      · rw [Function.update_of_ne hj, hR]
        simp only [wordMixFam]
        have : j < k + 1 ↔ j < k := by omega
        simp only [this]
    have e1 : R = Function.update R k ν := by
      funext j
      by_cases hj : j = k
      · subst hj; simp [hR, wordMixFam, hkS]
      · rw [Function.update_of_ne hj]
    have e2 : wordMixFam ν σ t (k + 1) (insert k S) = Function.update R k σ := by
      funext j
      by_cases hj : j = k
      · subst hj; simp [wordMixFam]
      · rw [Function.update_of_ne hj, hR]
        simp [wordMixFam, Finset.mem_insert, hj]
    rw [e0, piLaw_mix_update R k ν σ ht, ← e1, e2, smul_add, smul_smul, smul_smul,
      ← ENNReal.ofReal_mul (wordCoef_nonneg ht k S), ← ENNReal.ofReal_mul (wordCoef_nonneg ht k S)]
    have hc : S.card ≤ k := by
      simpa using Finset.card_le_card hSk
    have c1 : wordCoef t k S * (1 - t) = wordCoef t (k + 1) S := by
      simp only [wordCoef]
      rw [show k + 1 - S.card = (k - S.card) + 1 by omega, pow_succ]
      ring
    have c2 : wordCoef t k S * t = wordCoef t (k + 1) (insert k S) := by
      simp only [wordCoef]
      rw [Finset.card_insert_of_notMem hkS, show k + 1 - (S.card + 1) = k - S.card by omega,
        pow_succ]
      ring
    rw [c1, c2]

/-- **Word expansion of prefix expectations** under the mixture. -/
theorem integral_iidLaw_mix (ν σ : ProbabilityMeasure ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {k : ℕ} {H : (ℕ → ℝ) → ℝ} (hHm : Measurable H) (hdep : DepPrefix k H)
    (hint : ∀ S ∈ (Finset.range k).powerset, Integrable H (wordLaw ν σ S)) :
    ∫ g, H g ∂(iidLaw (mixPM ν σ t)) =
      ∑ S ∈ (Finset.range k).powerset, wordCoef t k S * ∫ g, H g ∂(wordLaw ν σ S) := by
  have hagree : ∀ S : Finset ℕ, ∀ j < k,
      (fun i => if i ∈ S then σ else ν) j = wordMixFam ν σ t k S j := fun S j hj => by
    simp [wordMixFam, hj]
  have hint' : ∀ S ∈ (Finset.range k).powerset, Integrable H (piLaw (wordMixFam ν σ t k S)) :=
    fun S hS => integrable_piLaw_prefix (hagree S) hHm hdep (hint S hS)
  rw [iidLaw_mix_expand ν σ ht k, integral_finsetSum_measure fun S hS =>
    (hint' S hS).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (wordCoef_nonneg ht k S), smul_eq_mul,
    wordLaw_eq_piLaw, integral_piLaw_prefix (hagree S) hHm hdep]

end

end PGM
