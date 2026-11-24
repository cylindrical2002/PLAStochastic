import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Strip
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Laws and densities of ladder heights

For a measurable entrance set `B` (the ascending ladder is `B = Ioi 0`):

* `preEntryOccupation ρ B` is the occupation measure `u(E) = ∑ₙ P(n < τ_B, S_n ∈ E)`;
  `entryLaw ρ B` is the (defective) law of `S_{τ_B}` on `{τ_B < ∞}`.
* `lintegral_entryLaw`: the ladder height formula
  `∫ g d(entryLaw) = ∫ u(dx) ∫ (1_B g)(x + y) ρ(dy)`, i.e.
  `P(τ_B < ∞, S_{τ_B} ∈ E) = ∫ u(dx) ρ((E ∩ B) - x)` (`entryLaw_apply`).
* If `ρ = f(y) dy`, then `{τ_B = n + 1}` contributes the density `1_B(h) k_n(h)` with
  `k_n(h) = E[f(h - S_n); n < τ_B]` (`map_firstEntry_succ_eq_withDensity`), and the discounted
  ladder height measure `E[s^{τ_B}; S_{τ_B} ∈ dh, τ_B < ∞]` has the density
  `ladderDensity ρ f B s h = 1_B(h) ∑ₙ s^{n+1} k_n(h)` (`setIntegral_entry_eq_integral_ladderDensity`).
* Envelopes: for a half-line type set `A`, `B = Aᶜ`, if `f(h - x) ≤ c e^{θ x}` for `x ∈ A ∪ {0}`,
  then `‖ladderDensity ρ f Aᶜ s h‖ ≤ ‖s‖ c (1 - E[e^{θ S_{τ_A}}; τ_A < ∞])⁻¹`
  (`norm_ladderDensity_le`); in particular the strict ascending ladder density is at most
  `‖s‖ D (1 - E[e^{θ H₋}; τ₋ < ∞])⁻¹ e^{-θ h}` when `f(y) ≤ D e^{-θ y}` on `y > 0`
  (`norm_ladderDensity_asc_le`), and dually for the weak descending ladder.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Finset
open scoped ENNReal

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {B : Set ℝ}

theorem firstEntry_eq_succ_iff {ω : ℕ → ℝ} {n : ℕ} :
    firstEntry B ω = ((n + 1 : ℕ) : ℕ∞) ↔
      (n : ℕ∞) < firstEntry B ω ∧ partialSum (n + 1) ω ∈ B := by
  rw [firstEntry_eq_coe_iff, coe_lt_firstEntry_iff]
  constructor
  · rintro ⟨-, hB, hbefore⟩
    exact ⟨fun j hj hjn => hbefore j hj (by omega), hB⟩
  · rintro ⟨hbefore, hB⟩
    exact ⟨Nat.succ_pos n, hB, fun j hj hjn => hbefore j hj (by omega)⟩

/-- Before the entrance time the walk is in `Bᶜ`, or at the origin. -/
theorem partialSum_mem_of_lt_firstEntry {ω : ℕ → ℝ} {n : ℕ}
    (h : (n : ℕ∞) < firstEntry B ω) : partialSum n ω ∈ Bᶜ ∨ partialSum n ω = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inr (partialSum_zero ω)
  · exact Or.inl (coe_lt_firstEntry_iff.mp h n hn le_rfl)

/-! ### The occupation measure and the ladder height formula -/

/-- The pre-entrance occupation measure `u(E) = ∑ₙ P(n < τ_B, S_n ∈ E)`. -/
def preEntryOccupation (ρ : Measure ℝ) (B : Set ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ =>
    ((pathLaw ρ).restrict {ω | (n : ℕ∞) < firstEntry B ω}).map (partialSum n)

/-- The defective law of the entrance position `S_{τ_B}` on `{τ_B < ∞}`. -/
def entryLaw (ρ : Measure ℝ) (B : Set ℝ) : Measure ℝ :=
  ((pathLaw ρ).restrict {ω | firstEntry B ω < ⊤}).map (entryValue B)

omit [IsProbabilityMeasure ρ] in
theorem lintegral_preEntryOccupation {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂preEntryOccupation ρ B = ∑' n : ℕ,
      ∫⁻ ω in {ω | (n : ℕ∞) < firstEntry B ω}, g (partialSum n ω) ∂pathLaw ρ := by
  rw [preEntryOccupation, lintegral_sum_measure]
  exact tsum_congr fun n => lintegral_map hg (measurable_partialSum n)

/-- The last step into `B`: `E[g(S_{n+1}); τ_B = n + 1] = E[∫ (1_B g)(S_n + y) dρ(y); n < τ_B]`. -/
theorem lintegral_firstEntry_succ (hBm : MeasurableSet B) (n : ℕ) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ ω in {ω | firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)}, g (partialSum (n + 1) ω) ∂pathLaw ρ =
      ∫⁻ ω in {ω | (n : ℕ∞) < firstEntry B ω},
        ∫⁻ y, B.indicator g (partialSum n ω + y) ∂ρ ∂pathLaw ρ := by
  set S : Set (ℕ → ℝ) := {ω | (n : ℕ∞) < firstEntry B ω}
  have hS : MeasurableSet S := measurableSet_coe_lt_firstEntry hBm n
  set X : (ℕ → ℝ) → ℝ≥0∞ × ℝ := fun ω => (S.indicator 1 ω, partialSum n ω)
  set Ψ : (ℝ≥0∞ × ℝ) × ℝ → ℝ≥0∞ := fun p => p.1.1 * B.indicator g (p.1.2 + p.2)
  have hX : Measurable X :=
    (measurable_const.indicator hS).prodMk (measurable_partialSum n)
  have hXd : DependsOnPrefix n X := by
    intro ω ω' h
    have hiff : ω ∈ S ↔ ω' ∈ S := coe_lt_firstEntry_congr (A := B) h
    simp only [X, Prod.mk.injEq]
    refine ⟨?_, partialSum_congr h⟩
    by_cases hω : ω ∈ S
    · rw [indicator_of_mem hω, indicator_of_mem (hiff.mp hω)]; rfl
    · rw [indicator_of_notMem hω, indicator_of_notMem (fun h' => hω (hiff.mpr h'))]
  have hΨ : Measurable Ψ :=
    (measurable_fst.comp measurable_fst).mul ((hg.indicator hBm).comp
      ((measurable_snd.comp measurable_fst).add measurable_snd))
  have hpt : ∀ ω, {ω | firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)}.indicator
      (fun ω => g (partialSum (n + 1) ω)) ω = Ψ (X ω, ω n) := by
    intro ω
    simp only [Ψ, X]
    rw [← partialSum_succ]
    by_cases hτ : firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)
    · obtain ⟨hlt, hmem⟩ := firstEntry_eq_succ_iff.mp hτ
      rw [indicator_of_mem (show ω ∈ {ω | firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)} from hτ),
        indicator_of_mem (show ω ∈ S from hlt), indicator_of_mem hmem, Pi.one_apply, one_mul]
    · rw [indicator_of_notMem (show ω ∉ {ω | firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)} from hτ)]
      by_cases hlt : ω ∈ S
      · have hnot : partialSum (n + 1) ω ∉ B := fun hmem =>
          hτ (firstEntry_eq_succ_iff.mpr ⟨hlt, hmem⟩)
        rw [indicator_of_notMem hnot, mul_zero]
      · rw [indicator_of_notMem hlt, zero_mul]
  rw [← lintegral_indicator (measurableSet_firstEntry_eq hBm (n + 1)), lintegral_congr hpt,
    lintegral_comp_prefix_eval hX hXd hΨ, ← lintegral_indicator hS]
  refine lintegral_congr fun ω => ?_
  simp only [Ψ, X]
  by_cases hω : ω ∈ S
  · rw [indicator_of_mem hω, indicator_of_mem hω]
    simp
  · rw [indicator_of_notMem hω, indicator_of_notMem hω]
    simp

theorem setOf_firstEntry_zero_eq_empty (B : Set ℝ) :
    {ω : ℕ → ℝ | firstEntry B ω = ((0 : ℕ) : ℕ∞)} = ∅ := by
  ext ω
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro h0
  exact (lt_irrefl 0) (firstEntry_eq_coe_iff.mp h0).1

/-- **Ladder height formula**: `∫ g d(entryLaw) = ∫ u(dx) ∫ (1_B g)(x + y) dρ(y)`. -/
theorem lintegral_entryLaw (hBm : MeasurableSet B) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂entryLaw ρ B =
      ∫⁻ x, ∫⁻ y, B.indicator g (x + y) ∂ρ ∂preEntryOccupation ρ B := by
  have hG : Measurable fun x => ∫⁻ y, B.indicator g (x + y) ∂ρ :=
    ((hg.indicator hBm).comp (measurable_fst.add measurable_snd)).lintegral_prod_right'
  rw [entryLaw, lintegral_map hg (measurable_entryValue hBm), lintegral_preEntryOccupation hG,
    setOf_firstEntry_lt_top_eq_iUnion, lintegral_iUnion (fun n => measurableSet_firstEntry_eq hBm n)
      (pairwise_disjoint_firstEntry_eq B), tsum_eq_zero_add' ENNReal.summable,
    setOf_firstEntry_zero_eq_empty, Measure.restrict_empty, lintegral_zero_measure, zero_add]
  refine tsum_congr fun n => ?_
  rw [← lintegral_firstEntry_succ hBm n hg]
  refine setLIntegral_congr_fun (measurableSet_firstEntry_eq hBm (n + 1)) fun ω hω => ?_
  simp only [mem_ofPred_eq] at hω
  simp only [entryValue_of_eq hω]

/-- `P(τ_B < ∞, S_{τ_B} ∈ E) = ∫ u(dx) ρ((E ∩ B) - x)`. -/
theorem entryLaw_apply (hBm : MeasurableSet B) {E : Set ℝ} (hE : MeasurableSet E) :
    entryLaw ρ B E = ∫⁻ x, ρ ((fun y => x + y) ⁻¹' (E ∩ B)) ∂preEntryOccupation ρ B := by
  rw [← lintegral_indicator_one hE, lintegral_entryLaw hBm (measurable_one.indicator hE)]
  refine lintegral_congr fun x => ?_
  rw [← lintegral_indicator_one ((hE.inter hBm).preimage (measurable_const_add x))]
  refine lintegral_congr fun y => ?_
  by_cases h1 : x + y ∈ B <;> by_cases h2 : x + y ∈ E <;> simp [h1, h2]

/-! ### Densities -/

/-- `K_n(h) = E[f(h - S_n); n < τ_B]` in `ℝ≥0∞`. -/
def ladderKernelENN (ρ : Measure ℝ) (f : ℝ → ℝ) (B : Set ℝ) (n : ℕ) (h : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω in {ω | (n : ℕ∞) < firstEntry B ω}, ENNReal.ofReal (f (h - partialSum n ω)) ∂pathLaw ρ

/-- `k_n(h) = E[f(h - S_n); n < τ_B]`. -/
def ladderKernel (ρ : Measure ℝ) (f : ℝ → ℝ) (B : Set ℝ) (n : ℕ) (h : ℝ) : ℝ :=
  ∫ ω in {ω | (n : ℕ∞) < firstEntry B ω}, f (h - partialSum n ω) ∂pathLaw ρ

/-- The discounted ladder height density `g_s(h) = 1_B(h) ∑ₙ s^{n+1} k_n(h)`. -/
def ladderDensity (ρ : Measure ℝ) (f : ℝ → ℝ) (B : Set ℝ) (s : ℂ) (h : ℝ) : ℂ :=
  B.indicator (fun h => ∑' n : ℕ, s ^ (n + 1) * (ladderKernel ρ f B n h : ℂ)) h

variable {f : ℝ → ℝ}

theorem measurable_ladderKernelENN (hfm : Measurable f) (n : ℕ) :
    Measurable (ladderKernelENN ρ f B n) := by
  have : Measurable fun p : ℝ × (ℕ → ℝ) => ENNReal.ofReal (f (p.1 - partialSum n p.2)) :=
    ENNReal.measurable_ofReal.comp (hfm.comp (measurable_fst.sub
      ((measurable_partialSum n).comp measurable_snd)))
  exact this.lintegral_prod_right'

omit [IsProbabilityMeasure ρ] in
theorem ladderKernel_eq_toReal (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f) (n : ℕ) (h : ℝ) :
    ladderKernel ρ f B n h = (ladderKernelENN ρ f B n h).toReal :=
  integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => hf0 _)
    (hfm.comp (measurable_const.sub (measurable_partialSum n))).aestronglyMeasurable

omit [IsProbabilityMeasure ρ] in
theorem ladderKernel_nonneg (hf0 : ∀ y, 0 ≤ f y) (n : ℕ) (h : ℝ) :
    0 ≤ ladderKernel ρ f B n h :=
  integral_nonneg fun _ => hf0 _

/-- With a density `f` for `ρ`, the step `{τ_B = n + 1}` contributes the density `1_B K_n`. -/
theorem map_firstEntry_succ_eq_withDensity (hBm : MeasurableSet B) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity fun y => ENNReal.ofReal (f y)) (n : ℕ) :
    ((pathLaw ρ).restrict {ω | firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)}).map (partialSum (n + 1)) =
      volume.withDensity (B.indicator (ladderKernelENN ρ f B n)) := by
  have hKm := measurable_ladderKernelENN (ρ := ρ) (B := B) hfm n
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hfE : Measurable fun y => ENNReal.ofReal (f y) := ENNReal.measurable_ofReal.comp hfm
  rw [lintegral_map hg (measurable_partialSum (n + 1)), lintegral_firstEntry_succ hBm n hg,
    lintegral_withDensity_eq_lintegral_mul _ (hKm.indicator hBm) hg]
  have hinner : ∀ x : ℝ, ∫⁻ y, B.indicator g (x + y) ∂ρ =
      ∫⁻ h, ENNReal.ofReal (f (h - x)) * B.indicator g h := by
    intro x
    have hgx : Measurable fun y => B.indicator g (x + y) :=
      (hg.indicator hBm).comp (measurable_const_add x)
    conv_lhs => rw [hρ]
    rw [lintegral_withDensity_eq_lintegral_mul _ hfE hgx]
    simp only [Pi.mul_apply]
    rw [← lintegral_sub_right_eq_self (fun y => ENNReal.ofReal (f y) * B.indicator g (x + y)) x]
    refine lintegral_congr fun h => ?_
    simp only [add_sub_cancel]
  simp_rw [hinner]
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun h => ?_
    have hmω : Measurable fun ω : ℕ → ℝ => ENNReal.ofReal (f (h - partialSum n ω)) :=
      ENNReal.measurable_ofReal.comp (hfm.comp (measurable_const.sub (measurable_partialSum n)))
    rw [lintegral_mul_const _ hmω, Pi.mul_apply]
    by_cases hh : h ∈ B
    · rw [indicator_of_mem hh, indicator_of_mem hh]; rfl
    · rw [indicator_of_notMem hh, indicator_of_notMem hh]; simp
  · exact ((ENNReal.measurable_ofReal.comp (hfm.comp (measurable_snd.sub
      ((measurable_partialSum n).comp measurable_fst)))).mul
      ((hg.indicator hBm).comp measurable_snd)).aemeasurable

/-- `∫ 1_B K_n = P(τ_B = n + 1)`. -/
theorem lintegral_indicator_ladderKernelENN (hBm : MeasurableSet B) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity fun y => ENNReal.ofReal (f y)) (n : ℕ) :
    ∫⁻ h, B.indicator (ladderKernelENN ρ f B n) h =
      pathLaw ρ {ω | firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)} := by
  have h := congrArg (fun μ : Measure ℝ => μ univ)
    (map_firstEntry_succ_eq_withDensity (ρ := ρ) hBm hfm hρ n)
  rw [Measure.map_apply (measurable_partialSum _) MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h
  exact h.symm

omit [IsProbabilityMeasure ρ] in
theorem indicator_ladderKernel_eq_toReal (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f) (n : ℕ)
    (h : ℝ) : B.indicator (ladderKernel ρ f B n) h =
      (B.indicator (ladderKernelENN ρ f B n) h).toReal := by
  by_cases hh : h ∈ B
  · rw [indicator_of_mem hh, indicator_of_mem hh, ladderKernel_eq_toReal hf0 hfm]
  · rw [indicator_of_notMem hh, indicator_of_notMem hh, ENNReal.toReal_zero]

theorem integrable_indicator_ladderKernel (hBm : MeasurableSet B) (hf0 : ∀ y, 0 ≤ f y)
    (hfm : Measurable f) (hρ : ρ = volume.withDensity fun y => ENNReal.ofReal (f y)) (n : ℕ) :
    Integrable (B.indicator (ladderKernel ρ f B n)) ∧
      ∫ h, B.indicator (ladderKernel ρ f B n) h =
        (pathLaw ρ).real {ω | firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)} := by
  have hKm := (measurable_ladderKernelENN (ρ := ρ) (B := B) hfm n).indicator hBm
  have hfin : ∫⁻ h, B.indicator (ladderKernelENN ρ f B n) h ≠ ∞ := by
    rw [lintegral_indicator_ladderKernelENN hBm hfm hρ n]; exact measure_ne_top _ _
  have heq : B.indicator (ladderKernel ρ f B n) =
      fun h => (B.indicator (ladderKernelENN ρ f B n) h).toReal :=
    funext (indicator_ladderKernel_eq_toReal hf0 hfm n)
  rw [heq]
  refine ⟨integrable_toReal_of_lintegral_ne_top hKm.aemeasurable hfin, ?_⟩
  rw [integral_toReal hKm.aemeasurable (ae_lt_top hKm hfin),
    lintegral_indicator_ladderKernelENN hBm hfm hρ n]
  rfl

/-- `E[φ(S_{n+1}); τ_B = n + 1] = ∫ 1_B(h) k_n(h) φ(h) dh`. -/
theorem setIntegral_firstEntry_succ_eq (hBm : MeasurableSet B) (hf0 : ∀ y, 0 ≤ f y)
    (hfm : Measurable f) (hρ : ρ = volume.withDensity fun y => ENNReal.ofReal (f y)) (n : ℕ)
    {φ : ℝ → ℂ} (hφ : Measurable φ) :
    ∫ ω in {ω | firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)}, φ (partialSum (n + 1) ω) ∂pathLaw ρ =
      ∫ h, ((B.indicator (ladderKernel ρ f B n) h : ℝ) : ℂ) * φ h := by
  have hKm := (measurable_ladderKernelENN (ρ := ρ) (B := B) hfm n).indicator hBm
  have hfin : ∫⁻ h, B.indicator (ladderKernelENN ρ f B n) h ≠ ∞ := by
    rw [lintegral_indicator_ladderKernelENN hBm hfm hρ n]; exact measure_ne_top _ _
  rw [← integral_map (measurable_partialSum (n + 1)).aemeasurable hφ.aestronglyMeasurable,
    map_firstEntry_succ_eq_withDensity hBm hfm hρ n,
    integral_withDensity_eq_integral_toReal_smul hKm (ae_lt_top hKm hfin)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [Complex.real_smul]
  rw [indicator_ladderKernel_eq_toReal hf0 hfm n h]

theorem measurable_ladderKernel (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f) (n : ℕ) :
    Measurable (ladderKernel ρ f B n) := by
  have : ladderKernel ρ f B n = fun h => (ladderKernelENN ρ f B n h).toReal :=
    funext fun h => ladderKernel_eq_toReal hf0 hfm n h
  rw [this]
  exact (measurable_ladderKernelENN hfm n).ennreal_toReal

/-- A bounded functional of `(τ_B, S_{τ_B})` as a series over the entrance time. -/
theorem setIntegral_entry_eq_tsum (hBm : MeasurableSet B) {s : ℂ} (hs : ‖s‖ ≤ 1)
    {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) :
    ∫ ω in {ω | firstEntry B ω < ⊤}, s ^ (firstEntry B ω).toNat * φ (entryValue B ω)
        ∂pathLaw ρ =
      ∑' n : ℕ, s ^ n * ∫ ω in {ω | firstEntry B ω = n}, φ (partialSum n ω) ∂pathLaw ρ := by
  have hGm : Measurable fun ω => s ^ (firstEntry B ω).toNat * φ (entryValue B ω) :=
    ((Measurable.of_discrete (f := fun k : ℕ => s ^ k)).comp
      ((Measurable.of_discrete (f := ENat.toNat)).comp (measurable_firstEntry hBm))).mul
      (hφ.comp (measurable_entryValue hBm))
  have hGb : ∀ ω, ‖s ^ (firstEntry B ω).toNat * φ (entryValue B ω)‖ ≤ C := fun ω => by
    rw [norm_mul, norm_pow]
    calc ‖s‖ ^ (firstEntry B ω).toNat * ‖φ (entryValue B ω)‖ ≤ 1 * ‖φ (entryValue B ω)‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hs) (norm_nonneg _)
      _ ≤ C := by rw [one_mul]; exact hC _
  have hU : IntegrableOn (fun ω => s ^ (firstEntry B ω).toNat * φ (entryValue B ω))
      (⋃ n : ℕ, {ω | firstEntry B ω = n}) (pathLaw ρ) :=
    Measure.integrableOn_of_bounded (M := C) (measure_ne_top _ _) hGm.aestronglyMeasurable
      (Filter.Eventually.of_forall hGb)
  rw [setOf_firstEntry_lt_top_eq_iUnion, integral_iUnion
    (fun n => measurableSet_firstEntry_eq hBm n) (pairwise_disjoint_firstEntry_eq B) hU]
  refine tsum_congr fun n => ?_
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_firstEntry_eq hBm n) fun ω hω => ?_
  simp only [mem_ofPred_eq] at hω
  simp only [hω, ENat.toNat_natCast, entryValue_of_eq hω]

omit [IsProbabilityMeasure ρ] in
theorem norm_mul_indicator_ladderKernel_le (hf0 : ∀ y, 0 ≤ f y) {s : ℂ} (hs : ‖s‖ ≤ 1)
    {φ : ℝ → ℂ} {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) (n : ℕ) (h : ℝ) :
    ‖s ^ (n + 1) * (((B.indicator (ladderKernel ρ f B n) h : ℝ) : ℂ) * φ h)‖ ≤
      C * B.indicator (ladderKernel ρ f B n) h := by
  have hk0 : 0 ≤ B.indicator (ladderKernel ρ f B n) h :=
    Set.indicator_nonneg (fun h _ => ladderKernel_nonneg hf0 n h) h
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk0]
  calc ‖s‖ ^ (n + 1) * (B.indicator (ladderKernel ρ f B n) h * ‖φ h‖)
      ≤ 1 * (B.indicator (ladderKernel ρ f B n) h * C) :=
        mul_le_mul (pow_le_one₀ (norm_nonneg _) hs) (mul_le_mul_of_nonneg_left (hC h) hk0)
          (mul_nonneg hk0 (norm_nonneg _)) zero_le_one
    _ = C * B.indicator (ladderKernel ρ f B n) h := by ring

/-- **The discounted ladder height density.** If `ρ = f(y) dy`, then for `‖s‖ ≤ 1` and bounded
measurable `φ`, `E[s^{τ_B} φ(S_{τ_B}); τ_B < ∞] = ∫ g_s(h) φ(h) dh` with
`g_s = ladderDensity ρ f B s`. -/
theorem setIntegral_entry_eq_integral_ladderDensity (hBm : MeasurableSet B)
    (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity fun y => ENNReal.ofReal (f y)) {s : ℂ} (hs : ‖s‖ ≤ 1)
    {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) :
    ∫ ω in {ω | firstEntry B ω < ⊤}, s ^ (firstEntry B ω).toNat * φ (entryValue B ω)
        ∂pathLaw ρ = ∫ h, ladderDensity ρ f B s h * φ h := by
  have hP : Summable fun n : ℕ => (pathLaw ρ).real {ω | firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)} :=
    (summable_nat_add_iff (f := fun n : ℕ => (pathLaw ρ).real {ω | firstEntry B ω = (n : ℕ∞)})
      1).mpr (summable_measure_toReal (fun n => measurableSet_firstEntry_eq hBm n)
        (pairwise_disjoint_firstEntry_eq B))
  have hKi := fun n => integrable_indicator_ladderKernel (ρ := ρ) hBm hf0 hfm hρ n
  have hFm : ∀ n : ℕ, Measurable fun h =>
      s ^ (n + 1) * (((B.indicator (ladderKernel ρ f B n) h : ℝ) : ℂ) * φ h) := fun n =>
    measurable_const.mul ((Complex.measurable_ofReal.comp
      ((measurable_ladderKernel hf0 hfm n).indicator hBm)).mul hφ)
  have hFi : ∀ n : ℕ, Integrable fun h =>
      s ^ (n + 1) * (((B.indicator (ladderKernel ρ f B n) h : ℝ) : ℂ) * φ h) := fun n =>
    ((hKi n).1.const_mul C).mono' (hFm n).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_mul_indicator_ladderKernel_le hf0 hs hC n))
  have hFint : ∀ n : ℕ, ∫ h, ‖s ^ (n + 1) * (((B.indicator (ladderKernel ρ f B n) h : ℝ) : ℂ) *
      φ h)‖ ≤ C * (pathLaw ρ).real {ω | firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)} := by
    intro n
    calc _ ≤ ∫ h, C * B.indicator (ladderKernel ρ f B n) h :=
          integral_mono (hFi n).norm ((hKi n).1.const_mul C)
            (norm_mul_indicator_ladderKernel_le hf0 hs hC n)
      _ = _ := by rw [integral_const_mul, (hKi n).2]
  have hFs : Summable fun n : ℕ => ∫ h, ‖s ^ (n + 1) *
      (((B.indicator (ladderKernel ρ f B n) h : ℝ) : ℂ) * φ h)‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hFint
      (hP.mul_left C)
  have ha : ∀ n : ℕ, s ^ (n + 1) * ∫ ω in {ω | firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)},
      φ (partialSum (n + 1) ω) ∂pathLaw ρ =
      ∫ h, s ^ (n + 1) * (((B.indicator (ladderKernel ρ f B n) h : ℝ) : ℂ) * φ h) := by
    intro n
    rw [setIntegral_firstEntry_succ_eq hBm hf0 hfm hρ n hφ, integral_const_mul]
  have hsucc : Summable fun n : ℕ => s ^ (n + 1) *
      ∫ ω in {ω | firstEntry B ω = ((n + 1 : ℕ) : ℕ∞)}, φ (partialSum (n + 1) ω) ∂pathLaw ρ := by
    refine Summable.of_norm_bounded (hP.mul_left C) fun n => ?_
    rw [ha n]
    exact (norm_integral_le_integral_norm _).trans (hFint n)
  rw [setIntegral_entry_eq_tsum hBm hs hφ hC, tsum_eq_zero_add' (f := fun n : ℕ => s ^ n *
    ∫ ω in {ω | firstEntry B ω = (n : ℕ∞)}, φ (partialSum n ω) ∂pathLaw ρ) hsucc]
  rw [setOf_firstEntry_zero_eq_empty, Measure.restrict_empty, integral_zero_measure, mul_zero,
    zero_add]
  simp_rw [ha]
  rw [integral_tsum_of_summable_integral_norm hFi hFs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [ladderDensity]
  by_cases hh : h ∈ B
  · simp only [indicator_of_mem hh]
    rw [← tsum_mul_right]
    exact tsum_congr fun n => by ring
  · simp [indicator_of_notMem hh]

/-- The ladder transform as the Laplace transform of the ladder density:
`E[s^{τ_B} e^{z S_{τ_B}}; τ_B < ∞] = ∫ g_s(h) e^{z h} dh` when `Re z · x ≤ 0` on `B`. -/
theorem entryTransform_eq_integral_ladderDensity (hBm : MeasurableSet B) (hf0 : ∀ y, 0 ≤ f y)
    (hfm : Measurable f) (hρ : ρ = volume.withDensity fun y => ENNReal.ofReal (f y))
    {s z : ℂ} (hs : ‖s‖ ≤ 1) (hzB : ∀ x ∈ B, z.re * x ≤ 0) :
    entryTransform ρ B s z = ∫ h, ladderDensity ρ f B s h * cexp (z * h) := by
  set φ : ℝ → ℂ := B.indicator fun h => cexp (z * h)
  have hφm : Measurable φ := (by fun_prop : Measurable fun h : ℝ => cexp (z * h)).indicator hBm
  have hφb : ∀ x, ‖φ x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ B
    · simp only [φ, indicator_of_mem hx, norm_cexp_mul_ofReal, Real.exp_le_one_iff]
      exact hzB x hx
    · simp [φ, indicator_of_notMem hx]
  have h := setIntegral_entry_eq_integral_ladderDensity (ρ := ρ) hBm hf0 hfm hρ hs hφm hφb
  rw [entryTransform]
  rw [setIntegral_congr_fun (measurableSet_firstEntry_lt_top hBm)
    (g := fun ω => s ^ (firstEntry B ω).toNat * φ (entryValue B ω)) (fun ω hω => by
      simp only [φ, indicator_of_mem (entryValue_mem hω)]), h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  by_cases hh : h ∈ B
  · simp only [φ, indicator_of_mem hh]
  · simp [ladderDensity, φ, indicator_of_notMem hh]

/-! ### Envelopes of the ladder densities -/

variable {A : Set ℝ}

/-- If `f(h - x) ≤ c e^{θ x}` for `x ∈ A ∪ {0}`, then
`∑ₙ k_n(h) ≤ c (1 - E[e^{θ S_{τ_A}}; τ_A < ∞])⁻¹` for the ladder `τ_{Aᶜ}`. -/
theorem summable_ladderKernel_of_le (hAm : MeasurableSet A) (hA : IsLadderSet A) {θ : ℝ}
    (hθ : ∀ x ∈ A, θ * x ≤ 0) (hF : expEntryMass ρ A θ < 1) (hf0 : ∀ y, 0 ≤ f y)
    {h c : ℝ} (hc : ∀ x, (x ∈ A ∨ x = 0) → f (h - x) ≤ c * Real.exp (θ * x)) :
    Summable (fun n => ladderKernel ρ f Aᶜ n h) ∧
      ∑' n, ladderKernel ρ f Aᶜ n h ≤ c * (1 - expEntryMass ρ A θ)⁻¹ := by
  have hc0 : 0 ≤ c := by
    have := hc 0 (Or.inr rfl)
    simp only [mul_zero, Real.exp_zero, mul_one, sub_zero] at this
    exact le_trans (hf0 h) this
  have hterm : ∀ n, ladderKernel ρ f Aᶜ n h ≤ c *
      ∫ ω in {ω | (n : ℕ∞) < firstEntry Aᶜ ω}, Real.exp (θ * partialSum n ω) ∂pathLaw ρ := by
    intro n
    have hmem : ∀ ω ∈ {ω | (n : ℕ∞) < firstEntry Aᶜ ω}, partialSum n ω ∈ A ∨ partialSum n ω = 0 :=
      fun ω hω => by
        rcases partialSum_mem_of_lt_firstEntry (B := Aᶜ) hω with h' | h'
        · exact Or.inl (by simpa using h')
        · exact Or.inr h'
    have hint : IntegrableOn (fun ω => Real.exp (θ * partialSum n ω))
        {ω | (n : ℕ∞) < firstEntry Aᶜ ω} (pathLaw ρ) := by
      refine Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _) (by fun_prop)
        ((ae_restrict_iff' (measurableSet_coe_lt_firstEntry hAm.compl n)).mpr
          (Filter.Eventually.of_forall fun ω hω => ?_))
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
      rcases hmem ω hω with h' | h'
      · exact hθ _ h'
      · rw [h', mul_zero]
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => hf0 _)
      (hint.const_mul c) ?_
    refine (ae_restrict_iff' (measurableSet_coe_lt_firstEntry hAm.compl n)).mpr
      (Filter.Eventually.of_forall fun ω hω => hc _ (hmem ω hω))
  have hpart : ∀ N, ∑ n ∈ range N, ladderKernel ρ f Aᶜ n h ≤
      c * (1 - expEntryMass ρ A θ)⁻¹ := by
    intro N
    calc ∑ n ∈ range N, ladderKernel ρ f Aᶜ n h
        ≤ ∑ n ∈ range N, c * ∫ ω in {ω | (n : ℕ∞) < firstEntry Aᶜ ω},
            Real.exp (θ * partialSum n ω) ∂pathLaw ρ := Finset.sum_le_sum fun n _ => hterm n
      _ = c * ∑ n ∈ range N, ∫ ω in {ω | (n : ℕ∞) < firstEntry Aᶜ ω},
            Real.exp (θ * partialSum n ω) ∂pathLaw ρ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_survival_exp_le hAm hA hθ hF N) hc0
  have hk0 : ∀ n, 0 ≤ ladderKernel ρ f Aᶜ n h := fun n => ladderKernel_nonneg hf0 n h
  exact ⟨summable_of_sum_range_le hk0 hpart, Real.tsum_le_of_sum_range_le hk0 hpart⟩

/-- The pointwise envelope of the discounted ladder density. -/
theorem norm_ladderDensity_le (hAm : MeasurableSet A) (hA : IsLadderSet A) {θ : ℝ}
    (hθ : ∀ x ∈ A, θ * x ≤ 0) (hF : expEntryMass ρ A θ < 1) (hf0 : ∀ y, 0 ≤ f y)
    {s : ℂ} (hs : ‖s‖ ≤ 1) {h c : ℝ}
    (hc : ∀ x, (x ∈ A ∨ x = 0) → f (h - x) ≤ c * Real.exp (θ * x)) :
    ‖ladderDensity ρ f Aᶜ s h‖ ≤ ‖s‖ * (c * (1 - expEntryMass ρ A θ)⁻¹) := by
  obtain ⟨hsum, hle⟩ := summable_ladderKernel_of_le hAm hA hθ hF hf0 hc
  have hc0 : 0 ≤ c * (1 - expEntryMass ρ A θ)⁻¹ :=
    le_trans (tsum_nonneg fun n => ladderKernel_nonneg hf0 n h) hle
  unfold ladderDensity
  by_cases hh : h ∈ Aᶜ
  · rw [indicator_of_mem hh]
    have hk0 : ∀ n, 0 ≤ ladderKernel ρ f Aᶜ n h := fun n => ladderKernel_nonneg hf0 n h
    have hnorm : ∀ n : ℕ, ‖s ^ (n + 1) * (ladderKernel ρ f Aᶜ n h : ℂ)‖ ≤
        ‖s‖ * ladderKernel ρ f Aᶜ n h := by
      intro n
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hk0 n), pow_succ']
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) hs)) (hk0 n)
    have hs' : Summable fun n : ℕ => ‖s‖ * ladderKernel ρ f Aᶜ n h := hsum.mul_left _
    calc ‖∑' n : ℕ, s ^ (n + 1) * (ladderKernel ρ f Aᶜ n h : ℂ)‖
        ≤ ∑' n : ℕ, ‖s ^ (n + 1) * (ladderKernel ρ f Aᶜ n h : ℂ)‖ :=
          norm_tsum_le_tsum_norm (hs'.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm)
      _ ≤ ∑' n : ℕ, ‖s‖ * ladderKernel ρ f Aᶜ n h :=
          (hs'.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm).tsum_le_tsum hnorm hs'
      _ = ‖s‖ * ∑' n, ladderKernel ρ f Aᶜ n h := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  · rw [indicator_of_notMem hh, norm_zero]
    exact mul_nonneg (norm_nonneg _) hc0

/-- **Envelope of the strict ascending ladder density**: if `f(y) ≤ D e^{-θ y}` for `y > 0`
(`θ ≥ 0`), then `‖g_s(h)‖ ≤ ‖s‖ D (1 - E[e^{θ H₋}; τ₋ < ∞])⁻¹ e^{-θ h}` for all `h`. -/
theorem norm_ladderDensity_asc_le {D θ : ℝ} (hθ : 0 ≤ θ)
    (hF : expEntryMass ρ (Iic 0) θ < 1) (hf0 : ∀ y, 0 ≤ f y)
    (hfD : ∀ y, 0 < y → f y ≤ D * Real.exp (-θ * y)) {s : ℂ} (hs : ‖s‖ ≤ 1) (h : ℝ) :
    ‖ladderDensity ρ f (Ioi 0) s h‖ ≤
      ‖s‖ * D * (1 - expEntryMass ρ (Iic 0) θ)⁻¹ * Real.exp (-θ * h) := by
  have hD : 0 ≤ D := by
    have := le_trans (hf0 1) (hfD 1 one_pos)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _) |>.trans_eq' rfl
  have hinv : 0 ≤ (1 - expEntryMass ρ (Iic 0) θ)⁻¹ := inv_nonneg.mpr (by linarith)
  by_cases hh : 0 < h
  · have hθA : ∀ x ∈ Iic (0 : ℝ), θ * x ≤ 0 := fun x hx => mul_nonpos_of_nonneg_of_nonpos hθ hx
    have hc : ∀ x, (x ∈ Iic (0 : ℝ) ∨ x = 0) → f (h - x) ≤
        (D * Real.exp (-θ * h)) * Real.exp (θ * x) := by
      intro x hx
      have hx0 : x ≤ 0 := by rcases hx with hx | hx; exact hx; exact hx.le
      calc f (h - x) ≤ D * Real.exp (-θ * (h - x)) := hfD _ (by linarith)
        _ = D * Real.exp (-θ * h) * Real.exp (θ * x) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
    have := norm_ladderDensity_le (ρ := ρ) measurableSet_Iic isLadderSet_Iic hθA hF hf0 hs hc
    rw [compl_Iic] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  · have : ladderDensity ρ f (Ioi 0) s h = 0 := by
      unfold ladderDensity
      rw [indicator_of_notMem (show h ∉ Ioi (0 : ℝ) from hh)]
    rw [this, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hD) hinv) (Real.exp_pos _).le

/-- **Envelope of the weak descending ladder density**: if `f(y) ≤ D e^{θ y}` for `y ≤ 0`
(`θ ≥ 0`), then `‖g_s(h)‖ ≤ ‖s‖ D (1 - E[e^{-θ H₊}; τ₊ < ∞])⁻¹ e^{θ h}` for all `h`. -/
theorem norm_ladderDensity_desc_le {D θ : ℝ} (hθ : 0 ≤ θ)
    (hF : expEntryMass ρ (Ioi 0) (-θ) < 1) (hf0 : ∀ y, 0 ≤ f y)
    (hfD : ∀ y, y ≤ 0 → f y ≤ D * Real.exp (θ * y)) {s : ℂ} (hs : ‖s‖ ≤ 1) (h : ℝ) :
    ‖ladderDensity ρ f (Iic 0) s h‖ ≤
      ‖s‖ * D * (1 - expEntryMass ρ (Ioi 0) (-θ))⁻¹ * Real.exp (θ * h) := by
  have hD : 0 ≤ D := by
    have := le_trans (hf0 0) (hfD 0 le_rfl)
    simpa using this
  have hinv : 0 ≤ (1 - expEntryMass ρ (Ioi 0) (-θ))⁻¹ := inv_nonneg.mpr (by linarith)
  by_cases hh : h ≤ 0
  · have hθA : ∀ x ∈ Ioi (0 : ℝ), -θ * x ≤ 0 := fun x hx => by
      have := mul_nonneg hθ (le_of_lt (show (0 : ℝ) < x from hx)); linarith
    have hc : ∀ x, (x ∈ Ioi (0 : ℝ) ∨ x = 0) → f (h - x) ≤
        (D * Real.exp (θ * h)) * Real.exp (-θ * x) := by
      intro x hx
      have hx0 : 0 ≤ x := by
        rcases hx with hx | hx
        · exact le_of_lt (show (0 : ℝ) < x from hx)
        · exact hx.symm.le
      calc f (h - x) ≤ D * Real.exp (θ * (h - x)) := hfD _ (by linarith)
        _ = D * Real.exp (θ * h) * Real.exp (-θ * x) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
    have := norm_ladderDensity_le (ρ := ρ) measurableSet_Ioi isLadderSet_Ioi hθA hF hf0 hs hc
    rw [compl_Ioi] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  · have : ladderDensity ρ f (Iic 0) s h = 0 := by
      unfold ladderDensity
      rw [indicator_of_notMem (show h ∉ Iic (0 : ℝ) from hh)]
    rw [this, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hD) hinv) (Real.exp_pos _).le

omit [IsProbabilityMeasure ρ] in
/-- The undiscounted ladder density is real and nonnegative. -/
theorem ladderDensity_one_eq (h : ℝ) :
    ladderDensity ρ f B 1 h =
      ((B.indicator (fun h => ∑' n, ladderKernel ρ f B n h) h : ℝ) : ℂ) := by
  unfold ladderDensity
  by_cases hh : h ∈ B
  · rw [indicator_of_mem hh, indicator_of_mem hh, Complex.ofReal_tsum]
    simp
  · rw [indicator_of_notMem hh, indicator_of_notMem hh, Complex.ofReal_zero]

omit [IsProbabilityMeasure ρ] in
/-- **Domination by the undiscounted density**: `|g_s(h)| ≤ ‖s‖ g_1(h)` for `‖s‖ ≤ 1`. -/
theorem norm_ladderDensity_le_one (hf0 : ∀ y, 0 ≤ f y) {s : ℂ} (hs : ‖s‖ ≤ 1) {h : ℝ}
    (hsum : Summable fun n => ladderKernel ρ f B n h) :
    ‖ladderDensity ρ f B s h‖ ≤ ‖s‖ * ‖ladderDensity ρ f B 1 h‖ := by
  have hk0 : ∀ n, 0 ≤ ladderKernel ρ f B n h := fun n => ladderKernel_nonneg hf0 n h
  rw [ladderDensity_one_eq h]
  unfold ladderDensity
  by_cases hh : h ∈ B
  · rw [indicator_of_mem hh, indicator_of_mem hh, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg hk0)]
    have hnorm : ∀ n : ℕ, ‖s ^ (n + 1) * (ladderKernel ρ f B n h : ℂ)‖ ≤
        ‖s‖ * ladderKernel ρ f B n h := by
      intro n
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hk0 n), pow_succ']
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) hs)) (hk0 n)
    have hs' : Summable fun n : ℕ => ‖s‖ * ladderKernel ρ f B n h := hsum.mul_left _
    calc ‖∑' n : ℕ, s ^ (n + 1) * (ladderKernel ρ f B n h : ℂ)‖
        ≤ ∑' n : ℕ, ‖s ^ (n + 1) * (ladderKernel ρ f B n h : ℂ)‖ :=
          norm_tsum_le_tsum_norm (hs'.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm)
      _ ≤ ∑' n : ℕ, ‖s‖ * ladderKernel ρ f B n h :=
          (hs'.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm).tsum_le_tsum hnorm hs'
      _ = ‖s‖ * ∑' n, ladderKernel ρ f B n h := tsum_mul_left
  · rw [indicator_of_notMem hh, indicator_of_notMem hh, norm_zero, Complex.ofReal_zero,
      norm_zero, mul_zero]

end PGM.WienerHopf
