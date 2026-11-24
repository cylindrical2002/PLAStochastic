import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Defs

/-!
# Splitting the iid path at a fixed time, and time reversal

Under `pathLaw ρ`:

* `indepFun_of_dependsOnPrefix`: a functional of the first `k` coordinates is independent of
  any functional of the shifted path `shift k ω`; `measurePreserving_shift`: the shifted path
  has the law of the path. Hence `integral_mul_shift`:
  `E[F · G ∘ shift k] = E[F] E[G]`, with the companion integrability and lintegral forms.
* `measurePreserving_reverse`: reversing the first `n` coordinates preserves the law;
  `partialSum_reverse`: the reversed walk is `S n - S (n - j)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ]

theorem iIndepFun_coord : iIndepFun (fun i (ω : ℕ → ℝ) => ω i) (pathLaw ρ) :=
  iIndepFun_infinitePi (P := fun _ : ℕ => ρ) (X := fun _ => id) fun _ => measurable_id

theorem measurePreserving_eval (i : ℕ) :
    MeasurePreserving (fun ω : ℕ → ℝ => ω i) (pathLaw ρ) ρ :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => ρ) i

theorem identDistrib_coord (i : ℕ) :
    IdentDistrib (fun ω : ℕ → ℝ => ω i) (fun ω : ℕ → ℝ => ω 0) (pathLaw ρ) (pathLaw ρ) :=
  ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
    (measurePreserving_eval (ρ := ρ) i).map_eq.trans (measurePreserving_eval 0).map_eq.symm⟩

/-- The future after time `k` is independent of the first `k` coordinates. -/
theorem indepFun_shift_seqPrefix (k : ℕ) :
    IndepFun (shift k) (seqPrefix k) (pathLaw ρ) := by
  rw [IndepFun_iff_Indep]
  exact indep_future_prefix (Z := fun i (ω : ℕ → ℝ) => ω i) (fun i => measurable_pi_apply i)
    iIndepFun_coord k

/-- The shifted path has the law of the path. -/
theorem measurePreserving_shift (k : ℕ) :
    MeasurePreserving (shift k) (pathLaw ρ) (pathLaw ρ) := by
  refine ⟨measurable_shift k, ?_⟩
  have h := (identDistrib_future (Z := fun i (ω : ℕ → ℝ) => ω i) (P := pathLaw ρ)
    (fun i => measurable_pi_apply i) iIndepFun_coord identDistrib_coord k).map_eq
  exact h.trans Measure.map_id

/-- Extend a prefix by zeros. -/
def extendPrefix (k : ℕ) (x : Fin k → ℝ) : ℕ → ℝ :=
  fun i => if h : i < k then x ⟨i, h⟩ else 0

theorem measurable_extendPrefix (k : ℕ) : Measurable (extendPrefix k) := by
  refine measurable_pi_lambda _ fun i => ?_
  unfold extendPrefix
  by_cases h : i < k
  · simp only [h, dif_pos]
    exact measurable_pi_apply _
  · simp only [h, dif_neg, not_false_eq_true]
    exact measurable_const

theorem extendPrefix_seqPrefix_apply {k i : ℕ} (hi : i < k) (ω : ℕ → ℝ) :
    extendPrefix k (seqPrefix k ω) i = ω i := by
  simp [extendPrefix, seqPrefix, hi]

/-- `F` only depends on the coordinates `ω 0, …, ω (k - 1)`. -/
def DependsOnPrefix {β : Type*} (k : ℕ) (F : (ℕ → ℝ) → β) : Prop :=
  ∀ ω ω' : ℕ → ℝ, (∀ i < k, ω i = ω' i) → F ω = F ω'

theorem DependsOnPrefix.eq_comp {β : Type*} {k : ℕ} {F : (ℕ → ℝ) → β}
    (hF : DependsOnPrefix k F) (ω : ℕ → ℝ) :
    F ω = F (extendPrefix k (seqPrefix k ω)) :=
  hF _ _ fun _ hi => (extendPrefix_seqPrefix_apply hi ω).symm

theorem DependsOnPrefix.mono {β : Type*} {k m : ℕ} {F : (ℕ → ℝ) → β}
    (hF : DependsOnPrefix k F) (hkm : k ≤ m) : DependsOnPrefix m F :=
  fun ω ω' h => hF ω ω' fun i hi => h i (lt_of_lt_of_le hi hkm)

theorem dependsOnPrefix_partialSum (n : ℕ) : DependsOnPrefix n (partialSum n) :=
  fun _ _ h => partialSum_congr h

/-- A functional of the first `k` coordinates is independent of the shifted path. -/
theorem indepFun_of_dependsOnPrefix {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {k : ℕ} {F : (ℕ → ℝ) → β} {G : (ℕ → ℝ) → γ}
    (hF : Measurable F) (hFd : DependsOnPrefix k F) (hG : Measurable G) :
    IndepFun F (fun ω => G (shift k ω)) (pathLaw ρ) := by
  have h := ((indepFun_shift_seqPrefix (ρ := ρ) k).comp hG
    (hF.comp (measurable_extendPrefix k))).symm
  have hEq : F = (F ∘ extendPrefix k) ∘ seqPrefix k := by
    funext ω
    exact hFd.eq_comp ω
  rw [hEq]
  exact h

/-- Splitting at a fixed time: `E[F · G ∘ shift k] = E[F] E[G]` for `F` depending on the first
`k` coordinates. -/
theorem integral_mul_shift {𝕜 : Type*} [RCLike 𝕜] {k : ℕ} {F G : (ℕ → ℝ) → 𝕜}
    (hF : Measurable F) (hFd : DependsOnPrefix k F) (hG : Measurable G) :
    ∫ ω, F ω * G (shift k ω) ∂pathLaw ρ =
      (∫ ω, F ω ∂pathLaw ρ) * ∫ ω, G ω ∂pathLaw ρ := by
  rw [(indepFun_of_dependsOnPrefix hF hFd hG).integral_fun_mul_eq_mul_integral
    hF.aestronglyMeasurable (hG.comp (measurable_shift k)).aestronglyMeasurable]
  congr 1
  change ∫ ω, G (shift k ω) ∂pathLaw ρ = _
  rw [← integral_map (measurable_shift k).aemeasurable
    (by rw [(measurePreserving_shift k).map_eq]; exact hG.aestronglyMeasurable),
    (measurePreserving_shift k).map_eq]

theorem integrable_mul_shift {𝕜 : Type*} [RCLike 𝕜] {k : ℕ} {F G : (ℕ → ℝ) → 𝕜}
    (hF : Measurable F) (hFd : DependsOnPrefix k F) (hG : Measurable G)
    (hFi : Integrable F (pathLaw ρ)) (hGi : Integrable G (pathLaw ρ)) :
    Integrable (fun ω => F ω * G (shift k ω)) (pathLaw ρ) := by
  have hGs : Integrable (fun ω => G (shift k ω)) (pathLaw ρ) :=
    (measurePreserving_shift (ρ := ρ) k).integrable_comp_of_integrable hGi
  exact (indepFun_of_dependsOnPrefix hF hFd hG).integrable_mul hFi hGs

theorem lintegral_mul_shift {k : ℕ} {F G : (ℕ → ℝ) → ℝ≥0∞}
    (hF : Measurable F) (hFd : DependsOnPrefix k F) (hG : Measurable G) :
    ∫⁻ ω, F ω * G (shift k ω) ∂pathLaw ρ =
      (∫⁻ ω, F ω ∂pathLaw ρ) * ∫⁻ ω, G ω ∂pathLaw ρ := by
  have h := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hF
    (hG.comp (measurable_shift k)) (indepFun_of_dependsOnPrefix (ρ := ρ) hF hFd hG)
  simp only [Pi.mul_apply, Function.comp_apply] at h
  rw [h]
  congr 1
  rw [← lintegral_map hG (measurable_shift k), (measurePreserving_shift k).map_eq]

/-! ### Time reversal of the first `n` steps -/

/-- The index permutation reversing `0, …, n - 1`. -/
def reverseIndex (n i : ℕ) : ℕ := if i < n then n - 1 - i else i

theorem reverseIndex_injective (n : ℕ) : Function.Injective (reverseIndex n) := by
  intro i j h
  unfold reverseIndex at h
  split_ifs at h <;> omega

/-- The path with its first `n` steps reversed. -/
def reverse (n : ℕ) (ω : ℕ → ℝ) : ℕ → ℝ := fun i => ω (reverseIndex n i)

theorem measurable_reverse (n : ℕ) : Measurable (reverse n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem measurePreserving_reverse (n : ℕ) :
    MeasurePreserving (reverse n) (pathLaw ρ) (pathLaw ρ) :=
  ⟨measurable_reverse n,
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ρ) (reverseIndex_injective n)⟩

/-- The reversed walk: `S_j (reverse n ω) = S_n ω - S_{n-j} ω` for `j ≤ n`. -/
theorem partialSum_reverse {n j : ℕ} (hj : j ≤ n) (ω : ℕ → ℝ) :
    partialSum j (reverse n ω) = partialSum n ω - partialSum (n - j) ω := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [partialSum_succ, ih (Nat.le_of_succ_le hj)]
    have hidx : reverse n ω j = ω (n - (j + 1)) := by
      simp only [reverse, reverseIndex, show j < n by omega, if_true]
      congr 1
      omega
    have hsplit : partialSum (n - j) ω = partialSum (n - (j + 1)) ω + ω (n - (j + 1)) := by
      rw [show n - j = n - (j + 1) + 1 by omega, partialSum_succ]
    rw [hidx, hsplit]
    ring

theorem integral_comp_reverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    {H : (ℕ → ℝ) → E} (hH : AEStronglyMeasurable H (pathLaw ρ)) :
    ∫ ω, H (reverse n ω) ∂pathLaw ρ = ∫ ω, H ω ∂pathLaw ρ := by
  rw [← integral_map (measurable_reverse n).aemeasurable
    (by rw [(measurePreserving_reverse n).map_eq]; exact hH),
    (measurePreserving_reverse n).map_eq]

theorem integral_comp_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (i : ℕ)
    {g : ℝ → E} (hg : AEStronglyMeasurable g ρ) :
    ∫ ω, g (ω i) ∂pathLaw ρ = ∫ y, g y ∂ρ := by
  rw [← integral_map (measurable_pi_apply i).aemeasurable
    (by rw [(measurePreserving_eval i).map_eq]; exact hg),
    (measurePreserving_eval i).map_eq]

/-! ### The step after a prefix -/

/-- Fubini for the step following a prefix: for a functional `X` of the first `k` coordinates,
`E[Ψ(X, ω k)] = E[∫ Ψ(X, y) dρ(y)]`. -/
theorem lintegral_comp_prefix_eval {α : Type*} [MeasurableSpace α] {k : ℕ}
    {X : (ℕ → ℝ) → α} (hX : Measurable X) (hXd : DependsOnPrefix k X)
    {Ψ : α × ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ ω, Ψ (X ω, ω k) ∂pathLaw ρ = ∫⁻ ω, ∫⁻ y, Ψ (X ω, y) ∂ρ ∂pathLaw ρ := by
  have hind : IndepFun X (fun ω : ℕ → ℝ => ω k) (pathLaw ρ) := by
    have h := indepFun_of_dependsOnPrefix (ρ := ρ) hX hXd (measurable_pi_apply 0)
    simpa only [shift_apply, add_zero] using h
  have hmap : (pathLaw ρ).map (fun ω => (X ω, ω k)) = ((pathLaw ρ).map X).prod ρ := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable
      (measurable_pi_apply k).aemeasurable).mp hind, (measurePreserving_eval k).map_eq]
  calc ∫⁻ ω, Ψ (X ω, ω k) ∂pathLaw ρ
      = ∫⁻ p, Ψ p ∂((pathLaw ρ).map (fun ω => (X ω, ω k))) :=
        (lintegral_map hΨ (hX.prodMk (measurable_pi_apply k))).symm
    _ = ∫⁻ p, Ψ p ∂(((pathLaw ρ).map X).prod ρ) := by rw [hmap]
    _ = ∫⁻ x, ∫⁻ y, Ψ (x, y) ∂ρ ∂((pathLaw ρ).map X) := lintegral_prod _ hΨ.aemeasurable
    _ = ∫⁻ ω, ∫⁻ y, Ψ (X ω, y) ∂ρ ∂pathLaw ρ := lintegral_map hΨ.lintegral_prod_right' hX

end PGM.WienerHopf
