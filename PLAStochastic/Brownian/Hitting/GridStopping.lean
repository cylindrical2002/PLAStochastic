import PLAStochastic.Brownian.Markov.ExponentialMartingale
import PLAStochastic.Brownian.Hitting.LowerBarrier
import Mathlib.Probability.Process.HittingTime
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual finite-grid stopping times for drifted Brownian motion

Discrete hitting indices are converted to stopping times on the original
nonnegative real time axis. The cutoff and the countable range are proved.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def gridFiltration (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (δ : ℝ≥0) :
    Filtration ℕ ‹MeasurableSpace Ω› where
  seq n := F (δ * n)
  mono' _ _ h := F.mono (mul_le_mul_of_nonneg_left (by exact_mod_cast h) (show 0 ≤ δ from bot_le))
  le' n := F.le (δ * n)

def gridHittingIndex (X : ℝ≥0 → Ω → ℝ) (S : Set ℝ) (δ : ℝ≥0) (N : ℕ) : Ω → ℕ :=
  hittingBtwn (fun n ω => X (δ * n) ω) S 0 N

def gridHittingTime (X : ℝ≥0 → Ω → ℝ) (S : Set ℝ) (δ : ℝ≥0) (N : ℕ) (ω : Ω) : ℝ≥0 :=
  δ * gridHittingIndex X S δ N ω

omit [MeasurableSpace Ω] in
theorem gridHittingTime_le (X : ℝ≥0 → Ω → ℝ) (S : Set ℝ) (δ : ℝ≥0) (N : ℕ) (ω : Ω) :
    gridHittingTime X S δ N ω ≤ δ * N := by
  have hn : gridHittingIndex X S δ N ω ≤ N :=
    hittingBtwn_le (u := fun (n : ℕ) ω => X (δ * n) ω) (s := S) (n := 0) (m := N) ω
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (show 0 ≤ δ from bot_le)

theorem isStoppingTime_gridHittingTime {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X : ℝ≥0 → Ω → ℝ} (hX : Adapted F X) {S : Set ℝ} (hS : MeasurableSet S)
    {δ : ℝ≥0} (hδ : 0 < δ) (N : ℕ) :
    IsStoppingTime F (fun ω => (gridHittingTime X S δ N ω : WithTop ℝ≥0)) := by
  have had : Adapted (gridFiltration F δ) (fun n ω => X (δ * n) ω) := fun n => hX (δ * n)
  have hstop := had.isStoppingTime_hittingBtwn (n := 0) (n' := N) hS
  intro t
  let k := ⌊t / δ⌋₊
  have hk : δ * (k : ℝ≥0) ≤ t := by
    have hf := Nat.floor_le (show (0 : ℝ≥0) ≤ t / δ from bot_le)
    exact (by simpa only [mul_comm] using (le_div_iff₀ hδ).mp hf)
  have hm : MeasurableSet[F (δ * k)] {ω | gridHittingIndex X S δ N ω ≤ k} := by
    simpa only [gridFiltration, gridHittingIndex, WithTop.coe_le_coe] using! hstop k
  convert F.mono hk _ hm using 1
  ext ω
  simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
  change δ * (gridHittingIndex X S δ N ω : ℝ≥0) ≤ t ↔ gridHittingIndex X S δ N ω ≤ k
  rw [mul_comm, ← le_div_iff₀ hδ, Nat.le_floor_iff (show (0 : ℝ≥0) ≤ t / δ from bot_le)]

omit [MeasurableSpace Ω] in
theorem gridHittingTime_countable_range (X : ℝ≥0 → Ω → ℝ) (S : Set ℝ) (δ : ℝ≥0) (N : ℕ) :
    (Set.range (fun ω => (gridHittingTime X S δ N ω : WithTop ℝ≥0))).Countable := by
  have h := (Set.to_countable (Set.range (gridHittingIndex X S δ N))).image
    (fun k : ℕ => ((δ * k : ℝ≥0) : WithTop ℝ≥0))
  simpa only [← Set.range_comp, Function.comp_def, gridHittingTime] using h

def driftBarrierSet (a b : ℝ) : Set ℝ := Set.Iio (-b) ∪ Set.Ioi a

theorem measurableSet_driftBarrierSet (a b : ℝ) : MeasurableSet (driftBarrierSet a b) :=
  measurableSet_Iio.union measurableSet_Ioi

variable {B : ℝ≥0 → Ω → ℝ}

def measurableBrownianDrift (hB : IsPreBrownianReal B μ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  measurableBrownian hB t ω - (t : ℝ)

theorem adapted_measurableBrownianDrift (hB : IsPreBrownianReal B μ) :
    Adapted (brownianNaturalFiltration hB) (measurableBrownianDrift hB) := by
  intro t
  exact (Filtration.stronglyAdapted_natural
    (fun t => (measurable_measurableBrownian hB t).stronglyMeasurable) t).measurable.sub_const _

theorem brownianGridExit_isStoppingTime (hB : IsPreBrownianReal B μ)
    (a b : ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (N : ℕ) :
    IsStoppingTime (brownianNaturalFiltration hB)
      (fun ω => (gridHittingTime (measurableBrownianDrift hB) (driftBarrierSet a b) δ N ω :
        WithTop ℝ≥0)) :=
  isStoppingTime_gridHittingTime (adapted_measurableBrownianDrift hB)
    (measurableSet_driftBarrierSet a b) hδ N

theorem integral_brownianGridExit (hB : IsPreBrownianReal B μ)
    (a b : ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (N : ℕ) :
    (∫ ω, stoppedValue (brownianExponential hB)
      (fun ω => (gridHittingTime (measurableBrownianDrift hB) (driftBarrierSet a b) δ N ω :
        WithTop ℝ≥0)) ω ∂μ) = 1 := by
  apply integral_brownianExponential_stopped hB (brownianGridExit_isStoppingTime hB a b hδ N)
    (T := δ * N)
  · intro ω
    exact_mod_cast gridHittingTime_le (measurableBrownianDrift hB) (driftBarrierSet a b) δ N ω
  · exact gridHittingTime_countable_range _ _ _ _

def reciprocalMesh (n : ℕ) : ℝ≥0 := 1 / (n + 1 : ℝ≥0)

theorem reciprocalMesh_pos (n : ℕ) : 0 < reciprocalMesh n := by
  unfold reciprocalMesh
  positivity

theorem reciprocalMesh_tendsto_zero : Tendsto reciprocalMesh atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem reciprocalMesh_mul_cutoff (H n : ℕ) :
    reciprocalMesh n * (H * (n + 1) : ℕ) = (H : ℝ≥0) := by
  simp [reciprocalMesh, mul_comm]

def upperGridIndex (n : ℕ) (t : ℝ≥0) : ℕ := ⌈t / reciprocalMesh n⌉₊

def upperGridTime (n : ℕ) (t : ℝ≥0) : ℝ≥0 := reciprocalMesh n * upperGridIndex n t

theorem upperGridIndex_le {H : ℕ} {t : ℝ≥0} (ht : t ≤ H) (n : ℕ) :
    upperGridIndex n t ≤ H * (n + 1) := by
  apply Nat.ceil_le.mpr
  rw [div_le_iff₀ (reciprocalMesh_pos n), mul_comm, reciprocalMesh_mul_cutoff]
  exact ht

theorem le_upperGridTime (n : ℕ) (t : ℝ≥0) : t ≤ upperGridTime n t := by
  have h := (div_le_iff₀ (reciprocalMesh_pos n)).mp (Nat.le_ceil (t / reciprocalMesh n))
  simpa only [upperGridTime, upperGridIndex, mul_comm] using h

theorem upperGridTime_lt (n : ℕ) (t : ℝ≥0) : upperGridTime n t < t + reciprocalMesh n := by
  have h := mul_lt_mul_of_pos_left
    (Nat.ceil_lt_add_one (show 0 ≤ t / reciprocalMesh n from bot_le)) (reciprocalMesh_pos n)
  simpa only [upperGridTime, upperGridIndex, mul_add, mul_one,
    mul_div_cancel₀ t (reciprocalMesh_pos n).ne'] using h

theorem upperGridTime_tendsto (t : ℝ≥0) :
    Tendsto (fun n => upperGridTime n t) atTop (𝓝 t) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using tendsto_const_nhds.add reciprocalMesh_tendsto_zero)
  · exact fun n => le_upperGridTime n t
  · exact fun n => (upperGridTime_lt n t).le

/-- First entrance in an open target set, with a deterministic endpoint included
as a fallback. The definition is meaningful on every path. -/
def boundedOpenExitTime (X : ℝ≥0 → Ω → ℝ) (S : Set ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  sInf (insert T {t : ℝ≥0 | t ≤ T ∧ X t ω ∈ S})

omit [MeasurableSpace Ω] in
theorem boundedOpenExitTime_le (X : ℝ≥0 → Ω → ℝ) (S : Set ℝ) (T : ℝ≥0) (ω : Ω) :
    boundedOpenExitTime X S T ω ≤ T :=
  csInf_le ⟨0, fun _ _ => bot_le⟩ (Set.mem_insert _ _)

omit [MeasurableSpace Ω] in
theorem boundedOpenExitTime_le_grid (X : ℝ≥0 → Ω → ℝ) (S : Set ℝ)
    (H n : ℕ) (ω : Ω) :
    boundedOpenExitTime X S H ω ≤
      gridHittingTime X S (reciprocalMesh n) (H * (n + 1)) ω := by
  apply csInf_le ⟨0, fun _ _ => bot_le⟩
  by_cases heq : gridHittingIndex X S (reciprocalMesh n) (H * (n + 1)) ω = H * (n + 1)
  · apply Set.mem_insert_iff.mpr
    left
    change reciprocalMesh n * (gridHittingIndex X S (reciprocalMesh n) (H * (n + 1)) ω : ℝ≥0) = H
    rw [heq, reciprocalMesh_mul_cutoff]
  · apply Set.mem_insert_of_mem
    refine ⟨?_, ?_⟩
    · exact (gridHittingTime_le X S _ _ ω).trans_eq (reciprocalMesh_mul_cutoff H n)
    · have hn : gridHittingIndex X S (reciprocalMesh n) (H * (n + 1)) ω ≤ H * (n + 1) :=
        hittingBtwn_le (u := fun (k : ℕ) ω => X (reciprocalMesh n * k) ω) ω
      exact hittingBtwn_mem_set_of_hittingBtwn_lt (lt_of_le_of_ne hn heq)

omit [MeasurableSpace Ω] in
/-- The actual finite-grid hitting times converge to the continuous open-exit
time. Openness and path continuity supply the missing grid detection. -/
theorem gridHittingTime_tendsto_boundedOpenExitTime {X : ℝ≥0 → Ω → ℝ} {S : Set ℝ}
    (hS : IsOpen S) {ω : Ω} (hX : Continuous (X · ω)) (H : ℕ) :
    Tendsto (fun n => gridHittingTime X S (reciprocalMesh n) (H * (n + 1)) ω)
      atTop (𝓝 (boundedOpenExitTime X S H ω)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (boundedOpenExitTime_le_grid X S H n ω))
  · intro b hb
    obtain ⟨t, ht, htb⟩ := exists_lt_of_csInf_lt (Set.insert_nonempty (H : ℝ≥0) _) hb
    rcases Set.mem_insert_iff.mp ht with heq | ht
    · subst t
      exact Eventually.of_forall (fun n =>
        ((gridHittingTime_le X S _ _ ω).trans_eq (reciprocalMesh_mul_cutoff H n)).trans_lt htb)
    · have hmem : ∀ᶠ n in atTop, X (upperGridTime n t) ω ∈ S :=
        ((hX.tendsto t).comp (upperGridTime_tendsto t)).eventually (hS.mem_nhds ht.2)
      have hlt := (upperGridTime_tendsto t).eventually_lt_const htb
      filter_upwards [hmem, hlt] with n hn hnb
      have hidx : gridHittingIndex X S (reciprocalMesh n) (H * (n + 1)) ω ≤ upperGridIndex n t :=
        hittingBtwn_le_of_mem (Nat.zero_le _) (upperGridIndex_le ht.1 n) hn
      have htime : gridHittingTime X S (reciprocalMesh n) (H * (n + 1)) ω ≤ upperGridTime n t :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hidx) (show 0 ≤ reciprocalMesh n from bot_le)
      exact htime.trans_lt hnb

def actualBrownianDrift (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := B t ω - (t : ℝ)

theorem gridHittingTime_brownian_ae_eq_original (hB : IsPreBrownianReal B μ)
    (S : Set ℝ) (δ : ℝ≥0) (N : ℕ) :
    gridHittingTime (measurableBrownianDrift hB) S δ N =ᵐ[μ]
      gridHittingTime (actualBrownianDrift B) S δ N := by
  filter_upwards [measurableBrownian_countable_ae_eq hB (fun k : ℕ => δ * k)] with ω hω
  have hp : (fun n : ℕ => measurableBrownianDrift hB (δ * n) ω) =
      (fun n : ℕ => actualBrownianDrift B (δ * n) ω) := by
    funext n
    exact congrArg (fun x : ℝ => x - ((δ * n : ℝ≥0) : ℝ)) (hω n)
  have hh := congrArg (fun f : ℕ → ℝ => hittingBtwn (fun n (_ : Unit) => f n) S 0 N ()) hp
  exact congrArg (fun k : ℕ => δ * (k : ℝ≥0)) hh

/-- The finite-grid stopping times converge to the actual Brownian open-exit
time, so the bounded continuous exit has exponential expectation one. -/
theorem integral_actualBrownianExponential_bounded_exit (hB : IsBrownianReal B μ)
    (a b : ℝ) (H : ℕ) :
    Integrable (fun ω => actualBrownianExponential B
      (boundedOpenExitTime (actualBrownianDrift B) (driftBarrierSet a b) H ω) ω) μ ∧
    (∫ ω, actualBrownianExponential B
      (boundedOpenExitTime (actualBrownianDrift B) (driftBarrierSet a b) H ω) ω ∂μ) = 1 := by
  apply integral_actualBrownianExponential_stopping_limit hB
    (τ := fun n ω => (gridHittingTime (measurableBrownianDrift hB.toIsPreBrownianReal)
      (driftBarrierSet a b) (reciprocalMesh n) (H * (n + 1)) ω : WithTop ℝ≥0))
    (T := H)
    (fun n => brownianGridExit_isStoppingTime hB.toIsPreBrownianReal a b (reciprocalMesh_pos n) _)
  · intro n ω
    exact_mod_cast (gridHittingTime_le (measurableBrownianDrift hB.toIsPreBrownianReal)
      (driftBarrierSet a b) _ _ ω).trans_eq (reciprocalMesh_mul_cutoff H n)
  · intro n
    exact gridHittingTime_countable_range _ _ _ _
  · have heq : ∀ᵐ ω ∂μ, ∀ n,
        gridHittingTime (measurableBrownianDrift hB.toIsPreBrownianReal)
          (driftBarrierSet a b) (reciprocalMesh n) (H * (n + 1)) ω =
        gridHittingTime (actualBrownianDrift B)
          (driftBarrierSet a b) (reciprocalMesh n) (H * (n + 1)) ω :=
      ae_all_iff.mpr (fun n => gridHittingTime_brownian_ae_eq_original hB.toIsPreBrownianReal
        (driftBarrierSet a b) (reciprocalMesh n) (H * (n + 1)))
    filter_upwards [hB.cont, heq] with ω hω heqω
    have hc : Continuous (actualBrownianDrift B · ω) := hω.sub continuous_subtype_val
    have ht := gridHittingTime_tendsto_boundedOpenExitTime (S := driftBarrierSet a b)
      (isOpen_Iio.union isOpen_Ioi) hc H
    convert! ht.congr (fun n => (heqω n).symm) using 1

end BrownianAffine
