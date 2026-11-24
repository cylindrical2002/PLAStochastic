import PLAStochastic.Swing.DenseSampling.Rejection.GuardMeasurability
import PLAStochastic.Swing.DenseSampling.Rejection.ContinuationBudget
import PLAStochastic.Swing.DenseSampling.CarriedPrefix.SmallStateRatio

/-! # Conditional estimates at every actual rejection observation -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The guard uses only information already observed at the rejection sample. -/
def nativeRejectionGuard (t y : ℕ → ℝ) (M h γ : ℝ) (b : ℕ) : Prop :=
  nativeRejectionAt t y 1 b ∧ -M*h ≤ nativeRejectionState t y 1 b ∧
    nativeRejectionState t y 1 b ≤ 2*γ

def nativeRejectionLongCost (y : ℕ → ℝ) (M γ : ℝ) (h : ℝ≥0) (N b : ℕ) : ℝ :=
  let t : ℕ → ℝ := fun j => (j : ℝ)*(h : ℝ)
  if nativeRejectionGuard t y M h γ b then
    nativeCarriedLongIndicator (nativeCarriedFuture y (nativeCarryAnchor t y 1 b) b)
      (nativeRejectionState t y 1 b) M h N else 0

def nativeRejectionBudgetCost (y : ℕ → ℝ) (M γ : ℝ) (h H : ℝ≥0) (b : ℕ) : ℝ :=
  if nativeRejectionGuard (fun j => (j : ℝ)*(h : ℝ)) y M h γ b
    then nativeRejectionDuration y 1 h H b else 0

theorem measurableSet_nativeRejectionGuard (t : ℕ → ℝ) (ht : StrictMono t)
    (M h γ : ℝ) (b : ℕ) : MeasurableSet {y : ℕ → ℝ | nativeRejectionGuard t y M h γ b} :=
  (measurableSet_nativeRejectionAt t ht 1 b).inter
    ((measurableSet_le measurable_const (measurable_nativeRejectionState t ht 1 b)).inter
      (measurableSet_le (measurable_nativeRejectionState t ht 1 b) measurable_const))

theorem nativeRejectionGuard_prefix_congr (t : ℕ → ℝ) (M h γ : ℝ) {y y' : ℕ → ℝ} {b : ℕ}
    (hy : ∀ j ≤ b+1, y j = y' j) :
    nativeRejectionGuard t y M h γ b ↔ nativeRejectionGuard t y' M h γ b := by
  unfold nativeRejectionGuard
  rw [nativeRejectionAt_prefix_congr t 1 hy, nativeRejectionState_prefix_congr t 1 hy]

theorem measurable_nativeRejectionLongCost (M γ : ℝ) {h : ℝ≥0} (hh : 0 < h) (N b : ℕ) :
    Measurable (fun y : ℕ → ℝ => nativeRejectionLongCost y M γ h N b) := by
  have ht := strictMono_mesh_times (show (0 : ℝ) < h by exact_mod_cast hh)
  apply Measurable.ite (measurableSet_nativeRejectionGuard _ ht M h γ b) _ measurable_const
  exact measurable_nativeCarriedLongIndicator _ (measurable_nativeRejectionState _ ht 1 b)
    (fun j => measurable_nativeCarriedFuture _ (measurable_nativeCarryAnchor _ ht 1 b)
      (fun i => measurable_pi_apply i) b j) M (by exact_mod_cast hh) N

theorem measurable_nativeRejectionBudgetCost (M γ : ℝ) {h : ℝ≥0} (hh : 0 < h) (H : ℝ≥0) (b : ℕ) :
    Measurable (fun y : ℕ → ℝ => nativeRejectionBudgetCost y M γ h H b) := by
  have ht := strictMono_mesh_times (show (0 : ℝ) < h by exact_mod_cast hh)
  apply Measurable.ite (measurableSet_nativeRejectionGuard _ ht M h γ b) _ measurable_const
  exact measurable_nativeCarriedTruncatedDuration _ (measurable_nativeRejectionState _ ht 1 b)
    (fun j => measurable_nativeCarriedFuture _ (measurable_nativeCarryAnchor _ ht 1 b)
      (fun i => measurable_pi_apply i) b j) 1 hh H

/-- The past is conditioned at b+1, retaining both the carry and its inherited
sign. The full fresh path is independent of this history by Brownian increments. -/
theorem exists_native_rejection_conditional_comparison {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {M : ℝ} (hM : 0 ≤ M) {q H : ℝ≥0} (hq : 0 < q) (hH : 0 < H)
    (hHs : (H : ℝ) ≤ 1/32) (hMH : M*(H : ℝ) ≤ 1) {β : ℝ} (hβ : 0 < β) :
    ∃ γ h₀ : ℝ, 0 < γ ∧ 0 < h₀ ∧ ∀ h : ℝ≥0, 0 < h → (h : ℝ) ≤ h₀ →
    ∀ b N : ℕ, q ≤ (N : ℝ≥0)*h → ∀ T : ℝ, (N : ℝ)*(h : ℝ) ≤ T →
    (∫ ω, nativeRejectionLongCost (fun j => B ((j : ℝ≥0)*h) ω) M γ h N b ∂μ) ≤
      β*(∫ ω, nativeRejectionBudgetCost (fun j => B ((j : ℝ≥0)*h) ω) M γ h H b ∂μ)+
        (2*T*(h : ℝ)^3)*μ.real {ω | nativeRejectionGuard (fun j => (j : ℝ)*(h : ℝ))
          (fun j => B ((j : ℝ≥0)*h) ω) M h γ b} := by
  obtain ⟨γ, h₀, hγ, hh₀, hc⟩ := exists_native_carried_small_state_guard_comparison
    (α := ℕ → ℝ) hB hM hq hH hHs hMH hβ
  refine ⟨γ, h₀, hγ, hh₀, ?_⟩
  intro h hh hhh b N hN T hNT
  let t : ℕ → ℝ := fun j => (j : ℝ)*(h : ℝ)
  have ht : StrictMono t := strictMono_mesh_times (by exact_mod_cast hh)
  let X := brownianGridPast B h (b+1)
  let W := fun y => nativeRejectionState t y 1 b
  let S := fun y => nativeRejectionSign t y 1 b
  let U := {y | nativeRejectionGuard t y M h γ b}
  have hi := hc h hh hhh _ (hB.shift (((b+1 : ℕ) : ℝ≥0)*h)) X
    (aemeasurable_brownianGridPast hB h (b+1)) (indepFun_brownianGridPast_future hB h (b+1))
    W S (measurable_nativeRejectionState t ht 1 b) (measurable_nativeRejectionSign t ht 1 b)
    U (measurableSet_nativeRejectionGuard t ht M h γ b) (fun _ hx => hx.2) N hN T hNT
  have hp (ω : Ω) : ∀ j ≤ b+1, X ω j = B ((j : ℝ≥0)*h) ω := by
    intro j hj
    exact if_pos hj
  have hg (ω : Ω) : X ω ∈ U ↔ nativeRejectionGuard t (fun j => B ((j : ℝ≥0)*h) ω) M h γ b :=
    nativeRejectionGuard_prefix_congr t M h γ (hp ω)
  have hw (ω : Ω) : W (X ω) = nativeRejectionState t (fun j => B ((j : ℝ≥0)*h) ω) 1 b :=
    nativeRejectionState_prefix_congr t 1 (hp ω)
  have hs (ω : Ω) : S (X ω) = nativeRejectionSign t (fun j => B ((j : ℝ≥0)*h) ω) 1 b :=
    nativeRejectionSign_prefix_congr t 1 (fun j hj => hp ω j (by omega))
  have hd (ω : Ω) : (fun j : ℕ => nativePolarity (S (X ω))*
      (B (((b+1 : ℕ) : ℝ≥0)*h+(j : ℝ≥0)*h) ω-B (((b+1 : ℕ) : ℝ≥0)*h) ω)) =
      nativeCarriedFuture (fun j => B ((j : ℝ≥0)*h) ω)
        (nativeCarryAnchor t (fun j => B ((j : ℝ≥0)*h) ω) 1 b) b := by
    funext j
    rw [hs ω]
    simp only [nativeCarriedFuture, nativeRejectionSign, Nat.cast_add, add_mul]
  have hset : X ⁻¹' U = {ω | nativeRejectionGuard t (fun j => B ((j : ℝ≥0)*h) ω) M h γ b} := by
    ext ω
    exact hg ω
  rw [hset] at hi
  simpa only [hg, hw, hd, nativeRejectionLongCost, nativeRejectionBudgetCost,
    nativeRejectionDuration, nativeRejectionState, t, Set.preimage_ofPred_eq, U] using hi

end SwingRepair
