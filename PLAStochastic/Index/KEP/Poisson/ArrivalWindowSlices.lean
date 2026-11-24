import PLAStochastic.ForMathlib.Probability.OrderStatistics.PoissonArrivals
import PLAStochastic.Index.KEP.CountRoute.WindowBridge

/-!
# Exact Poisson window slices of the actual exponential arrival process

The joint event specifying k arrivals before time s and the normalized
arrival coordinates has precisely the Poisson singleton mass times the
sorted-uniform coordinate law. Padding and rescaling give the same window
kernel used by the original finite-sample bridge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Renyi
open scoped ENNReal Nat

def kepArrivalCountEvent (s : ℝ) (k : ℕ) : Set (ℕ → ℝ) :=
  {g | (∀ i : Fin k, gapKeys g ((i : ℕ) + 1) ≤ s) ∧ s < gapKeys g (k + 1)}

def kepArrivalWindowCoordinates (s : ℝ) (k : ℕ) (g : ℕ → ℝ) : Fin k → ℝ :=
  fun i => s⁻¹ * gapKeys g ((i : ℕ) + 1)

theorem measurable_kepArrivalWindowCoordinates (s : ℝ) (k : ℕ) :
    Measurable (kepArrivalWindowCoordinates s k) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact (((measurable_pi_apply ((i : ℕ) + 1)).comp measurable_gapKeys)).const_mul _

theorem measurableSet_kepArrivalCountEvent (s : ℝ) (k : ℕ) :
    MeasurableSet (kepArrivalCountEvent s k) := by
  have hall : MeasurableSet {g : ℕ → ℝ | ∀ i : Fin k, gapKeys g ((i : ℕ) + 1) ≤ s} := by
    simpa only [Set.ofPred_forall, Function.comp_apply] using MeasurableSet.iInter fun i : Fin k =>
      measurableSet_le (((measurable_pi_apply ((i : ℕ) + 1)).comp measurable_gapKeys))
        (measurable_const (a := s))
  exact hall.inter (measurableSet_lt measurable_const
    ((measurable_pi_apply (k + 1)).comp measurable_gapKeys))

theorem expSeqMeasure_arrival_window {s : ℝ} (hs : 0 < s) (k : ℕ)
    {A : Set (Fin k → ℝ)} (hA : MeasurableSet A) :
    expSeqMeasure (kepArrivalCountEvent s k ∩ kepArrivalWindowCoordinates s k ⁻¹' A) =
      (poissonMeasure ⟨s, hs.le⟩) {k} * orderLaw k A := by
  have hX := (iidSeq_expCoord.indep.precomp Fin.val_injective).hasLaw_pi
    (fun i : Fin (k + 1) => hasLaw_expCoord i)
  have he : (fun g : ℕ → ℝ => fun i : Fin (k + 1) => expCoord i g) ⁻¹'
        ((psMap k) ⁻¹' arrivalWindowSet k s A) =
      kepArrivalCountEvent s k ∩ kepArrivalWindowCoordinates s k ⁻¹' A := by
    ext g
    change (arrivalWindowCoordinates k s (psMap k (fun i => expCoord i g)) ∈ A ∧
      (∀ i : Fin k, psMap k (fun i => expCoord i g) i.castSucc ≤ s) ∧
      s < psMap k (fun i => expCoord i g) (Fin.last k)) ↔
      ((∀ i : Fin k, gapKeys g ((i : ℕ) + 1) ≤ s) ∧ s < gapKeys g (k + 1)) ∧
        kepArrivalWindowCoordinates s k g ∈ A
    have hsum (i : Fin (k + 1)) :
        gammaSum (fun i : Fin (k + 1) => expCoord i g) ((i : ℕ) + 1) =
          gapKeys g ((i : ℕ) + 1) := by
      simpa only [expCoord, gapKeys] using gammaSum_expCoord g (Nat.succ_le_of_lt i.isLt)
    have hcoords : arrivalWindowCoordinates k s (psMap k (fun i => expCoord i g)) =
        kepArrivalWindowCoordinates s k g := by
      funext i
      change s⁻¹ * psMap k (fun i => expCoord i g) i.castSucc = _
      rw [psMap_apply, hsum]
      rfl
    rw [hcoords]
    simp_rw [psMap_apply, hsum]
    simp only [Fin.val_castSucc, Fin.val_last]
    tauto
  rw [← he, ← Measure.map_apply_of_aemeasurable hX.aemeasurable
    (measurePreserving_psMap.measurable (measurableSet_arrivalWindowSet s hA)),
    hX.map_eq, exponential_arrival_window hs hA, poissonMeasure_singleton, orderLaw_apply]
  have hv : volume (A ∩ closedSimplex k) = volume (A ∩ simplex k) := by
    simpa only [Measure.restrict_apply hA] using congrArg
      (fun mu : Measure (Fin k → ℝ) => mu A) (restrict_simplex_eq_closedSimplex (n := k)).symm
  rw [hv, ← mul_assoc]
  congr 1
  have hfac : 0 < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  rfl

theorem expSeqMeasure_arrival_window_kernel {s : ℝ} (hs : 0 < s) (p : ℝ) (k : ℕ)
    {C : Set (ℕ → ℝ)} (hC : MeasurableSet C) :
    expSeqMeasure (kepArrivalCountEvent s k ∩
        (fun g => padScale p (kepArrivalWindowCoordinates s k g)) ⁻¹' C) =
      (poissonMeasure ⟨s, hs.le⟩) {k} * winKernel p k C := by
  rw [winKernel_apply, Measure.map_apply (measurable_padScale p) hC]
  exact expSeqMeasure_arrival_window hs k ((measurable_padScale p) hC)

end

end PGM
