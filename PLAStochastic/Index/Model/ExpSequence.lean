import PLAStochastic.Index.Model.ExpGaps
import Mathlib.Probability.Independence.InfinitePi

/-!
# A canonical iid Exp(1) sequence

The coordinates of `ℕ → ℝ` under the infinite product of `expMeasure 1` are iid
Exp(1).  It carries the Rényi representation of Model K.  The expectation theorems are
transferred to arbitrary sample spaces; the pathwise uniform theorem `K_RE_uniform` is stated
on this space, because its good event is an event of the exponential variables alone.
-/

namespace PGM

open MeasureTheory ProbabilityTheory

/-- The product law of an iid Exp(1) sequence. -/
noncomputable def expSeqMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => expMeasure 1)

instance : IsProbabilityMeasure expSeqMeasure := by
  unfold expSeqMeasure; infer_instance

/-- The coordinate process. -/
def expCoord (i : ℕ) (ω : ℕ → ℝ) : ℝ := ω i

theorem measurable_expCoord (i : ℕ) : Measurable (expCoord i) := measurable_pi_apply i

theorem hasLaw_expCoord (i : ℕ) : HasLaw (expCoord i) (expMeasure 1) expSeqMeasure :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => expMeasure 1) i).hasLaw

theorem iidSeq_expCoord : IIDSeq expSeqMeasure expCoord where
  measurable := measurable_expCoord
  indep := iIndepFun_infinitePi (P := fun _ : ℕ => expMeasure 1) (X := fun _ x => x)
    (fun _ => measurable_id)
  ident t := ⟨(measurable_expCoord t).aemeasurable, (measurable_expCoord 0).aemeasurable,
    by rw [(hasLaw_expCoord t).map_eq, (hasLaw_expCoord 0).map_eq]⟩

theorem gapLaw_expCoord : GapLaw expSeqMeasure expCoord 1 1 16 :=
  gapLaw_exp iidSeq_expCoord (hasLaw_expCoord 0)

/-- The shifted coordinates `ω (s+1)` are again an iid Exp(1) gap law. -/
theorem gapLaw_expCoord_succ : GapLaw expSeqMeasure (fun s => expCoord (s + 1)) 1 1 16 := by
  have h := gapLaw_expCoord.shift 1
  simpa [add_comm] using h

end PGM
