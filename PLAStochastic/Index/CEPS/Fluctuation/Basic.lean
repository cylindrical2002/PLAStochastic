import PLAStochastic.ForMathlib.Probability.RandomWalk.Fluctuation.SparreAndersenEndpoint
import PLAStochastic.Index.GEP.LayerLaw.ActualLayers

/-!
# Endpoint-preserving fluctuation identities on the actual gap space

The affine increments include centered walks and the slope-dependent walks
used by the segment kernel. The identities use the actual canonical iid law.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set SwingRepair.Fluctuation

/-- An affine transform of the actual canonical iid gap coordinate. -/
def cepsWalkIncrement (a b : ℝ) (i : ℕ) (g : ℕ → ℝ) : ℝ := a * g i + b

theorem measurable_cepsWalkIncrement (a b : ℝ) (i : ℕ) :
    Measurable (cepsWalkIncrement a b i) := by
  unfold cepsWalkIncrement
  fun_prop

/-- Sparre Andersen retains the terminal position for every actual affine gap walk. -/
theorem ceps_fluctuation_endpoint (ν : ProbabilityMeasure ℝ) (a b : ℝ) (n k : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    iidLaw ν {g | posCount (fun i => cepsWalkIncrement a b i g) (List.range n) = k ∧
        ((List.range n).map fun i => cepsWalkIncrement a b i g).sum ∈ B} =
      iidLaw ν {g | IsFirstArgmax (fun i => cepsWalkIncrement a b i g) (List.range n) k ∧
        ((List.range n).map fun i => cepsWalkIncrement a b i g).sum ∈ B} := by
  have hseq := iidSeq_gapCoord ν
  have haff : Measurable (fun x : ℝ => a * x + b) := (measurable_const.mul measurable_id).add_const b
  have hi : iIndepFun (cepsWalkIncrement a b) (iidLaw ν) :=
    hseq.indep.comp (fun _ x => a * x + b) (fun _ => haff)
  have hcommon : ∀ i, (iidLaw ν).map (cepsWalkIncrement a b i) =
      (iidLaw ν).map (cepsWalkIncrement a b 0) := fun i =>
    ((hseq.ident i).comp haff).map_eq
  exact measure_posCount_endpoint_eq_measure_isFirstArgmax_endpoint
    (measurable_cepsWalkIncrement a b) hi hcommon n k hB

end

end PGM
