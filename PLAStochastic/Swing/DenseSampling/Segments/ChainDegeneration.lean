import PLAStochastic.Swing.Algorithm.OutputChain
import PLAStochastic.Swing.DenseSampling.Segments.BoundaryNonextension
import PLAStochastic.Swing.DenseSampling.Segments.SignedBoundaryFlip

/-!
# Fixed-index degeneration of native output chains

The induction uses the indexed geometry of the true chain. Convergence before
the horizon forces each fixed segment to be a completed rejection segment;
nonextension then collapses its successor and the signed rejection law flips
the carried boundary error.
-/

noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- Total indexing of an observed native output list. The default is only used
outside the list; the limit theorems prove eventual existence of each index. -/
def nativeSegmentAt (segs : List NativeSegment) (k : ℕ) : NativeSegment :=
  segs[k]?.getD ⟨0, 0, 0, 0⟩

theorem nativeSegmentAt_eq_getElem {segs : List NativeSegment} {k : ℕ}
    (hk : k < segs.length) : nativeSegmentAt segs k = segs[k] := by
  simp only [nativeSegmentAt, List.getElem?_eq_getElem hk, Option.getD_some]

/-- An endpoint converging strictly before the observation horizon is
eventually followed by another actual segment, so it cannot be the EOF line. -/
theorem eventually_native_next_index (f : C(ℝ, ℝ)) {ε σ H : ℝ} (hH : σ < H)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ} {N : ι → ℕ}
    {segs : ι → List NativeSegment}
    (hchain : ∀ᶠ i in l, NativeChain (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε 0 (f 0) (N i) (segs i))
    (hhorizon : Tendsto (fun i => (N i : ℝ) * h i) l (𝓝 H))
    (k : ℕ) (hk : ∀ᶠ i in l, k < (segs i).length)
    (hfinish : Tendsto (fun i => ((nativeSegmentAt (segs i) k).finish : ℝ) * h i) l (𝓝 σ)) :
    ∀ᶠ i in l, k + 1 < (segs i).length := by
  filter_upwards [hchain, hk,
    hfinish.eventually_lt_const (show σ < (σ + H) / 2 by linarith),
    hhorizon.eventually_const_lt (show (σ + H) / 2 < H by linarith)] with i hc hi he hN
  by_contra hbad
  have hlast : k + 1 = (segs i).length := by omega
  rw [nativeSegmentAt_eq_getElem hi, hc.getElem_last_finish hi hlast] at he
  linarith

/-- Every fixed index in a true native chain eventually exists, its endpoint
converges to the first pinch, and its fitted-minus-sample error alternates.
The premises for index zero are supplied by the separately proved true first
native segment theorem. No premise asserts any later segment limit. -/
theorem nativeChain_fixed_index_degeneracy (f : C(ℝ, ℝ)) {ε σ H η : ℝ}
    (hε : 0 < ε) (hσ : 0 ≤ σ) (hH : σ < H) (hη : |η| = ε)
    (hno : ∀ q : ℝ, |f σ - q| = ε → ∀ T : ℝ, 0 < T → ¬ ∃ a,
      continuousSlopeFeasible (fun t => f (σ + t)) q ε T a)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ} {N : ι → ℕ}
    {segs : ι → List NativeSegment} (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0))
    (hchain : ∀ᶠ i in l, NativeChain (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε 0 (f 0) (N i) (segs i))
    (hhorizon : Tendsto (fun i => (N i : ℝ) * h i) l (𝓝 H))
    (hfirst : ∀ᶠ i in l, 0 < (segs i).length)
    (hfirstTime : Tendsto (fun i => ((nativeSegmentAt (segs i) 0).finish : ℝ) * h i) l (𝓝 σ))
    (hfirstOffset : Tendsto (fun i => nativeSegmentEndpoint (fun j => (j : ℝ) * h i)
      (nativeSegmentAt (segs i) 0) - f (((nativeSegmentAt (segs i) 0).finish : ℝ) * h i)) l (𝓝 η)) :
    ∀ k : ℕ,
      (∀ᶠ i in l, k + 1 < (segs i).length) ∧
      Tendsto (fun i => ((nativeSegmentAt (segs i) k).finish : ℝ) * h i) l (𝓝 σ) ∧
      Tendsto (fun i => nativeSegmentEndpoint (fun j => (j : ℝ) * h i)
        (nativeSegmentAt (segs i) k) - f (((nativeSegmentAt (segs i) k).finish : ℝ) * h i))
        l (𝓝 ((-1 : ℝ) ^ k * η)) := by
  have habs (k : ℕ) : |(-1 : ℝ) ^ k * η| = ε := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, hη]
  have hmain : ∀ k : ℕ,
      (∀ᶠ i in l, k < (segs i).length) ∧
      Tendsto (fun i => ((nativeSegmentAt (segs i) k).finish : ℝ) * h i) l (𝓝 σ) ∧
      Tendsto (fun i => nativeSegmentEndpoint (fun j => (j : ℝ) * h i)
        (nativeSegmentAt (segs i) k) - f (((nativeSegmentAt (segs i) k).finish : ℝ) * h i))
        l (𝓝 ((-1 : ℝ) ^ k * η)) := by
    intro k
    induction k with
    | zero => simpa only [pow_zero, one_mul] using And.intro hfirst ⟨hfirstTime, hfirstOffset⟩
    | succ k ih =>
      have hk := eventually_native_next_index f hH hchain hhorizon k ih.1 ih.2.1
      let next : ι → NativeSegment := fun i => nativeSegmentAt (segs i) (k + 1)
      have hjunction : ∀ᶠ i in l,
          (next i).start = (nativeSegmentAt (segs i) k).finish ∧
          (next i).anchorValue = nativeSegmentEndpoint (fun j => (j : ℝ) * h i)
            (nativeSegmentAt (segs i) k) := by
        filter_upwards [hchain, hk] with i hc hi
        simp only [next, nativeSegmentAt_eq_getElem hi,
          nativeSegmentAt_eq_getElem (show k < (segs i).length by omega)]
        exact hc.getElem_succ hi
      have hs : Tendsto (fun i => ((next i).start : ℝ) * h i) l (𝓝 σ) := by
        apply ih.2.1.congr'
        exact hjunction.mono (fun i hi => by dsimp only; rw [hi.1])
      have hqoff : Tendsto (fun i => (next i).anchorValue - f (((next i).start : ℝ) * h i))
          l (𝓝 ((-1 : ℝ) ^ k * η)) := by
        apply ih.2.2.congr'
        exact hjunction.mono (fun i hi => by dsimp only; rw [hi.1, hi.2])
      have hq : Tendsto (fun i => (next i).anchorValue) l (𝓝 ((-1 : ℝ) ^ k * η + f σ)) := by
        have ht := hqoff.add ((f.continuous.tendsto σ).comp hs)
        simpa only [Function.comp_def, sub_add_cancel] using ht
      have hvalid : ∀ᶠ i in l, NativeSegmentValid (fun j => (j : ℝ) * h i)
          (fun j => f ((j : ℝ) * h i)) ε (next i) := by
        filter_upwards [hchain, hk] with i hc hi
        rw [show next i = (segs i)[k + 1] from nativeSegmentAt_eq_getElem hi]
        exact hc.getElem_valid hi
      have hboundary : |f σ - ((-1 : ℝ) ^ k * η + f σ)| = ε := by
        rw [show f σ - ((-1 : ℝ) ^ k * η + f σ) = -((-1 : ℝ) ^ k * η) by ring, abs_neg]
        exact habs k
      have he : Tendsto (fun i => ((next i).finish : ℝ) * h i) l (𝓝 σ) :=
        tendsto_feasible_grid_finish_of_no_extension f hσ hboundary.le
          (hno _ hboundary) hh hconv hs hq
          (hvalid.mono (fun _ hv => hv.positive.le))
          (hvalid.mono (fun _ hv => ⟨_, hv.feasible⟩))
      have hk2 := eventually_native_next_index f hH hchain hhorizon (k + 1) hk he
      have hdata : ∀ᶠ i in l, (next i).start < (next i).finish ∧
          |(next i).anchorValue - f (((next i).start : ℝ) * h i)| ≤ ε ∧
          feasibleSlope (Finset.Icc ((next i).start + 1) (next i).finish)
            (fun j => (j : ℝ) * h i) (fun j => f ((j : ℝ) * h i))
            (((next i).start : ℝ) * h i) (next i).anchorValue ε (next i).slope ∧
          ¬ nativePrefixFeasible (fun j => (j : ℝ) * h i)
            (fun j => f ((j : ℝ) * h i)) ε (next i).start ((next i).finish + 1) (next i).anchorValue := by
        filter_upwards [hchain, hk2] with i hc hi
        have hk' : k + 1 < (segs i).length := by omega
        have hv := hc.getElem_valid hk'
        have hq' := hc.getElem_anchor_error
          (show |f 0 - f ((0 : ℕ) * h i)| ≤ ε by simpa using hε.le) hk'
        have hr := hc.getElem_reject hi
        simpa only [next, nativeSegmentAt_eq_getElem hk'] using
          And.intro hv.positive ⟨hq', hv.feasible, hr⟩
      have ho := tendsto_native_endpoint_opposite_boundary f hσ hε
        (eq_or_eq_neg_of_abs_eq (habs k)) hh hconv hs he hqoff hdata
      refine ⟨hk, he, ?_⟩
      have hsign : -((-1 : ℝ) ^ k * η) = (-1 : ℝ) ^ (k + 1) * η := by
        rw [pow_succ]
        ring
      rw [hsign] at ho
      exact ho
  intro k
  exact ⟨eventually_native_next_index f hH hchain hhorizon k (hmain k).1 (hmain k).2.1,
    (hmain k).2⟩

end SwingRepair
