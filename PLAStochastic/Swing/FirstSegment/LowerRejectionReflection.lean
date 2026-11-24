import PLAStochastic.Swing.FirstSegment.SelectedIncrementTail
import PLAStochastic.Swing.Algorithm.ConeReflection

/-! # The reflected first-rejection process is the actual lower rejection

The tail estimates of `NativeFirstSelectedTail` are proved for upper
rejections only.  This file records the pathwise identification of the
reflected native process with the genuine lower-rejection layer, so the
reflection step of Lemma G.1 is a proved equality of events rather than a
symmetry assumption.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*}

/-- Reflected increments. -/
def negIncrements (Z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun n ω => -Z n ω

@[simp] theorem negIncrements_apply (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    negIncrements Z n ω = -Z n ω := rfl

theorem cumulativeSamples_neg (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    cumulativeSamples (negIncrements Z) n ω = -cumulativeSamples Z n ω := by
  simp [cumulativeSamples, negIncrements, Finset.sum_neg_distrib]

theorem feasibleSlope_neg {ι : Type*} (samples : Finset ι) (t y : ι → ℝ)
    (t₀ y₀ ε m : ℝ) :
    feasibleSlope samples t (fun i => -y i) t₀ (-y₀) ε (-m) ↔
      feasibleSlope samples t y t₀ y₀ ε m := by
  constructor <;> intro h i hi <;> have := h i hi
  · rw [show y i - (y₀ + m*(t i - t₀)) = -(-y i - (-y₀ + -m*(t i - t₀))) by ring, abs_neg]
    exact this
  · rw [show -y i - (-y₀ + -m*(t i - t₀)) = -(y i - (y₀ + m*(t i - t₀))) by ring, abs_neg]
    exact this

theorem nativePrefixFeasible_neg (t y : ℕ → ℝ) (ε : ℝ) (s e : ℕ) (q : ℝ) :
    nativePrefixFeasible t (fun i => -y i) ε s e (-q) ↔ nativePrefixFeasible t y ε s e q := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨-m, (feasibleSlope_neg _ t y (t s) q ε (-m)).mp (by simpa using hm)⟩
  · rintro ⟨m, hm⟩
    exact ⟨-m, (feasibleSlope_neg _ t y (t s) q ε m).mpr hm⟩

/-- The actual lower endpoint of the accepted first-rejection cone. -/
def nativeFirstConeLower (Y : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  nativeConeLower (Finset.Icc 1 (n+1)) (Finset.nonempty_Icc.mpr (by omega))
    (fun j => (j : ℝ)) (fun j => Y j ω) 0 (Y 0 ω) E

/-- The genuine lower rejection threshold for the next fresh increment. -/
def nativeFirstLowerThreshold (Y : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Y 0 ω+((n+2 : ℕ) : ℝ)*nativeFirstConeLower Y E n ω-E-Y (n+1) ω

/-- Reflecting every increment turns the accepted cone upside down, exchanges the
two rejection thresholds, and preserves the feasibility flag. -/
theorem nativeFirstPrefixState_neg (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) (ω : Ω) :
    nativeFirstPrefixState (cumulativeSamples (negIncrements Z)) E n ω =
      (-nativeFirstConeLower (cumulativeSamples Z) E n ω,
        -nativeFirstLowerThreshold (cumulativeSamples Z) E n ω,
        (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.2) := by
  have hy : (fun j => cumulativeSamples (negIncrements Z) j ω) =
      (fun j => -(cumulativeSamples Z j ω)) := funext fun j => cumulativeSamples_neg Z j ω
  have hzero : cumulativeSamples (negIncrements Z) 0 ω = -(cumulativeSamples Z 0 ω) :=
    cumulativeSamples_neg Z 0 ω
  have hupper : nativeConeUpper (Finset.Icc 1 (n+1)) (Finset.nonempty_Icc.mpr (by omega))
      (fun j => (j : ℝ)) (fun j => cumulativeSamples (negIncrements Z) j ω) 0
      (cumulativeSamples (negIncrements Z) 0 ω) E =
        -nativeFirstConeLower (cumulativeSamples Z) E n ω := by
    rw [hy, hzero]
    exact nativeConeUpper_neg_eq_neg_lower _ _ _ _ 0 _ E
  have hfeas : nativePrefixFeasible (fun j => (j : ℝ))
      (fun j => cumulativeSamples (negIncrements Z) j ω) E 0 (n+1)
      (cumulativeSamples (negIncrements Z) 0 ω) ↔
        nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω) E 0 (n+1)
          (cumulativeSamples Z 0 ω) := by
    rw [hy, hzero]
    exact nativePrefixFeasible_neg _ _ E 0 (n+1) _
  dsimp only [nativeFirstPrefixState]
  refine Prod.ext hupper (Prod.ext ?_ ?_)
  · dsimp only
    rw [hupper, hzero, cumulativeSamples_neg Z (n+1) ω]
    dsimp only [nativeFirstLowerThreshold]
    ring
  · dsimp only
    by_cases hf : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω) E 0 (n+1)
        (cumulativeSamples Z 0 ω)
    · rw [if_pos (hfeas.mpr hf), if_pos hf]
    · rw [if_neg (fun h => hf (hfeas.mp h)), if_neg hf]

/-- The actual lower first-rejection layer at index `n+1`. -/
def nativeFirstLowerRejectionEvent (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) : Set Ω :=
  {ω | (nativeFirstPrefixState (cumulativeSamples Z) E n ω).2.2 = true ∧
    Z (n+1) ω < nativeFirstLowerThreshold (cumulativeSamples Z) E n ω}

/-- Pathwise equality: a lower rejection of the original path is exactly an upper
rejection of the reflected path. -/
theorem nativeFirstLowerRejectionEvent_eq_neg (Z : ℕ → Ω → ℝ) (E : ℝ) (n : ℕ) :
    nativeFirstLowerRejectionEvent Z E n = nativeFirstUpperRejectionEvent (negIncrements Z) E n := by
  ext ω
  simp only [nativeFirstLowerRejectionEvent, nativeFirstUpperRejectionEvent, mem_ofPred_eq,
    nativeFirstPrefixState_neg Z E n ω, negIncrements_apply, neg_lt_neg_iff]

/-- The actual lower rejection also records the first duration at `n+1`. -/
theorem nativeFirstLowerRejectionEvent_recording (Z : ℕ → Ω → ℝ)
    (E : ℝ) (n : ℕ) {ω : Ω} (hω : ω ∈ nativeFirstLowerRejectionEvent Z E n) :
    nativeFirstDuration Z E ω = n+1 := by
  rw [nativeFirstLowerRejectionEvent_eq_neg] at hω
  have hs := nativeFirstUpperRejectionEvent_spec (negIncrements Z) E n hω
  have hy : (fun j => cumulativeSamples (negIncrements Z) j ω) =
      (fun j => -(cumulativeSamples Z j ω)) := funext fun j => cumulativeSamples_neg Z j ω
  have hfeas : ∀ j, nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => cumulativeSamples (negIncrements Z) i ω) E 0 j 0 ↔
      nativePrefixFeasible (fun i => (i : ℝ)) (fun i => cumulativeSamples Z i ω) E 0 j 0 := by
    intro j
    rw [hy]
    simpa using nativePrefixFeasible_neg (fun i => (i : ℝ)) (fun i => cumulativeSamples Z i ω) E 0 j 0
  have hfit : nativePrefixFeasible (fun i => (i : ℝ)) (fun i => cumulativeSamples Z i ω)
      E 0 (n+1) (cumulativeSamples Z 0 ω) := by
    simpa only [cumulativeSamples_zero] using (hfeas (n+1)).mp hs.1
  have hrej : ¬ nativePrefixFeasible (fun i => (i : ℝ)) (fun i => cumulativeSamples Z i ω)
      E 0 (n+2) (cumulativeSamples Z 0 ω) := by
    simp only [cumulativeSamples_zero]
    exact fun h => hs.2.1 ((hfeas (n+2)).mpr h)
  have hthreshold : ∀ j, nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => cumulativeSamples Z i ω) E 0 j (cumulativeSamples Z 0 ω) ↔ j < n+2 := by
    intro j
    exact ⟨fun hj => by
      by_contra hnj
      exact hrej (nativePrefixFeasible_mono_end hj (by omega)),
      fun hj => nativePrefixFeasible_mono_end hfit (by omega)⟩
  simpa only [nativeFirstDuration, show n+2-1 = n+1 by omega] using
    nativeFirstRecording_eq_threshold (fun i => (i : ℝ)) (fun i => cumulativeSamples Z i ω) E
      (by omega : 1 < n+2) hthreshold

end SwingRepair
