import PLAStochastic.Swing.Algorithm.ConstrainedSSE

/-!
# Actual native feasible cones and selected recordings

The finite bounds use the full tolerance and the fitted anchor. No half-budget
repair cone is used. Feasibility of the accepted prefix entails that the actual
clipped coefficient is feasible and is its unique constrained SSE minimizer.
-/

namespace SwingRepair

noncomputable section

def nativeConeLower {ι : Type*} (samples : Finset ι) (hne : samples.Nonempty)
    (t y : ι → ℝ) (a q ε : ℝ) : ℝ :=
  samples.sup' hne (fun i => slopeLower (t i) (y i) a q ε)

def nativeConeUpper {ι : Type*} (samples : Finset ι) (hne : samples.Nonempty)
    (t y : ι → ℝ) (a q ε : ℝ) : ℝ :=
  samples.inf' hne (fun i => slopeUpper (t i) (y i) a q ε)

def nativeSelectedSlope {ι : Type*} (samples : Finset ι) (hne : samples.Nonempty)
    (t y : ι → ℝ) (a q ε : ℝ) : ℝ :=
  nativeClippedSlope (nativeConeLower samples hne t y a q ε)
    (nativeConeUpper samples hne t y a q ε) (nativeLeastSquares samples t y a q)

theorem nativeCone_mem_iff {ι : Type*} (samples : Finset ι) (hne : samples.Nonempty)
    (t y : ι → ℝ) (a q ε m : ℝ) (ht : ∀ i ∈ samples, a < t i) :
    m ∈ Set.Icc (nativeConeLower samples hne t y a q ε)
      (nativeConeUpper samples hne t y a q ε) ↔ feasibleSlope samples t y a q ε m := by
  rw [feasibleSlope_iff_bounds samples t y a q ε m ht]
  simp only [Set.mem_Icc, nativeConeLower, nativeConeUpper, Finset.sup'_le_iff,
    Finset.le_inf'_iff]
  exact ⟨fun h i hi => ⟨h.1 i hi, h.2 i hi⟩,
    fun h => ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩⟩

theorem nativeCone_nonempty_iff {ι : Type*} (samples : Finset ι) (hne : samples.Nonempty)
    (t y : ι → ℝ) (a q ε : ℝ) (ht : ∀ i ∈ samples, a < t i) :
    (∃ m, feasibleSlope samples t y a q ε m) ↔
      nativeConeLower samples hne t y a q ε ≤ nativeConeUpper samples hne t y a q ε := by
  constructor
  · rintro ⟨m, hm⟩
    have h := (nativeCone_mem_iff samples hne t y a q ε m ht).mpr hm
    exact h.1.trans h.2
  · intro h
    refine ⟨nativeConeLower samples hne t y a q ε, ?_⟩
    exact (nativeCone_mem_iff samples hne t y a q ε _ ht).mp ⟨le_rfl, h⟩

/-! Feasible selectors, including choices unrelated to SSE, always lie in the
same interval cone. This is the only selector fact used by the H.2 charging
geometry. -/
theorem feasibleSlope_mem_nativeCone {ι : Type*} (samples : Finset ι)
    (hne : samples.Nonempty) (t y : ι → ℝ) (a q ε m : ℝ)
    (ht : ∀ i ∈ samples, a < t i)
    (hm : feasibleSlope samples t y a q ε m) :
    m ∈ Set.Icc (nativeConeLower samples hne t y a q ε)
      (nativeConeUpper samples hne t y a q ε) := by
  exact (nativeCone_mem_iff samples hne t y a q ε m ht).mpr hm

theorem nativeSelectedSlope_feasible {ι : Type*} (samples : Finset ι) (hne : samples.Nonempty)
    (t y : ι → ℝ) (a q ε : ℝ) (ht : ∀ i ∈ samples, a < t i)
    (hc : ∃ m, feasibleSlope samples t y a q ε m) :
    feasibleSlope samples t y a q ε (nativeSelectedSlope samples hne t y a q ε) := by
  apply (nativeCone_mem_iff samples hne t y a q ε _ ht).mp
  exact nativeClippedSlope_mem ((nativeCone_nonempty_iff samples hne t y a q ε ht).mp hc)

theorem nativeSelectedSlope_minimal {ι : Type*} (samples : Finset ι) (hne : samples.Nonempty)
    (t y : ι → ℝ) (a q ε m : ℝ) (ht : ∀ i ∈ samples, a < t i)
    (hm : feasibleSlope samples t y a q ε m) :
    nativeSSE samples t y a q (nativeSelectedSlope samples hne t y a q ε) ≤
      nativeSSE samples t y a q m :=
  nativeSSE_clipped_minimal hne ht ((nativeCone_mem_iff samples hne t y a q ε m ht).mpr hm)

theorem nativeSelectedSlope_unique {ι : Type*} (samples : Finset ι) (hne : samples.Nonempty)
    (t y : ι → ℝ) (a q ε m : ℝ) (ht : ∀ i ∈ samples, a < t i)
    (hm : feasibleSlope samples t y a q ε m)
    (hmin : nativeSSE samples t y a q m ≤
      nativeSSE samples t y a q (nativeSelectedSlope samples hne t y a q ε)) :
    m = nativeSelectedSlope samples hne t y a q ε :=
  nativeSSE_clipped_unique hne ht ((nativeCone_mem_iff samples hne t y a q ε m ht).mpr hm)
    (le_antisymm hmin (nativeSelectedSlope_minimal samples hne t y a q ε m ht hm))

/-- At any accepted endpoint the new fitted recording retains the full-budget error bound. -/
theorem nativeSelected_recording_error {ι : Type*} (samples : Finset ι) (hne : samples.Nonempty)
    (t y : ι → ℝ) (a q ε : ℝ) (ht : ∀ i ∈ samples, a < t i)
    (hc : ∃ m, feasibleSlope samples t y a q ε m) {b : ι} (hb : b ∈ samples) :
    |q + nativeSelectedSlope samples hne t y a q ε * (t b - a) - y b| ≤ ε := by
  rw [abs_sub_comm]
  exact nativeSelectedSlope_feasible samples hne t y a q ε ht hc b hb

theorem nativeSSECross_insert {ι : Type*} [DecidableEq ι] (samples : Finset ι)
    {j : ι} (hj : j ∉ samples) (t y : ι → ℝ) (a q : ℝ) :
    nativeSSECross (insert j samples) t y a q =
      (t j - a) * (y j - q) + nativeSSECross samples t y a q := by
  simp [nativeSSECross, hj]

theorem nativeSSETimeSquare_insert {ι : Type*} [DecidableEq ι] (samples : Finset ι)
    {j : ι} (hj : j ∉ samples) (t : ι → ℝ) (a : ℝ) :
    nativeSSETimeSquare (insert j samples) t a =
      (t j - a) ^ 2 + nativeSSETimeSquare samples t a := by
  simp [nativeSSETimeSquare, hj]

end

end SwingRepair
