import PLAStochastic.Swing.FrozenCarry.Interior.RangeSum

/-! # The concrete interior index range

Taking `a = ⌈E^{1+δ}⌉` and `b = ⌊E^{2-δ}⌋+1` gives a range of indices lying in
the interior window whose logarithmic width is `(1-2δ) log E` up to an absolute
constant. -/
noncomputable section
open MeasureTheory Filter Set Finset
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The lower endpoint of the interior range. -/
def frozenInteriorLow (δ E : ℝ) : ℕ := ⌈E^(1+δ)⌉₊

/-- The upper endpoint of the interior range, exclusive. -/
def frozenInteriorHigh (δ E : ℝ) : ℕ := ⌊E^(2-δ)⌋₊+1

theorem frozenInteriorLow_pos {δ E : ℝ} (hδ : 0 ≤ δ) (hE : 1 ≤ E) :
    1 ≤ frozenInteriorLow δ E := by
  have hp : (1 : ℝ) ≤ E^(1+δ) := Real.one_le_rpow hE (by linarith)
  exact Nat.one_le_ceil_iff.mpr (by linarith)

theorem frozenInteriorLow_ge (δ E : ℝ) :
    E^(1+δ) ≤ (frozenInteriorLow δ E : ℝ) := Nat.le_ceil _

theorem frozenInteriorLow_lt {δ E : ℝ} (hE : 0 ≤ E) :
    (frozenInteriorLow δ E : ℝ) < E^(1+δ)+1 := Nat.ceil_lt_add_one (by positivity)

theorem frozenInteriorHigh_gt (δ E : ℝ) :
    E^(2-δ) < (frozenInteriorHigh δ E : ℝ) := by
  have := Nat.lt_floor_add_one (E^(2-δ))
  simpa only [frozenInteriorHigh, Nat.cast_add, Nat.cast_one] using this

theorem frozenInteriorHigh_le {δ E : ℝ} (hE : 0 ≤ E) :
    (frozenInteriorHigh δ E : ℝ) ≤ E^(2-δ)+1 := by
  have := Nat.floor_le (show (0 : ℝ) ≤ E^(2-δ) by positivity)
  simpa only [frozenInteriorHigh, Nat.cast_add, Nat.cast_one] using by linarith

/-- Every index of the range lies in the interior window. -/
theorem frozenInteriorRange_mem {δ E : ℝ} (hE : 0 ≤ E) {n : ℕ}
    (hn : n ∈ Finset.Ico (frozenInteriorLow δ E) (frozenInteriorHigh δ E)) :
    frozenInteriorWindow δ E n := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hn
  constructor
  · exact le_trans (frozenInteriorLow_ge δ E) (by exact_mod_cast hlo)
  · have hhiR : (n : ℝ) < (frozenInteriorHigh δ E : ℝ) := by exact_mod_cast hhi
    have hfl : (n : ℝ) ≤ (⌊E^(2-δ)⌋₊ : ℝ) := by
      have : n ≤ ⌊E^(2-δ)⌋₊ := by
        simp only [frozenInteriorHigh] at hhi
        omega
      exact_mod_cast this
    exact hfl.trans (Nat.floor_le (by positivity))

/-- The logarithmic width of the interior range is `(1-2δ) log E` up to an
absolute constant. -/
theorem frozenInteriorRange_log_width {δ E : ℝ} (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1) (hE : 1 ≤ E) :
    |Real.log (frozenInteriorHigh δ E : ℝ)-Real.log (frozenInteriorLow δ E : ℝ)-
      (1-2*δ)*Real.log E| ≤ Real.log 2 := by
  have hEpos : (0 : ℝ) < E := by linarith
  have hlow1 : (1 : ℝ) ≤ E^(1+δ) := Real.one_le_rpow hE (by linarith)
  have hhigh1 : (1 : ℝ) ≤ E^(2-δ) := Real.one_le_rpow hE (by linarith)
  have hlogp : Real.log (E^(1+δ)) = (1+δ)*Real.log E := Real.log_rpow hEpos _
  have hlogq : Real.log (E^(2-δ)) = (2-δ)*Real.log E := Real.log_rpow hEpos _
  -- lower endpoint
  have haL : (1+δ)*Real.log E ≤ Real.log (frozenInteriorLow δ E : ℝ) := by
    rw [← hlogp]
    exact Real.log_le_log (by linarith) (frozenInteriorLow_ge δ E)
  have haU : Real.log (frozenInteriorLow δ E : ℝ) ≤ Real.log 2+(1+δ)*Real.log E := by
    have hb : (frozenInteriorLow δ E : ℝ) ≤ 2*E^(1+δ) := by
      have := (frozenInteriorLow_lt (E := E) (δ := δ) (by linarith)).le
      linarith
    have := Real.log_le_log (by
      have : (0 : ℝ) < (frozenInteriorLow δ E : ℝ) := by
        have h1 := frozenInteriorLow_pos hδ hE
        exact_mod_cast h1
      exact this) hb
    rwa [Real.log_mul (by norm_num) (by linarith), hlogp] at this
  -- upper endpoint
  have hbL : (2-δ)*Real.log E ≤ Real.log (frozenInteriorHigh δ E : ℝ) := by
    rw [← hlogq]
    exact Real.log_le_log (by linarith) (frozenInteriorHigh_gt δ E).le
  have hbU : Real.log (frozenInteriorHigh δ E : ℝ) ≤ Real.log 2+(2-δ)*Real.log E := by
    have hb : (frozenInteriorHigh δ E : ℝ) ≤ 2*E^(2-δ) := by
      have := frozenInteriorHigh_le (E := E) (δ := δ) (by linarith)
      linarith
    have := Real.log_le_log (by
      have : (0 : ℝ) < (frozenInteriorHigh δ E : ℝ) := by
        have : (0 : ℝ) < E^(2-δ) := by linarith
        linarith [frozenInteriorHigh_gt δ E]
      exact this) hb
    rwa [Real.log_mul (by norm_num) (by linarith), hlogq] at this
  rw [abs_le]
  constructor <;> linarith

end SwingRepair
