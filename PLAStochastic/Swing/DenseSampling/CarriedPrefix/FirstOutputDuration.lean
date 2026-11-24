import PLAStochastic.Swing.DenseSampling.CarriedPrefix.ClippedDuration

/-! # Carried feasibility determines the actual first output duration -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- Anchor at zero; the carried observation is the first sample after it. -/
def nativeCarriedFitSamples (D : ℕ → ℝ) (w ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | j+1 => w+D j-ε

theorem nativeCarriedFit_iff_nativePrefix (D : ℕ → ℝ) (w ε h : ℝ) (N : ℕ) :
    nativeCarriedFit D w ε h N ↔ nativePrefixFeasible (fun j => (j : ℝ)*h)
      (nativeCarriedFitSamples D w ε) ε 0 (N+1) 0 := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by
      have := (Finset.mem_Icc.mp hj).1; omega)
    have hb := hm j (by have := (Finset.mem_Icc.mp hj).2; omega)
    dsimp only [nativeCarriedFitSamples]
    push_cast
    rw [abs_le]
    constructor <;> nlinarith [hb.1, hb.2]
  · rintro ⟨m, hm⟩
    refine ⟨m, fun j hj => ?_⟩
    have hb := hm (j+1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    dsimp only [nativeCarriedFitSamples] at hb
    push_cast at hb
    have hlo := (abs_le.mp hb).1
    have hup := (abs_le.mp hb).2
    constructor <;> nlinarith

/-- Any selector that accepts the maximal feasible prefix has this same
finite duration. Only acceptance and rejection enter this interface. -/
theorem nativeCarriedFiniteDuration_eq_of_maximal {D : ℕ → ℝ} {w ε h : ℝ}
    (hh : 0 ≤ h) {e K : ℕ} (he : 1 ≤ e) (heK : e ≤ K+1)
    (hfit : nativeCarriedFit D w ε h (e-1))
    (hrej : e < K+1 → ¬ nativeCarriedFit D w ε h e) :
    nativeCarriedFiniteDuration D w ε h K = (e : ℝ)*h := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro j hj
    by_cases hf : nativeCarriedFit D w ε h j
    · rw [if_pos hf]
      have hje : j+1 ≤ e := by
        by_contra hn
        have hej : e ≤ j := by omega
        have hjK : j ≤ K := by have := Finset.mem_range.mp hj; omega
        exact hrej (by omega) (nativeCarriedFit_mono hf hej)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hje) hh
    · rw [if_neg hf]
      positivity
  · have hl := le_nativeCarriedFiniteDuration_of_fit (show e-1 ≤ K by omega) hfit
    have heq : ((e-1 : ℕ) : ℝ)+1 = (e : ℝ) := by
      rw [Nat.cast_sub he, Nat.cast_one]
      ring
    simpa only [heq] using hl

/-- The actual native output satisfies the selector-independent maximality
interface, so the finite carried duration is its true first segment length. -/
theorem nativeCarriedFiniteDuration_eq_nativeStream_first (D : ℕ → ℝ) (w : ℝ)
    {ε h : ℝ} (hε : 0 ≤ ε) (hh : 0 < h) (K : ℕ) :
    nativeCarriedFiniteDuration D w ε h K =
      ((nativeSegmentAt (nativeStream (fun j => (j : ℝ)*h) (nativeCarriedFitSamples D w ε)
        ε (K+1)) 0).finish : ℝ)*h := by
  let t (j : ℕ) := (j : ℝ)*h
  let y := nativeCarriedFitSamples D w ε
  let segs := nativeStream t y ε (K+1)
  have hc : NativeChain t y ε 0 (y 0) (K+1) segs :=
    nativeStream_spec t y (strictMono_mesh_times hh) hε (K+1)
  have hpos : 0 < segs.length := by
    by_contra hn
    have heq : segs = [] := List.length_eq_zero_iff.mp (by omega)
    rw [heq] at hc
    have he := hc.finish_eq_start_of_nil
    omega
  have hstart := hc.getElem_zero hpos
  have hbounds := hc.getElem_bounds hpos
  let e := segs[0].finish
  have he : 1 ≤ e := by
    have hposE : 0 < e := by
      change 0 < segs[0].finish
      simpa only [hstart.1] using hbounds.2.2
    omega
  have heK : e ≤ K+1 := hbounds.2.1
  have hfit : nativeCarriedFit D w ε h (e-1) := by
    apply (nativeCarriedFit_iff_nativePrefix D w ε h (e-1)).mpr
    have hf := (hc.getElem_valid hpos).feasible
    rw [hstart.1, hstart.2] at hf
    refine ⟨segs[0].slope, ?_⟩
    simpa only [Nat.sub_add_cancel he, y, nativeCarriedFitSamples, t, e] using hf
  have hrej : e < K+1 → ¬ nativeCarriedFit D w ε h e := by
    intro heLt hf
    have hlen : 0+1 < segs.length := by
      by_contra hn
      have heq := hc.getElem_last_finish hpos (by omega)
      have : e = K+1 := heq
      omega
    have hr := hc.getElem_reject hlen
    rw [hstart.1, hstart.2] at hr
    exact hr ((nativeCarriedFit_iff_nativePrefix D w ε h e).mp hf)
  have hout := nativeCarriedFiniteDuration_eq_of_maximal hh.le he heK hfit hrej
  rw [nativeSegmentAt_eq_getElem hpos]
  exact hout

/-- The actual native first output length, clipped at H, after inserting the
already observed carry as the first sample. -/
def nativeCarriedNativeDuration (D : ℕ → ℝ) (w ε : ℝ) (h H : ℝ≥0) : ℝ :=
  min (H : ℝ) (((nativeSegmentAt (nativeStream (fun j => (j : ℝ)*(h : ℝ))
    (nativeCarriedFitSamples D w ε) ε ((⌈H/h⌉₊+1)+1)) 0).finish : ℝ)*(h : ℝ))

theorem nativeCarriedTruncatedDuration_eq_native (D : ℕ → ℝ) (w : ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) {h : ℝ≥0} (hh : 0 < h) (H : ℝ≥0) :
    nativeCarriedTruncatedDuration D w ε h H = nativeCarriedNativeDuration D w ε h H := by
  unfold nativeCarriedTruncatedDuration nativeCarriedNativeDuration
  rw [nativeCarriedFiniteDuration_eq_nativeStream_first D w hε (by exact_mod_cast hh)]

end SwingRepair
