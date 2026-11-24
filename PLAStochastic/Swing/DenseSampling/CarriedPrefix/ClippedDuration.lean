import PLAStochastic.Swing.DenseSampling.CarriedPrefix.BoundaryLowerBound
import PLAStochastic.Swing.DenseSampling.PostFirst.DurationsAndMaxima

/-! # The actual feasible carried-prefix duration, clipped at a fixed cutoff -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- Removing later observations preserves carried feasibility. -/
theorem nativeCarriedFit_mono {D : ℕ → ℝ} {w ε h : ℝ} {n N : ℕ}
    (hfit : nativeCarriedFit D w ε h N) (hn : n ≤ N) : nativeCarriedFit D w ε h n := by
  obtain ⟨m, hm⟩ := hfit
  exact ⟨m, fun j hj => hm j (hj.trans hn)⟩

theorem nativeCarriedFit_iff_exists_bounded (D : ℕ → ℝ) (w ε h : ℝ) (N : ℕ) :
    nativeCarriedFit D w ε h N ↔ ∃ n : ℕ, nativeBoundedCarriedFit D w ε n h N := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨n, hn⟩ := exists_nat_ge |m|
    exact ⟨n, m, hn, by simpa only [mul_assoc] using hm⟩
  · rintro ⟨n, m, _, hm⟩
    exact ⟨m, by simpa only [mul_assoc] using hm⟩

theorem measurableSet_nativeCarriedFit {Ω : Type*} [MeasurableSpace Ω]
    (D : ℕ → Ω → ℝ) {W : Ω → ℝ} (hW : Measurable W) (hD : ∀ j, Measurable (D j))
    (ε : ℝ) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    MeasurableSet {ω | nativeCarriedFit (fun j => D j ω) (W ω) ε h N} := by
  have heq : {ω | nativeCarriedFit (fun j => D j ω) (W ω) ε h N} =
      ⋃ n : ℕ, {ω | nativeBoundedCarriedFit (fun j => D j ω) (W ω) ε n h N} := by
    ext ω
    simp only [mem_iUnion, mem_ofPred_eq, nativeCarriedFit_iff_exists_bounded]
  rw [heq]
  exact MeasurableSet.iUnion (fun n => measurableSet_nativeBoundedCarriedFit D hW hD ε n hh N)

/-- Maximum duration of an actually feasible prefix among finitely many
observations. The carried observation has anchor-relative age h. -/
def nativeCarriedFiniteDuration (D : ℕ → ℝ) (w ε h : ℝ) (K : ℕ) : ℝ :=
  (Finset.range (K+1)).sup' (by simp)
    (fun j => if nativeCarriedFit D w ε h j then ((j : ℝ)+1)*h else 0)

def nativeCarriedTruncatedDuration (D : ℕ → ℝ) (w ε : ℝ) (h H : ℝ≥0) : ℝ :=
  min (H : ℝ) (nativeCarriedFiniteDuration D w ε h (⌈H/h⌉₊+1))

theorem nativeCarriedFiniteDuration_nonneg (D : ℕ → ℝ) (w ε : ℝ) {h : ℝ}
    (hh : 0 ≤ h) (K : ℕ) : 0 ≤ nativeCarriedFiniteDuration D w ε h K := by
  have hm := Finset.le_sup' (s := Finset.range (K+1))
    (f := fun j => if nativeCarriedFit D w ε h j then ((j : ℝ)+1)*h else 0)
    (by simp : 0 ∈ Finset.range (K+1))
  apply le_trans _ hm
  split_ifs <;> positivity

theorem nativeCarriedTruncatedDuration_bounds (D : ℕ → ℝ) (w ε : ℝ) (h H : ℝ≥0) :
    0 ≤ nativeCarriedTruncatedDuration D w ε h H ∧ nativeCarriedTruncatedDuration D w ε h H ≤ H :=
  ⟨le_min H.coe_nonneg (nativeCarriedFiniteDuration_nonneg D w ε h.coe_nonneg _), min_le_left _ _⟩

theorem le_nativeCarriedFiniteDuration_of_fit {D : ℕ → ℝ} {w ε h : ℝ} {j K : ℕ}
    (hj : j ≤ K) (hf : nativeCarriedFit D w ε h j) :
    ((j : ℝ)+1)*h ≤ nativeCarriedFiniteDuration D w ε h K := by
  have hm := Finset.le_sup' (s := Finset.range (K+1))
    (f := fun j => if nativeCarriedFit D w ε h j then ((j : ℝ)+1)*h else 0)
    (Finset.mem_range.mpr (show j < K+1 by omega))
  simpa only [if_pos hf, nativeCarriedFiniteDuration] using hm

theorem measurable_nativeCarriedFiniteDuration {Ω : Type*} [MeasurableSpace Ω]
    (D : ℕ → Ω → ℝ) {W : Ω → ℝ} (hW : Measurable W) (hD : ∀ j, Measurable (D j))
    (ε : ℝ) {h : ℝ} (hh : 0 < h) (K : ℕ) :
    Measurable (fun ω => nativeCarriedFiniteDuration (fun j => D j ω) (W ω) ε h K) := by
  have hm : Measurable ((Finset.range (K+1)).sup' (by simp)
      (fun j (ω : Ω) => if nativeCarriedFit (fun j => D j ω) (W ω) ε h j
        then ((j : ℝ)+1)*h else 0)) :=
    Finset.measurable_sup' (by simp) (fun j _ => measurable_const.ite
      (measurableSet_nativeCarriedFit D hW hD ε hh j) measurable_const)
  convert hm using 1
  ext ω
  simp only [nativeCarriedFiniteDuration, Finset.sup'_apply]

theorem aemeasurable_nativeCarriedTruncatedDuration_brownian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) {W : Ω → ℝ}
    (hW : AEMeasurable W μ) (ε : ℝ) {h : ℝ≥0} (hh : 0 < h) (H : ℝ≥0) :
    AEMeasurable (fun ω => nativeCarriedTruncatedDuration (fun j => B ((j : ℝ≥0)*h) ω)
      (W ω) ε h H) μ := by
  have hm := measurable_nativeCarriedFiniteDuration
    (fun j (p : ℝ × (ℕ → ℝ)) => p.2 j) measurable_fst
    (fun j => (measurable_pi_apply j).comp measurable_snd) ε (by exact_mod_cast hh) (⌈H/h⌉₊+1)
  have hc := ((measurable_const (a := (H : ℝ))).min hm).comp_aemeasurable
    (hW.prodMk (aemeasurable_pi_lambda _ (fun j => hB.aemeasurable ((j : ℝ≥0)*h))))
  convert hc using 1
  ext ω
  rfl

/-- Every target below the cutoff can be witnessed by the actual finite grid
used in the carried-fit lower estimate. -/
theorem le_nativeCarriedTruncatedDuration_of_fit {D : ℕ → ℝ} {w ε : ℝ}
    {h H T : ℝ≥0} (hh : 0 < h) (hTH : T ≤ H)
    (hf : nativeCarriedFit D w ε h (⌊T/h⌋₊+1)) :
    (T : ℝ) ≤ nativeCarriedTruncatedDuration D w ε h H := by
  apply le_min (by exact_mod_cast hTH)
  have hK : ⌊T/h⌋₊+1 ≤ ⌈H/h⌉₊+1 := Nat.add_le_add_right
    ((Nat.floor_le_ceil (T/h)).trans (Nat.ceil_mono (div_le_div_of_nonneg_right hTH (show (0 : ℝ≥0) ≤ h from bot_le)))) 1
  apply le_trans _ (le_nativeCarriedFiniteDuration_of_fit hK hf)
  have hfloor := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (T/h))
  have hfloor' : (T : ℝ) < ((⌊T/h⌋₊ : ℝ)+1)*(h : ℝ) := by exact_mod_cast hfloor
  push_cast
  nlinarith [h.coe_nonneg]

theorem measureReal_nativeCarriedTruncatedDuration_tail_lower {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {h H T : ℝ≥0} (hh : 0 < h) (hT : 0 < T) (hTs : (T : ℝ) ≤ 1/32) (hTH : T ≤ H)
    {w M : ℝ} (hM : 0 ≤ M) (hw : -M*(h : ℝ) ≤ w)
    (hMh : 2*M*(h : ℝ) ≤ Real.sqrt (h : ℝ)) (hMt : M*(T : ℝ) ≤ 1)
    (hdt : 8*(max w 0+Real.sqrt (h : ℝ)) ≤ (T : ℝ)) :
    (Real.exp (-1)*((max w 0+Real.sqrt (h : ℝ))/(2*(T : ℝ)))) *
      gaussianFirstPositivePass.toReal ≤
      μ.real {ω | (T : ℝ) ≤ nativeCarriedTruncatedDuration
        (fun j => B ((j : ℝ≥0)*h) ω) w 1 h H} := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hN : (⌊T/h⌋₊ : ℝ≥0)*h ≤ T := (le_div_iff₀ hh).mp (Nat.floor_le (by positivity))
  apply (measureReal_nativeCarriedFit_lower hB hh hT hTs hM hw hMh hMt hdt _ hN).trans
  apply measureReal_mono (μ := μ)
  intro ω hω
  exact le_nativeCarriedTruncatedDuration_of_fit hh hTH hω

end SwingRepair
