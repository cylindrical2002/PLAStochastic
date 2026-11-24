import PLAStochastic.Index.Algorithm.SegmentLength
import PLAStochastic.ForMathlib.Probability.StoppedSum.IndepIncrements
import PLAStochastic.ForMathlib.Probability.Process.IIDRegeneration

/-!
# The iid gap model

The keys are the partial sums of a gap sequence, `gapKeys g t = g 0 + ⋯ + g (t - 1)`,
starting at `gapKeys g 0 = 0`, and `gapSegLen eps g` is the ALG-OPT segment length of
these keys.  For an iid real sequence `X` (`IIDSeq P X`) with natural filtration
`gapFiltration X _ t = σ(X 0, …, X (t - 1))` this file provides:

* shifts of an iid sequence are iid (`IIDSeq.shift`), and centred gaps have
  independent increments for the gap filtration (`IIDSeq.indepIncrements`);
* the keys `gapKeys (seq X ·) s`, `s ≤ t`, are `F t`-measurable, and the segment length
  is a stopping index for the gap filtration (`gapSegLen_lt_measurable`) and a stopping
  rule on sequence space (`isStoppingRule_gapSegLen`, `isStoppingRule_gapSegLen_fst`);
* the future `(X m, X (m + 1), …)` is independent of `F m`
  (`indep_future_gapFiltration`, `measure_future_inter_gapFiltration`);
* the keys seen from index `m` are a translate of the keys of the shifted gaps, so the
  segment starting at key `m` is the first segment of the shifted gaps
  (`gapKeys_shift`, `segLen_gapKeys_shift`);
* moments of `X t` equal those of `X 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace PGM

/-! ## Keys and segment length of a gap sequence -/

/-- The keys of a gap sequence, starting at `0`: `gapKeys g t = g 0 + ⋯ + g (t - 1)`. -/
def gapKeys (g : ℕ → ℝ) : ℕ → ℝ := fun t => ∑ s ∈ Finset.range t, g s

/-- The ALG-OPT segment length of the walk with gaps `g`. -/
noncomputable def gapSegLen (eps : ℝ) (g : ℕ → ℝ) : ℕ∞ := segLen eps (gapKeys g)

theorem gapKeys_zero (g : ℕ → ℝ) : gapKeys g 0 = 0 := by
  simp [gapKeys]

/-- The keys seen from index `m` are a translate of the keys of the shifted gaps. -/
theorem gapKeys_shift (g : ℕ → ℝ) (m i : ℕ) :
    gapKeys (fun t => g (m + t)) i = gapKeys g (m + i) - gapKeys g m := by
  simp only [gapKeys, Finset.sum_range_add]
  ring

/-- The segment starting at key `m` is the first segment of the shifted gaps. -/
theorem segLen_gapKeys_shift (eps : ℝ) (g : ℕ → ℝ) (m : ℕ) :
    segLen eps (fun i => gapKeys g (m + i)) = gapSegLen eps (fun t => g (m + t)) := by
  have h := segLen_affine (eps := eps) (p := gapKeys (fun t => g (m + t)))
    (s := 1) (c := gapKeys g m) one_ne_zero
  rw [gapSegLen, ← h]
  congr 1
  funext i
  rw [gapKeys_shift]
  ring

/-- The first `t + 1` keys only read the gaps `g 0, …, g (t - 1)`. -/
theorem gapKeys_congr {g g' : ℕ → ℝ} {t : ℕ} (h : ∀ i < t, g i = g' i) :
    ∀ s ≤ t, gapKeys g s = gapKeys g' s := by
  intro s hs
  exact Finset.sum_congr rfl fun i hi => h i (by rw [Finset.mem_range] at hi; omega)

/-! ## Stopping rules on sequence space -/

theorem measurable_gapKeys : Measurable gapKeys :=
  measurable_pi_lambda _ fun _ =>
    Finset.measurable_sum _ fun s _ => measurable_pi_apply s

/-- The segment length of the gaps is a stopping rule on real sequence space. -/
theorem isStoppingRule_gapSegLen (eps : ℝ) : IsStoppingRule (gapSegLen eps) := by
  intro t
  refine measurableSet_comap_seqPrefix_of_agree ?_ fun z z' h hz => ?_
  · have heq : {z : ℕ → ℝ | (t : ℕ∞) < gapSegLen eps z} =
        gapKeys ⁻¹' {p | prefixAffineFeasible eps p (t + 1)} := by
      ext z
      simp only [gapSegLen, Set.mem_ofPred_eq, Set.mem_preimage, lt_segLen_iff]
    rw [heq]
    exact measurable_gapKeys (measurableSet_prefixAffineFeasible eps (t + 1))
  · simp only [Set.mem_ofPred_eq, gapSegLen] at hz ⊢
    exact (lt_segLen_congr (gapKeys_congr h)).mp hz

/-- The segment length of the first components is a stopping rule on sequences of pairs. -/
theorem isStoppingRule_gapSegLen_fst (eps : ℝ) :
    IsStoppingRule (fun z : ℕ → ℝ × ℕ => gapSegLen eps (fun s => (z s).1)) := by
  intro t
  obtain ⟨S, hS, hSeq⟩ := isStoppingRule_gapSegLen eps t
  refine ⟨(fun v : Fin t → ℝ × ℕ => fun i => (v i).1) ⁻¹' S,
    (measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst) hS, ?_⟩
  ext z
  change seqPrefix t (fun s => (z s).1) ∈ S ↔
    (fun s => (z s).1) ∈ {z : ℕ → ℝ | (t : ℕ∞) < gapSegLen eps z}
  rw [← hSeq]
  rfl

/-! ## iid sequences and the gap filtration -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- An iid real sequence. -/
structure IIDSeq (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop where
  measurable : ∀ t, Measurable (X t)
  indep : iIndepFun X P
  ident : ∀ t, IdentDistrib (X t) (X 0) P P

/-- The natural filtration of the gaps: `F t = σ(X 0, …, X (t - 1))`. -/
def gapFiltration (X : ℕ → Ω → ℝ) (hX : ∀ t, Measurable (X t)) : Filtration ℕ mΩ where
  seq t := ⨆ s ∈ Set.Iio t, MeasurableSpace.comap (X s) inferInstance
  mono' := fun _ _ hst =>
    biSup_mono fun _ hs => lt_of_lt_of_le hs hst
  le' := fun _ => iSup₂_le fun s _ => (hX s).comap_le

theorem gapFiltration_apply (hX : ∀ t, Measurable (X t)) (t : ℕ) :
    gapFiltration X hX t = ⨆ s ∈ Set.Iio t, MeasurableSpace.comap (X s) inferInstance :=
  rfl

theorem gapFiltration_measurable_lt (hX : ∀ t, Measurable (X t)) {s t : ℕ} (hst : s < t) :
    Measurable[gapFiltration X hX t] (X s) :=
  (comap_measurable (X s)).mono (le_iSup₂ (f := fun s (_ : s ∈ Set.Iio t) =>
    MeasurableSpace.comap (X s) inferInstance) s hst) le_rfl

theorem measurable_gapKeys_past (hX : ∀ t, Measurable (X t)) {s t : ℕ} (hst : s ≤ t) :
    Measurable[gapFiltration X hX t] (fun ω => gapKeys (seq X ω) s) := by
  simp only [gapKeys, seq]
  exact Finset.measurable_sum _ fun r hr =>
    gapFiltration_measurable_lt hX (by rw [Finset.mem_range] at hr; omega)

/-- The segment length is a stopping index for the gap filtration. -/
theorem gapSegLen_lt_measurable (hX : ∀ t, Measurable (X t)) (eps : ℝ) (t : ℕ) :
    MeasurableSet[gapFiltration X hX t] {ω | (t : ℕ∞) < gapSegLen eps (seq X ω)} := by
  classical
  let G : Ω → ℕ → ℝ := fun ω s => if s ≤ t then gapKeys (seq X ω) s else 0
  have hG : Measurable[gapFiltration X hX t] G := by
    refine @measurable_pi_lambda _ _ _ (gapFiltration X hX t) _ G fun s => ?_
    by_cases hs : s ≤ t
    · simp only [G, hs, if_true]
      exact measurable_gapKeys_past hX hs
    · simp only [G, hs, if_false]
      exact measurable_const
  have heq : {ω | (t : ℕ∞) < gapSegLen eps (seq X ω)} =
      G ⁻¹' {p | prefixAffineFeasible eps p (t + 1)} := by
    ext ω
    simp only [gapSegLen, Set.mem_ofPred_eq, Set.mem_preimage, lt_segLen_iff]
    exact prefixAffineFeasible_congr fun i hi => by
      simp only [G, show i ≤ t by omega, if_true]
  rw [heq]
  exact hG (measurableSet_prefixAffineFeasible eps (t + 1))

namespace IIDSeq

/-- A shifted iid sequence is iid. -/
theorem shift (h : IIDSeq P X) (m : ℕ) : IIDSeq P (fun t => X (m + t)) where
  measurable t := h.measurable (m + t)
  indep := h.indep.precomp (g := fun t => m + t) fun _ _ hij => by simpa using hij
  ident t := (h.ident (m + t)).trans (h.ident m).symm

/-- Centred gaps have independent increments for the gap filtration. -/
theorem indepIncrements (h : IIDSeq P X) (c : ℝ) :
    IndepIncrements P (gapFiltration X h.measurable) (fun t ω => X t ω - c) where
  measurable t := (gapFiltration_measurable_lt h.measurable (Nat.lt_succ_self t)).sub_const c
  indep t := by
    have hd : Disjoint ({t} : Set ℕ) (Set.Iio t) := by simp
    have hind := indep_iSup_of_disjoint (fun k => (h.measurable k).comap_le) h.indep.iIndep hd
    simp only [Set.mem_singleton_iff, iSup_iSup_eq_left] at hind
    exact indep_of_indep_of_le_left hind ((comap_measurable (X t)).sub_const c).comap_le

end IIDSeq

/-! ## Independence of the future from the gap filtration -/

/-- The future `(X m, X (m + 1), …)` is independent of the gap filtration at `m`. -/
theorem indep_future_gapFiltration (h : IIDSeq P X) (m : ℕ) :
    Indep (MeasurableSpace.comap (fun ω t => X (m + t) ω) inferInstance)
      (gapFiltration X h.measurable m) P := by
  have hd : Disjoint (Set.Ici m) (Set.Iio m) := by
    apply Set.disjoint_left.mpr
    intro i h1 h2
    simp only [Set.mem_Ici, Set.mem_Iio] at h1 h2
    omega
  have hind := indep_iSup_of_disjoint (fun k => (h.measurable k).comap_le) h.indep.iIndep hd
  have h1 : MeasurableSpace.comap (fun ω (t : ℕ) => X (m + t) ω) inferInstance ≤
      ⨆ i ∈ Set.Ici m, MeasurableSpace.comap (X i) inferInstance := by
    rw [MeasurableSpace.comap_process_pi]
    exact iSup_le fun j => le_iSup_of_le (m + j) (le_iSup_of_le (by simp) le_rfl)
  exact indep_of_indep_of_le_left hind h1

/-- Event form of `indep_future_gapFiltration`. -/
theorem measure_future_inter_gapFiltration (h : IIDSeq P X) (m : ℕ)
    {A : Set (ℕ → ℝ)} (hA : MeasurableSet A)
    {B : Set Ω} (hB : MeasurableSet[gapFiltration X h.measurable m] B) :
    P ((fun ω t => X (m + t) ω) ⁻¹' A ∩ B) = P ((fun ω t => X (m + t) ω) ⁻¹' A) * P B :=
  (Indep_iff _ _ P).mp (indep_future_gapFiltration h m) _ _ ⟨A, hA, rfl⟩ hB

/-! ## Moments transfer along an iid sequence -/

namespace IIDSeq

theorem integral_eq (h : IIDSeq P X) (t : ℕ) : ∫ ω, X t ω ∂P = ∫ ω, X 0 ω ∂P :=
  (h.ident t).integral_eq

theorem integral_sq_sub_eq (h : IIDSeq P X) (t : ℕ) (c : ℝ) :
    ∫ ω, (X t ω - c) ^ 2 ∂P = ∫ ω, (X 0 ω - c) ^ 2 ∂P :=
  ((h.ident t).comp (u := fun x : ℝ => (x - c) ^ 2) (by fun_prop)).integral_eq

theorem integral_abs_sub_pow_three_eq (h : IIDSeq P X) (t : ℕ) (c : ℝ) :
    ∫ ω, |X t ω - c| ^ 3 ∂P = ∫ ω, |X 0 ω - c| ^ 3 ∂P :=
  ((h.ident t).comp (u := fun x : ℝ => |x - c| ^ 3) (by fun_prop)).integral_eq

theorem memLp_iff (h : IIDSeq P X) (t : ℕ) {p : ENNReal} :
    MemLp (X t) p P ↔ MemLp (X 0) p P :=
  (h.ident t).memLp_iff

end IIDSeq

end PGM
