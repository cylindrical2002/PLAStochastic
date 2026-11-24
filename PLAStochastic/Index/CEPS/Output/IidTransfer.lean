import PLAStochastic.Index.GEP.OrbitClosure.OrbitMoments
import PLAStochastic.Index.GEP.OrbitClosure.CyclicReduction

/-!
# Track O: events of finitely many iid gaps

The first `n` coordinates of the canonical iid sequence have the product law
(`iidLaw_map_fin`), so events of `n` gaps can be evaluated on `iidLaw` (`pi_eq_iidLaw`).
Two such events control the stopping time `T = n`:

* the **window event** `windowEvent eps n a w` (the gaps `a, …, a+w-1` have `ε`-feasible keys)
  contains `{T = n}` whenever `a + w + 1 ≤ n` (`stopsAt_mem_windowEvent`), depends only on
  the window coordinates (`windowEvent_congr`), and has probability at most
  `(72/71) e^{-λ w/ε²}` (`pi_windowEvent_le`: shift invariance and `gapSegLen_tail`);
* the **walk event** `walkEvent x n` (`max_{j ≤ n} |S_j - j| > x`) contains `{T = n}` for
  `x = ε` (`stopsAt_mem_walkEvent`: otherwise the line of slope one fits) and has probability
  at most `2 e^{-c min(x²/n, x)}` (`pi_walkEvent_le`, from `iid_maximal_bernstein`).

These are the long and short stopping tails of `output-closure.md` (O9) and `smoothing.md`
(S7) for the uninserted coordinates.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

namespace PGM

/-- The first `n` coordinates of the canonical iid sequence have the product law. -/
theorem iidLaw_map_fin (ν : ProbabilityMeasure ℝ) (n : ℕ) :
    (iidLaw ν).map (fun g (i : Fin n) => g i) = Measure.pi fun _ => (ν : Measure ℝ) := by
  have hX := iidSeq_gapCoord ν
  have hmarg : ∀ m, (iidLaw ν).map (gapCoord m) = (ν : Measure ℝ) := fun m =>
    Measure.infinitePi_map_eval _ m
  have e2 := (hX.indep.precomp (g := fun i : Fin n => (i : ℕ)) Fin.val_injective).map_fun_eq_pi_map
    (fun i => (hX.measurable _).aemeasurable)
  simp only [hmarg] at e2
  exact e2

theorem pi_eq_iidLaw (ν : ProbabilityMeasure ℝ) {n : ℕ} {E : Set (Fin n → ℝ)}
    (hE : MeasurableSet E) :
    Measure.pi (fun _ => (ν : Measure ℝ)) E = iidLaw ν {g | (fun i : Fin n => g i) ∈ E} := by
  rw [← iidLaw_map_fin ν n, Measure.map_apply
    (measurable_pi_lambda _ fun i => measurable_pi_apply _) hE]
  rfl

theorem measurable_vext_apply {n : ℕ} (q : ℕ) : Measurable fun z : Fin n → ℝ => vext z q := by
  by_cases hq : q < n
  · simp only [vext, hq, dif_pos]
    exact measurable_pi_apply _
  · simp only [vext, hq, dif_neg, not_false_eq_true]
    exact measurable_const

/-! ## The window event -/

/-- The gaps `a, …, a + w - 1` have `ε`-feasible keys. -/
def windowEvent (eps : ℝ) (n a w : ℕ) : Set (Fin n → ℝ) :=
  {z | prefixAffineFeasible eps (gapKeys fun t => vext z (a + t)) (w + 1)}

variable {eps : ℝ}

theorem measurableSet_windowEvent (n a w : ℕ) : MeasurableSet (windowEvent eps n a w) := by
  have hm : Measurable fun z : Fin n → ℝ => gapKeys fun t => vext z (a + t) :=
    measurable_gapKeys.comp (measurable_pi_lambda _ fun t => measurable_vext_apply (a + t))
  exact hm (measurableSet_prefixAffineFeasible eps (w + 1))

theorem windowEvent_congr {n a w : ℕ} {z z' : Fin n → ℝ}
    (h : ∀ l : Fin n, a ≤ (l : ℕ) → (l : ℕ) < a + w → z l = z' l) :
    z ∈ windowEvent eps n a w ↔ z' ∈ windowEvent eps n a w := by
  simp only [windowEvent, mem_ofPred_eq]
  refine prefixAffineFeasible_congr fun i hi => ?_
  refine gapKeys_congr (t := w) (fun t ht => ?_) i (by omega)
  simp only [vext]
  by_cases hq : a + t < n
  · rw [dif_pos hq, dif_pos hq]
    exact h ⟨a + t, hq⟩ (by simp) (by simp; omega)
  · rw [dif_neg hq, dif_neg hq]

theorem stopsAt_mem_windowEvent {n a w : ℕ} {z : Fin n → ℝ} (hz : stopsAt eps z)
    (h : a + w + 1 ≤ n) : z ∈ windowEvent eps n a w := by
  have hwin := prefixAffineFeasible_window hz.1 (r := a) (w := w + 1) (by omega)
  have hkeys : (fun i => vkeys z (a + i)) = fun i => 1 * gapKeys (fun t => vext z (a + t)) i +
      gapKeys (vext z) a := by
    funext i
    rw [gapKeys_shift, vkeys]
    ring
  rw [hkeys, prefixAffineFeasible_affine_iff one_ne_zero] at hwin
  exact hwin

/-- **Long stopping tail of a window**. -/
theorem pi_windowEvent_le {b β vmin : ℝ} (hvmin0 : 0 < vmin) (heps : epsZero b β ≤ eps)
    {ν : ProbabilityMeasure ℝ} (hν : MomClass b β vmin ν) {n a w : ℕ} (h : a + w ≤ n) :
    Measure.pi (fun _ => (ν : Measure ℝ)) (windowEvent eps n a w) ≤
      ENNReal.ofReal (72 / 71 * Real.exp (-(tailRate * vmin) * w / eps ^ 2)) := by
  rw [pi_eq_iidLaw ν (measurableSet_windowEvent n a w)]
  have hset : {g : ℕ → ℝ | (fun i : Fin n => g i) ∈ windowEvent eps n a w} =
      (fun (g : ℕ → ℝ) (i : ℕ) => g (a + i)) ⁻¹' {g | (w : ℕ∞) < gapSegLen eps g} := by
    ext g
    simp only [windowEvent, mem_ofPred_eq, Set.mem_preimage, gapSegLen, lt_segLen_iff]
    refine prefixAffineFeasible_congr fun i hi => ?_
    refine gapKeys_congr (t := w) (fun t ht => ?_) i (by omega)
    simp only [vext, show a + t < n by omega, dif_pos]
  have hsh : Measurable fun (g : ℕ → ℝ) (i : ℕ) => g (a + i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hT : MeasurableSet {g : ℕ → ℝ | (w : ℕ∞) < gapSegLen eps g} := by
    obtain ⟨E', hE', hiff⟩ := exists_prefix_set_lt_gapSegLen eps w
    have : {g : ℕ → ℝ | (w : ℕ∞) < gapSegLen eps g} =
        (fun g : ℕ → ℝ => fun i : Fin w => g i) ⁻¹' E' := by
      ext g; exact hiff g
    rw [this]
    exact (measurable_pi_lambda _ fun i => measurable_pi_apply _) hE'
  rw [hset, ← Measure.map_apply hsh hT, map_shift_iidLaw]
  exact gapSegLen_tail hvmin0 heps hν w

/-! ## The walk event -/

/-- `max_{j ≤ n} |S_j - j| > x` for the keys of `n` gaps. -/
def walkEvent (x : ℝ) (n : ℕ) : Set (Fin n → ℝ) := {z | ∃ j ≤ n, x < |vkeys z j - j|}

theorem measurableSet_walkEvent (x : ℝ) (n : ℕ) : MeasurableSet (walkEvent x n) := by
  have : walkEvent x n = ⋃ j : ℕ, ⋃ (_ : j ≤ n), {z : Fin n → ℝ | x < |vkeys z j - j|} := by
    ext z
    simp [walkEvent]
  rw [this]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
    measurableSet_lt measurable_const
      (continuous_abs.measurable.comp ((measurable_vkeys_apply n j).sub_const _))

/-- A stop at `n` means that the line of slope one does not fit the first `n + 1` keys. -/
theorem stopsAt_mem_walkEvent {n : ℕ} {z : Fin n → ℝ} (hz : stopsAt eps z) :
    z ∈ walkEvent eps n := by
  by_contra h
  simp only [walkEvent, mem_ofPred_eq, not_exists, not_and, not_lt] at h
  refine hz.2 ⟨1, 0, fun i hi => ?_⟩
  have := h i (by omega)
  rw [one_mul, add_zero, abs_sub_comm]
  exact this

/-- **Short stopping tail**: the maximal Bernstein bound for the walk event. -/
theorem pi_walkEvent_le {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) {ν : ProbabilityMeasure ℝ}
    (hpos : (ν : Measure ℝ) (Iic 0) = 0) (hmean : lawMean ν = 1) (hexp : ExpMom θ₁ B₁ ν)
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    Measure.pi (fun _ => (ν : Measure ℝ)) (walkEvent x n) ≤
      ENNReal.ofReal (2 * Real.exp (-(bernsteinRate θ₁ B₁ * min (x ^ 2 / n) x))) := by
  rw [pi_eq_iidLaw ν (measurableSet_walkEvent x n)]
  have hset : {g : ℕ → ℝ | (fun i : Fin n => g i) ∈ walkEvent x n} =
      {g | ∃ j ≤ n, x < |gapKeys g j - j|} := by
    ext g
    simp only [walkEvent, mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj, hjx⟩
      exact ⟨j, hj, by rwa [vkeys_eq_gapKeys g hj] at hjx⟩
    · rintro ⟨j, hj, hjx⟩
      exact ⟨j, hj, by rwa [vkeys_eq_gapKeys g hj]⟩
  rw [hset, ← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (iid_maximal_bernstein hθ₁ hpos hmean hexp n hn hx)

end PGM
