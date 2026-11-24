import PLAStochastic.Swing.Entrance.Grid.Reflection

/-!
# Measurability of the entrance-cut objects

For a random path `Y : Ω → ℕ → ℝ` with measurable coordinates, the running endpoints, the
rescaled width, the refresh event and the frozen endpoint at each fixed index are measurable;
the adaptive cut is a measurable `ℕ∞`-valued variable; quantities evaluated at the random cut are
measurable; and the truncation event `entranceGood` is a measurable set. Applied to the
coordinate process on `ℕ → ℝ`, this makes `entranceGood` an event of the increment law.
-/

open MeasureTheory Finset

namespace SwingRepair

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → ℕ → ℝ} (hY : ∀ n, Measurable fun ω => Y ω n)
  (E : ℝ)
include hY

theorem measurable_slopeLower_path (i : ℕ) :
    Measurable fun ω => slopeLower (i : ℝ) (Y ω i) 0 (Y ω 0) E := by
  unfold slopeLower
  exact (((hY i).sub (hY 0)).sub_const E).div_const _

theorem measurable_entranceLower (n : ℕ) : Measurable fun ω => entranceLower (Y ω) E n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [entranceLower_zero]
    exact measurable_const
  · have h : (fun ω => entranceLower (Y ω) E n) = (Icc 1 n).sup' (nonempty_Icc.mpr hn)
        (fun i ω => slopeLower (i : ℝ) (Y ω i) 0 (Y ω 0) E) := by
      funext ω
      rw [entranceLower_eq_sup' (Y ω) E hn, Finset.sup'_apply]
    rw [h]
    exact Finset.measurable_sup' _ (fun i _ => measurable_slopeLower_path hY E i)

theorem measurable_entranceUpper (n : ℕ) : Measurable fun ω => entranceUpper (Y ω) E n := by
  have h : (fun ω => entranceUpper (Y ω) E n) = fun ω => -entranceLower (-Y ω) E n := by
    funext ω
    rw [entranceLower_neg, neg_neg]
  rw [h]
  exact (measurable_entranceLower (Y := fun ω => -Y ω) (fun n => (hY n).neg) E n).neg

theorem measurable_entranceWidth (n : ℕ) : Measurable fun ω => entranceWidth (Y ω) E n := by
  unfold entranceWidth
  exact measurable_const.mul
    ((measurable_entranceUpper hY E n).sub (measurable_entranceLower hY E n))

theorem measurableSet_entranceRefreshesLower (n : ℕ) :
    MeasurableSet {ω | entranceRefreshesLower (Y ω) E n} :=
  measurableSet_eq_fun (measurable_entranceLower hY E n) (measurable_slopeLower_path hY E n)

theorem measurable_entranceFrozenSlope (n : ℕ) :
    Measurable fun ω => entranceFrozenSlope (Y ω) E n := by
  unfold entranceFrozenSlope
  exact Measurable.ite (measurableSet_entranceRefreshesLower hY E n)
    (measurable_entranceUpper hY E n) (measurable_entranceLower hY E n)

theorem measurableSet_entranceCut_eq (n : ℕ) :
    MeasurableSet {ω | entranceCut (Y ω) E = n} := by
  have h : {ω | entranceCut (Y ω) E = n} = {ω | 1 ≤ n ∧
      entranceWidth (Y ω) E n ≤ entranceCutLevel E ∧
      ∀ k, 1 ≤ k → k < n → entranceCutLevel E < entranceWidth (Y ω) E k} := by
    ext ω
    exact entranceCut_eq_coe_iff (Y ω) E
  rw [h, measurableSet_setOfPred]
  refine measurable_const.and (Measurable.and ?_ (Measurable.forall fun k =>
    measurable_const.imp (measurable_const.imp ?_)))
  · exact measurableSet_setOfPred.mp
      (measurableSet_le (measurable_entranceWidth hY E n) measurable_const)
  · exact measurableSet_setOfPred.mp
      (measurableSet_lt measurable_const (measurable_entranceWidth hY E k))

theorem measurableSet_entranceCut_top : MeasurableSet {ω | entranceCut (Y ω) E = ⊤} := by
  have h : {ω | entranceCut (Y ω) E = ⊤} =
      {ω | ∀ n, 1 ≤ n → entranceCutLevel E < entranceWidth (Y ω) E n} := by
    ext ω
    exact entranceCut_eq_top_iff (Y ω) E
  rw [h, measurableSet_setOfPred]
  exact Measurable.forall fun n => measurable_const.imp (measurableSet_setOfPred.mp
    (measurableSet_lt measurable_const (measurable_entranceWidth hY E n)))

/-- The adaptive cut is a measurable `ℕ∞`-valued random variable. -/
theorem measurable_entranceCut : Measurable fun ω => entranceCut (Y ω) E := by
  apply measurable_to_countable'
  intro x
  cases x with
  | top => exact measurableSet_entranceCut_top hY E
  | coe n => exact measurableSet_entranceCut_eq hY E n

/-- A family of measurable quantities evaluated at the random cut index is measurable. -/
theorem measurable_at_entranceCut {β : Type*} [MeasurableSpace β] {g : ℕ → Ω → β}
    (hg : ∀ n, Measurable (g n)) :
    Measurable fun ω => g (entranceCut (Y ω) E).toNat ω := by
  have hN : Measurable fun ω => (entranceCut (Y ω) E).toNat :=
    Measurable.of_discrete.comp (measurable_entranceCut hY E)
  exact (measurable_from_prod_countable_left (f := fun p : Ω × ℕ => g p.2 p.1)
    (fun n => hg n)).comp (measurable_id.prodMk hN)

/-- The truncation event of the cut is measurable. -/
theorem measurableSet_entranceGood (δ M : ℝ) :
    MeasurableSet {ω | entranceGood (Y ω) E δ M} := by
  rw [measurableSet_setOfPred]
  unfold entranceGood
  refine Measurable.exists fun n => ?_
  refine (measurableSet_setOfPred.mp (measurableSet_entranceCut_eq hY E n)).and
    (measurable_const.and (measurable_const.and (Measurable.and ?_ (Measurable.and ?_ ?_))))
  · exact measurableSet_setOfPred.mp (measurableSet_le
      (measurable_const.mul (measurable_entranceFrozenSlope hY E n)).abs measurable_const)
  · exact measurableSet_setOfPred.mp
      (measurableSet_le measurable_const (measurable_entranceWidth hY E n))
  · exact measurableSet_setOfPred.mp
      (measurableSet_le (measurable_entranceWidth hY E n) measurable_const)

end

end SwingRepair
