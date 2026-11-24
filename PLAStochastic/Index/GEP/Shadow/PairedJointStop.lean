import PLAStochastic.Index.GEP.Shadow.LocalStop
import PLAStochastic.Index.GEP.Shadow.Synchronization

/-!
# WP3: joint stopping bounds for iid active/passive pairs

`memory-route.md` §4–5 (paired-cyclic, paired-early, paired-space, and the long-window
bound of §5), in the form of the WP2 joint bounds `stopMeas_le_early`, `stopMeas_le_long`,
`stopMeas_le_spatial`, `stopMeas_le_kernel` (`PLAStochastic/Index/GEP/OrbitClosure/JointStop.lean`).

The pairs `V i = (X_i, Y_i)` are iid on an arbitrary probability space; the two coordinates of a
pair may be dependent.  The active coordinate `X` chooses the stop `T_X = actLen eps V`, and the
passive sum `A_t = ∑_{i<t} Y_i` is the mark.  The joint stopping measure is
`pStopMeas eps P V t : A ↦ P(T_X = t, A_t ∈ A)`.  The passive law `ρ` is in the WP2 moment class
with an exponential moment; the active law is arbitrary apart from positivity, its stopping tail
`P(T_X > R) ≤ At e^{-aT R/eps²}` and `E (X - Y)² ≤ δ`.  With `F n` local bounds of `A_n`,
`r = ⌊t/2⌋`, `E = eps²` and `t > 2 eps`:

* early stop (`memory-route.md` (paired-early)): a cyclic failure makes one half of the active
  walk move by `eps/6`; then the passive walk moves by `eps/12` (maximal Bernstein) or the
  residual walk `∑ (X_i - Y_i)` does (Kolmogorov).  The event lives on one half; the passive sum
  of the other half gives the density (`IIDSeqE.measure_block_inter_le`):
  `ν_t ≤ (8/t)(e^{-(c/144) E/t} + 72 t δ/E) F(r) dx`;
* long time (`memory-route.md` §5): one of sixteen predetermined active blocks of length
  `⌊t/8⌋` is feasible; its probability is the active stopping tail, not a Bernstein bound (the
  active law has no exponential moment): `ν_t ≤ (32 At/t) e^{-(aT/16) t/E} F(r) dx`;
* spatial (`memory-route.md` (paired-space)): only the passive sum enters,
  `ν_t ≤ (8/t) e^{-(c/16) Q_t(x)} F(r) dx`.

`pStopMeas_le_kernel` combines them with `min(x + y, z, w) ≤ min(x, z, w) + min(y, z, w)`,
`min(z, w) ≤ e^{-(v+w)/2}` and `min(s², q²) ≤ s q`:
`ν_t ≤ (C₁/t) F(r) e^{-γ₁(E/t + t/E + Q)} + (C₂/t) F(r) √(tδ/E) e^{-γ₂(t/E + Q)}`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## The joint stopping measure of a paired sequence -/

/-- The joint stopping measure `A ↦ P(T_X = t, ∑_{i<t} Y_i ∈ A)`. -/
def pStopMeas (eps : ℝ) (P : Measure Ω) (V : ℕ → Ω → ℝ × ℝ) (t : ℕ) : Measure ℝ :=
  (P.restrict {ω | actLen eps V ω = (t : ℕ∞)}).map fun ω => gapKeys (fun i => (V i ω).2) t

theorem measurable_actLen {V : ℕ → Ω → ℝ × ℝ} (hV : ∀ t, Measurable (V t)) (eps : ℝ) :
    Measurable (actLen eps V) :=
  (isStoppingRule_gapSegLen eps).measurable.comp
    (measurable_pi_lambda _ fun t => (hV t).fst)

theorem measurable_pasKeys {V : ℕ → Ω → ℝ × ℝ} (hV : ∀ t, Measurable (V t)) (t : ℕ) :
    Measurable fun ω => gapKeys (fun i => (V i ω).2) t :=
  Finset.measurable_sum _ fun i _ => (hV i).snd

theorem measurable_actSum {V : ℕ → Ω → ℝ × ℝ} (hV : ∀ t, Measurable (V t)) (eps : ℝ) :
    Measurable (actSum eps V) := by
  have hm : Measurable (fun p : Ω × ℕ => gapKeys (fun i => (V i p.1).2) p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pasKeys hV n
  exact hm.comp (measurable_id.prodMk
    ((Measurable.of_discrete (f := ENat.toNat)).comp (measurable_actLen hV eps)))

theorem pStopMeas_apply {V : ℕ → Ω → ℝ × ℝ} (hV : ∀ t, Measurable (V t)) (eps : ℝ) (t : ℕ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    pStopMeas eps P V t A =
      P {ω | actLen eps V ω = (t : ℕ∞) ∧ gapKeys (fun i => (V i ω).2) t ∈ A} := by
  rw [pStopMeas, Measure.map_apply (measurable_pasKeys hV t) hA,
    Measure.restrict_apply (measurable_pasKeys hV t hA)]
  congr 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  exact and_comm

/-- A stop at `t ≤ 2 eps` is impossible. -/
theorem pStopMeas_eq_zero {eps : ℝ} (heps : 0 ≤ eps) (V : ℕ → Ω → ℝ × ℝ) {t : ℕ}
    (ht : (t : ℝ) ≤ 2 * eps) : pStopMeas eps P V t = 0 := by
  have hempty : {ω : Ω | actLen eps V ω = (t : ℕ∞)} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hT
    set C := ConstantLineLengthCertificate.of_nonneg heps
    have h := constantLine_le_segLen C (gapKeys fun s => (V s ω).1)
    rw [← gapSegLen] at h
    change (C.q : ℕ∞) ≤ actLen eps V ω at h
    rw [hT] at h
    have hq : C.q ≤ t := by exact_mod_cast h
    have hq' : (C.q : ℝ) ≤ t := by exact_mod_cast hq
    linarith [C.lower]
  rw [pStopMeas, hempty, Measure.restrict_empty, Measure.map_zero]

/-- The law of the passive sum along the active tree is the sum of the joint stopping
measures. -/
theorem map_actSum_eq_sum {V : ℕ → Ω → ℝ × ℝ} (hV : ∀ t, Measurable (V t)) {eps : ℝ}
    (hfin : ∀ᵐ ω ∂P, actLen eps V ω ≠ ⊤) :
    P.map (actSum eps V) = Measure.sum (pStopMeas eps P V) := by
  ext A hA
  rw [Measure.map_apply (measurable_actSum hV eps) hA, Measure.sum_apply _ hA]
  set B : ℕ → Set Ω := fun t => {ω | actLen eps V ω = (t : ℕ∞)} with hBdef
  have hB : ∀ t, MeasurableSet (B t) := fun t =>
    measurable_actLen hV eps (measurableSet_singleton _)
  have hS : ∀ t, pStopMeas eps P V t A = P (actSum eps V ⁻¹' A ∩ B t) := by
    intro t
    rw [pStopMeas_apply hV eps t hA]
    congr 1
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, hBdef, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1⟩
      rw [actSum, h1, ENat.toNat_natCast]
      exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [actSum, h2, ENat.toNat_natCast] at h1
      exact h1
  simp_rw [hS]
  have hdisj : Pairwise (Function.onFun Disjoint fun t => actSum eps V ⁻¹' A ∩ B t) := by
    intro i j hij
    refine Set.disjoint_left.2 fun ω hi hj => hij ?_
    have := hi.2.symm.trans hj.2
    exact_mod_cast this
  rw [← measure_iUnion hdisj fun t => (measurable_actSum hV eps hA).inter (hB t)]
  refine measure_congr ?_
  filter_upwards [hfin] with ω hω
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.1 hω
  apply propext
  constructor
  · intro h
    exact Set.mem_iUnion.2 ⟨t, h, ht.symm⟩
  · intro h
    obtain ⟨_, h1, _⟩ := Set.mem_iUnion.1 h
    exact h1

/-! ## The standing hypotheses -/

/-- The hypotheses on an iid paired sequence used by the joint bounds: iid pairs, positive
active coordinates, passive law `ρ`, a centred square-integrable residual `X - Y` with
`E (X - Y)² ≤ δ`, and a finite active stop with the tail `P(T_X > R) ≤ At e^{-aT R/eps²}`.
Nothing else is assumed on the active law. -/
structure PairedHyp (P : Measure Ω) (V : ℕ → Ω → ℝ × ℝ) (ρ : ProbabilityMeasure ℝ)
    (eps At aT δ : ℝ) : Prop where
  iid : IIDSeqE P V
  pos_act : ∀ᵐ ω ∂P, ∀ i, 0 < (V i ω).1
  law_pas : P.map (fun ω => (V 0 ω).2) = (ρ : Measure ℝ)
  memLp_res : MemLp (fun ω => (V 0 ω).1 - (V 0 ω).2) 2 P
  mean_res : ∫ ω, ((V 0 ω).1 - (V 0 ω).2) ∂P = 0
  dist : ∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P ≤ δ
  fin : ∀ᵐ ω ∂P, actLen eps V ω ≠ ⊤
  tail : ∀ R : ℕ, P.real {ω | (R : ℕ∞) < actLen eps V ω} ≤ At * Real.exp (-(aT * R / eps ^ 2))

variable [IsProbabilityMeasure P] {V : ℕ → Ω → ℝ × ℝ} {ρ : ProbabilityMeasure ℝ}

omit [IsProbabilityMeasure P] in
/-- The passive coordinates form an iid real sequence. -/
theorem IIDSeqE.iidSeq_snd (hV : IIDSeqE P V) : IIDSeq P (fun i ω => (V i ω).2) :=
  ⟨fun i => (hV.measurable i).snd, hV.indep.comp (fun _ => Prod.snd) (fun _ => measurable_snd),
    fun i => (hV.ident i).comp measurable_snd⟩

omit [IsProbabilityMeasure P] in
/-- Events of the passive path have their `iidLaw ρ` probabilities. -/
theorem IIDSeqE.measure_pas_eq (hV : IIDSeqE P V)
    (hρ : P.map (fun ω => (V 0 ω).2) = (ρ : Measure ℝ)) {S : Set (ℕ → ℝ)}
    (hS : MeasurableSet S) :
    P {ω | (fun i => (V i ω).2) ∈ S} = iidLaw ρ S := by
  have hY := hV.iidSeq_snd
  have hmap := map_seq_eq_iidLaw hY ρ hρ.symm
  rw [← hmap, Measure.map_apply (measurable_seq hY.measurable) hS]
  rfl

omit [IsProbabilityMeasure P] in
theorem PairedHyp.pos_pas {eps At aT δ : ℝ} (h : PairedHyp P V ρ eps At aT δ)
    (hpos : (ρ : Measure ℝ) (Iic 0) = 0) : ∀ᵐ ω ∂P, ∀ i, 0 < (V i ω).2 := by
  have h0 : ∀ᵐ ω ∂P, 0 < (V 0 ω).2 := by
    have hm : Measurable fun ω => (V 0 ω).2 := (h.iid.measurable 0).snd
    have hae : ∀ᵐ x ∂(P.map fun ω => (V 0 ω).2), 0 < x := by
      rw [h.law_pas]
      filter_upwards [compl_mem_ae_iff.2 hpos] with x hx
      simpa using hx
    exact ae_of_ae_map hm.aemeasurable hae
  refine ae_all_iff.mpr fun i => ?_
  exact ((h.iid.ident i).comp measurable_snd).symm.ae_snd measurableSet_Ioi h0

omit [IsProbabilityMeasure P] in
/-- A stop has a positive mark: `ν_t (-∞, 0] = 0`. -/
theorem PairedHyp.pStopMeas_Iic {eps At aT δ : ℝ} (h : PairedHyp P V ρ eps At aT δ)
    (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (heps : 0 ≤ eps) (t : ℕ) :
    pStopMeas eps P V t (Iic 0) = 0 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [pStopMeas_eq_zero heps V (by simp only [Nat.cast_zero]; linarith)]
    rfl
  · rw [pStopMeas_apply h.iid.measurable eps t measurableSet_Iic]
    have hsub : {ω | actLen eps V ω = (t : ℕ∞) ∧ gapKeys (fun i => (V i ω).2) t ∈ Iic 0} ⊆
        {ω | gapKeys (fun i => (V i ω).2) t ∈ Iic 0} := fun ω hω => hω.2
    refine le_antisymm ((measure_mono hsub).trans (le_of_eq ?_)) zero_le
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h.pos_pas hpos] with ω hω
    simp only [Set.mem_Iic, not_le, gapKeys]
    exact Finset.sum_pos (fun i _ => hω i) (Finset.nonempty_range_iff.2 ht.ne')

/-! ## The residual walk: Kolmogorov -/

/-- Kolmogorov's inequality for the residual walk `∑_{i<k} (X_i - Y_i)`. -/
theorem IIDSeqE.measureReal_resid_le (hV : IIDSeqE P V)
    (hD2 : MemLp (fun ω => (V 0 ω).1 - (V 0 ω).2) 2 P)
    (hD0 : ∫ ω, ((V 0 ω).1 - (V 0 ω).2) ∂P = 0) {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    P.real {ω | ∃ k ≤ n, lam ≤ |∑ i ∈ Finset.range k, ((V i ω).1 - (V i ω).2)|} ≤
      n * (∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P) / lam ^ 2 := by
  have hf : Measurable (fun p : ℝ × ℝ => p.1 - p.2) := measurable_fst.sub measurable_snd
  set Z : ℕ → Ω → ℝ := fun t ω => (V t ω).1 - (V t ω).2 with hZdef
  have hZ := hV.indepIncrements _ hf
  have hZ2 : ∀ t, MemLp (Z t) 2 P := fun t =>
    ((hV.ident t).comp hf).memLp_iff.mpr hD2
  have hZ0 : ∀ t, ∫ ω, Z t ω ∂P = 0 := by
    intro t
    rw [show (∫ ω, Z t ω ∂P) = ∫ ω, Z 0 ω ∂P from hV.integral_comp hf t]
    exact hD0
  have hk := kolmogorov_maximal hZ hZ2 hZ0 hlam n
  have hsq : ∫ ω, partialSum Z n ω ^ 2 ∂P = n * ∫ ω, Z 0 ω ^ 2 ∂P := by
    rw [partialSum_eq_weightedSum_one, integral_weightedSum_sq hZ (PredictableWeight.one _)
      hZ2 hZ0]
    have e : ∀ t, ∫ ω, Z t ω ^ 2 ∂P = ∫ ω, Z 0 ω ^ 2 ∂P := fun t =>
      hV.integral_comp (hf.pow_const 2) t
    simp only [one_pow, integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [Finset.sum_congr rfl fun t _ => e t, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsq] at hk
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact hk

omit [IsProbabilityMeasure P] in
theorem PairedHyp.delta_nonneg {eps At aT δ : ℝ} (h : PairedHyp P V ρ eps At aT δ) : 0 ≤ δ :=
  le_trans (integral_nonneg fun _ => sq_nonneg _) h.dist

/-! ## Early stop: passive Bernstein plus residual Kolmogorov -/

omit [IsProbabilityMeasure P] in
/-- The maximal Bernstein bound for the passive walk, read on the paired space. -/
theorem IIDSeqE.measure_pasWalk_le (hV : IIDSeqE P V)
    (hρ : P.map (fun ω => (V 0 ω).2) = (ρ : Measure ℝ)) {θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁)
    (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (hmean : lawMean ρ = 1) (hexp : ExpMom θ₁ B₁ ρ)
    (s : ℕ) (hs : 1 ≤ s) {x : ℝ} (hx : 0 < x) :
    P {ω | ∃ j ≤ s, x < |gapKeys (fun i => (V i ω).2) j - j|} ≤
      ENNReal.ofReal (2 * Real.exp (-(bernsteinRate θ₁ B₁ * min (x ^ 2 / s) x))) := by
  obtain ⟨E', hE', hiff⟩ := exists_prefix_set_walk x s
  have hS : MeasurableSet {g : ℕ → ℝ | ∃ j ≤ s, x < |gapKeys g j - j|} := by
    have e : {g : ℕ → ℝ | ∃ j ≤ s, x < |gapKeys g j - j|} =
        {g | (fun i : Fin s => g i) ∈ E'} := by
      ext g; exact hiff g
    rw [e]
    exact (measurable_pi_lambda _ fun i => measurable_pi_apply _) hE'
  have e := hV.measure_pas_eq hρ hS
  change P {ω | (fun i => (V i ω).2) ∈ {g : ℕ → ℝ | ∃ j ≤ s, x < |gapKeys g j - j|}} ≤ _
  rw [e, ← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (iid_maximal_bernstein hθ₁ hpos hmean hexp s hs hx)

/-- **The paired walk bound**: a deviation `eps/6` of the active walk of length `s ≤ t` needs
a deviation `eps/12` of the passive walk or of the residual walk. -/
theorem PairedHyp.walk_le {eps At aT δ : ℝ} (h : PairedHyp P V ρ eps At aT δ)
    {b β vmin θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) (hρ : MomClass b β vmin ρ) (hexp : ExpMom θ₁ B₁ ρ)
    (hepspos : 0 < eps) {t s : ℕ} (ht : 2 * eps < t) (hs : 1 ≤ s) (hst : s ≤ t) :
    P {ω | ∃ j ≤ s, eps / 6 < |gapKeys (fun i => (V i ω).1) j - j|} ≤
      ENNReal.ofReal (2 * Real.exp (-(bernsteinRate θ₁ B₁ / 144) * (eps ^ 2 / t)) +
        144 * t * δ / eps ^ 2) := by
  set W : Set Ω := {ω | ∃ j ≤ s, eps / 12 < |gapKeys (fun i => (V i ω).2) j - j|} with hW
  set R : Set Ω := {ω | ∃ k ≤ s, eps / 12 ≤
    |∑ i ∈ Finset.range k, ((V i ω).1 - (V i ω).2)|} with hR
  have hsub : {ω | ∃ j ≤ s, eps / 6 < |gapKeys (fun i => (V i ω).1) j - j|} ⊆ W ∪ R := by
    rintro ω ⟨j, hj, hlt⟩
    by_cases hw : eps / 12 < |gapKeys (fun i => (V i ω).2) j - j|
    · exact Or.inl ⟨j, hj, hw⟩
    · refine Or.inr ⟨j, hj, ?_⟩
      have e : gapKeys (fun i => (V i ω).1) j - j = (gapKeys (fun i => (V i ω).2) j - j) +
          ∑ i ∈ Finset.range j, ((V i ω).1 - (V i ω).2) := by
        simp only [gapKeys, Finset.sum_sub_distrib]
        ring
      rw [e] at hlt
      have := abs_add_le (gapKeys (fun i => (V i ω).2) j - j)
        (∑ i ∈ Finset.range j, ((V i ω).1 - (V i ω).2))
      linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hE : 0 < eps ^ 2 := by positivity
  set c := bernsteinRate θ₁ B₁ with hc
  have hB₁ : 0 < B₁ := (integral_exp_pos hexp.integrable).trans_le hexp.le
  have hc0 : 0 < c := bernsteinRate_pos hθ₁ hB₁
  -- the passive walk
  have hPW : P W ≤ ENNReal.ofReal (2 * Real.exp (-(c / 144) * (eps ^ 2 / t))) := by
    refine (h.iid.measure_pasWalk_le h.law_pas hθ₁ hρ.pos hρ.mean hexp s hs
      (by positivity : 0 < eps / 12)).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have hmin : eps ^ 2 / (144 * t) ≤ min ((eps / 12) ^ 2 / s) (eps / 12) := by
      refine le_min ?_ ?_
      · rw [div_le_div_iff₀ (by positivity) hs0]
        nlinarith [mul_le_mul_of_nonneg_left hst' (sq_nonneg eps)]
      · rw [div_le_iff₀ (by positivity)]
        nlinarith
    have e : -(c / 144) * (eps ^ 2 / t) = -(c * (eps ^ 2 / (144 * t))) := by
      field_simp
    rw [e, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left hmin hc0.le
  -- the residual walk
  have hPR : P R ≤ ENNReal.ofReal (144 * t * δ / eps ^ 2) := by
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((h.iid.measureReal_resid_le h.memLp_res h.mean_res
      (by positivity : 0 < eps / 12) s).trans ?_)
    have hd0 : 0 ≤ ∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    have hd := h.dist
    rw [div_le_div_iff₀ (by positivity) hE]
    have h1 : (s : ℝ) * (∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P) ≤ t * δ :=
      mul_le_mul hst' hd hd0 ht0.le
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg eps)]
  calc P {ω | ∃ j ≤ s, eps / 6 < |gapKeys (fun i => (V i ω).1) j - j|}
      ≤ P (W ∪ R) := measure_mono hsub
    _ ≤ P W + P R := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(c / 144) * (eps ^ 2 / t))) +
          ENNReal.ofReal (144 * t * δ / eps ^ 2) := add_le_add hPW hPR
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by have := h.delta_nonneg; positivity)]

/-- A uniform bound on sets is a constant density bound. -/
theorem le_withDensity_const_of_le {μ : Measure ℝ} {c : ℝ}
    (h : ∀ A, MeasurableSet A → μ A ≤ ENNReal.ofReal c * volume A) :
    μ ≤ volume.withDensity fun _ => ENNReal.ofReal c := by
  rw [withDensity_const, Measure.le_iff]
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul]
  exact h A hA

/-- `2 / t` as the extended real `ofReal (2 / t)`. -/
theorem two_div_natCast_eq_ofReal {t : ℕ} (ht : 0 < t) :
    (2 : ℝ≥0∞) / (t : ℝ≥0∞) = ENNReal.ofReal (2 / t) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast ht), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_natCast]

/-- **Paired early-stop bound** (`memory-route.md` (paired-early)). -/
theorem PairedHyp.pStopMeas_le_early {eps At aT δ : ℝ} (h : PairedHyp P V ρ eps At aT δ)
    {b β vmin θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) (heps : 8 ≤ eps) (hρ : MomClass b β vmin ρ)
    (hexp : ExpMom θ₁ B₁ ρ) {F : ℕ → ℝ}
    (hF : ∀ n, 1 ≤ n → LocBd (F n) (convPow (ρ : Measure ℝ) n))
    (hFa : ∀ n m, 1 ≤ n → n ≤ m → F m ≤ F n) {t : ℕ} (ht : 2 * eps < t) :
    pStopMeas eps P V t ≤ volume.withDensity fun _ =>
      ENNReal.ofReal (8 / t * (Real.exp (-(bernsteinRate θ₁ B₁ / 144) * (eps ^ 2 / t)) +
        72 * t * δ / eps ^ 2) * F (t / 2)) := by
  classical
  have heps0 : 0 ≤ eps := by linarith
  have hepspos : 0 < eps := by linarith
  have ht' : (16 : ℝ) < t := by linarith
  have ht16 : 16 < t := by exact_mod_cast ht'
  have htpos : 0 < t := by omega
  have hδ := h.delta_nonneg
  set r := t / 2 with hr
  have hr1 : 1 ≤ r := by omega
  have hrt : r ≤ t - r := by omega
  set ee := Real.exp (-(bernsteinRate θ₁ B₁ / 144) * (eps ^ 2 / t)) with hee
  set pp := 2 * ee + 144 * t * δ / eps ^ 2 with hpp
  have hpp0 : 0 ≤ pp := by positivity
  have hFr0 : 0 ≤ F r := (hF r hr1).const_nonneg
  obtain ⟨E₁, hE₁, hE₁iff⟩ := exists_prefix_set_walk (eps / 6) r
  obtain ⟨E₂, hE₂, hE₂iff⟩ := exists_prefix_set_walk (eps / 6) (t - r)
  set E'₁ : Set (Fin r → ℝ × ℝ) := (fun v i => (v i).1) ⁻¹' E₁ with hE'₁def
  set E'₂ : Set (Fin (t - r) → ℝ × ℝ) := (fun v i => (v i).1) ⁻¹' E₂ with hE'₂def
  have hE'₁ : MeasurableSet E'₁ :=
    (measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst) hE₁
  have hE'₂ : MeasurableSet E'₂ :=
    (measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst) hE₂
  set S₁ : Set Ω := {ω | (fun i : Fin r => V (i : ℕ) ω) ∈ E'₁} with hS₁def
  set S₂ : Set Ω := {ω | (fun i : Fin (t - r) => V (r + i) ω) ∈ E'₂} with hS₂def
  have hS₁ : MeasurableSet S₁ := (measurable_pi_lambda _ fun i => h.iid.measurable _) hE'₁
  have hS₂ : MeasurableSet S₂ := (measurable_pi_lambda _ fun i => h.iid.measurable _) hE'₂
  have hP₁ : P S₁ ≤ ENNReal.ofReal pp := by
    have e : S₁ = {ω | ∃ j ≤ r, eps / 6 < |gapKeys (fun i => (V i ω).1) j - j|} := by
      ext ω
      simp only [hS₁def, hE'₁def, Set.mem_preimage, Set.mem_ofPred_eq]
      exact (hE₁iff (fun i => (V i ω).1)).symm
    rw [e]
    exact h.walk_le hθ₁ hρ hexp hepspos ht hr1 (by omega)
  have hP₂ : P S₂ ≤ ENNReal.ofReal pp := by
    rw [hS₂def, h.iid.measure_block_shift r (t - r) hE'₂]
    have e : {ω | (fun i : Fin (t - r) => V (i : ℕ) ω) ∈ E'₂} =
        {ω | ∃ j ≤ t - r, eps / 6 < |gapKeys (fun i => (V i ω).1) j - j|} := by
      ext ω
      simp only [hE'₂def, Set.mem_preimage, Set.mem_ofPred_eq]
      exact (hE₂iff (fun i => (V i ω).1)).symm
    rw [e]
    exact h.walk_le hθ₁ hρ hexp hepspos ht (by omega) (by omega)
  refine le_withDensity_const_of_le fun A hA => ?_
  have hcyc := h.iid.actLen_sum_le_cyclic h.pos_act heps0 htpos (hS₁.union hS₂)
    (fun ω _ hc => by
      rcases cyclicCount_pos_walk (r := r) (g := fun i => (V i ω).1) (by omega) hc with h1 | h2
      · exact Or.inl (show (fun i : Fin r => (V (i : ℕ) ω).1) ∈ E₁ from (hE₁iff _).1 h1)
      · exact Or.inr (show (fun i : Fin (t - r) => (V (r + i) ω).1) ∈ E₂ from
          (hE₂iff (fun i => (V (r + i) ω).1)).1 h2)) hA
  have hc₁ : LocBd (F (t - r)) (convPow (P.map fun ω => (V 0 ω).2) (t - r)) := by
    rw [h.law_pas]; exact hF (t - r) (by omega)
  have hc₂ : LocBd (F r) (convPow (P.map fun ω => (V 0 ω).2) (t - (t - r))) := by
    rw [h.law_pas, show t - (t - r) = r by omega]; exact hF r hr1
  have h₁ := h.iid.measure_block_inter_le (u := 0) (m := r) (t := t) (by omega) hE'₁ hc₁ hA
  simp only [zero_add] at h₁
  have h₂ := h.iid.measure_block_inter_le (u := r) (m := t - r) (t := t) (by omega) hE'₂ hc₂ hA
  have hFtr : ENNReal.ofReal (F (t - r)) ≤ ENNReal.ofReal (F r) :=
    ENNReal.ofReal_le_ofReal (hFa r (t - r) hr1 hrt)
  rw [pStopMeas_apply h.iid.measurable eps t hA]
  calc P {ω | actLen eps V ω = (t : ℕ∞) ∧ gapKeys (fun i => (V i ω).2) t ∈ A}
      ≤ 2 / (t : ℝ≥0∞) * P ((S₁ ∪ S₂) ∩ {ω | gapKeys (fun i => (V i ω).2) t ∈ A}) := hcyc
    _ ≤ 2 / (t : ℝ≥0∞) * (P (S₁ ∩ {ω | gapKeys (fun i => (V i ω).2) t ∈ A}) +
          P (S₂ ∩ {ω | gapKeys (fun i => (V i ω).2) t ∈ A})) := by
        rw [Set.union_inter_distrib_right]
        gcongr
        exact measure_union_le _ _
    _ ≤ 2 / (t : ℝ≥0∞) * (ENNReal.ofReal pp * (ENNReal.ofReal (F r) * volume A) +
          ENNReal.ofReal pp * (ENNReal.ofReal (F r) * volume A)) := by
        gcongr
        · exact h₁.trans (mul_le_mul' hP₁ (mul_le_mul_left hFtr _))
        · exact h₂.trans (mul_le_mul_left hP₂ _)
    _ = ENNReal.ofReal (2 / t) * ENNReal.ofReal pp * ENNReal.ofReal (F r) * 2 * volume A := by
        rw [two_div_natCast_eq_ofReal htpos]
        ring
    _ = ENNReal.ofReal (8 / t * (ee + 72 * t * δ / eps ^ 2) * F r) * volume A := by
        congr 1
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hpp]
        ring


/-! ## Long time: the active stopping tail on a predetermined block -/

/-- **Paired long-time bound** (`memory-route.md` §5): one of sixteen active blocks of length
`⌊t/8⌋` is feasible; the block event reads only active coordinates, and its probability is the
active stopping tail. -/
theorem PairedHyp.pStopMeas_le_long {eps At aT δ : ℝ} (h : PairedHyp P V ρ eps At aT δ)
    (hAt : 0 ≤ At) (haT : 0 < aT) (heps8 : 8 ≤ eps) {F : ℕ → ℝ}
    (hF : ∀ n, 1 ≤ n → LocBd (F n) (convPow (ρ : Measure ℝ) n))
    (hFa : ∀ n m, 1 ≤ n → n ≤ m → F m ≤ F n) {t : ℕ} (ht : 2 * eps < t) :
    pStopMeas eps P V t ≤ volume.withDensity fun _ =>
      ENNReal.ofReal (32 * At / t * Real.exp (-(aT / 16) * (t / eps ^ 2)) * F (t / 2)) := by
  classical
  have heps0 : 0 ≤ eps := by linarith
  have ht' : (16 : ℝ) < t := by linarith
  have ht16 : 16 < t := by exact_mod_cast ht'
  have htpos : 0 < t := by omega
  set m := t / 8 with hm
  set r := t / 2 with hr
  have hr1 : 1 ≤ r := by omega
  have hrm : r ≤ t - m := by omega
  have hFr0 : 0 ≤ F r := (hF r hr1).const_nonneg
  set PP := At * Real.exp (-(aT / 16) * (t / eps ^ 2)) with hPP
  have hPP0 : 0 ≤ PP := by positivity
  obtain ⟨E', hE', hE'iff⟩ := exists_prefix_set_lt_gapSegLen eps m
  set E'' : Set (Fin m → ℝ × ℝ) := (fun v i => (v i).1) ⁻¹' E' with hE''def
  have hE'' : MeasurableSet E'' :=
    (measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst) hE'
  set J := (Finset.range 16).filter (fun j => (j + 1) * m ≤ t) with hJ
  set S : ℕ → Set Ω := fun j => {ω | (fun i : Fin m => (V (j * m + i) ω).1) ∈ E'} with hSdef
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (measurable_pi_lambda _ fun i => (h.iid.measurable _).fst) hE'
  have hU : MeasurableSet (⋃ j ∈ J, S j) := Finset.measurableSet_biUnion J fun j _ => hSm j
  have hsub : ∀ ω : Ω, (∀ i, 0 < (V i ω).1) →
      1 ≤ cyclicCount eps (fun i : Fin t => (V i ω).1) → ω ∈ ⋃ j ∈ J, S j := by
    intro ω hω hc
    obtain ⟨j, hj16, hjt, hjT⟩ := cyclicCount_pos_block heps0 (by omega) hω hc
    exact Set.mem_iUnion₂.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj16, hjt⟩,
      (hE'iff _).1 hjT⟩
  have hPS : ∀ j, P (S j) ≤ ENNReal.ofReal PP := by
    intro j
    have e1 : S j = {ω | (fun i : Fin m => V (j * m + i) ω) ∈ E''} := rfl
    rw [e1, h.iid.measure_block_shift (j * m) m hE'']
    have e : {ω | (fun i : Fin m => V (i : ℕ) ω) ∈ E''} = {ω | (m : ℕ∞) < actLen eps V ω} := by
      ext ω
      exact (hE'iff (fun i => (V i ω).1)).symm
    rw [e, ← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((h.tail m).trans ?_)
    rw [hPP]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hAt
    have hE : 0 < eps ^ 2 := by positivity
    have h16 : (t : ℝ) ≤ 16 * m := by exact_mod_cast (show t ≤ 16 * m by omega)
    have hkey : aT / 16 * (t / eps ^ 2) ≤ aT * m / eps ^ 2 := by
      calc aT / 16 * (t / eps ^ 2) = aT * (t / 16) / eps ^ 2 := by ring
        _ ≤ aT * m / eps ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) haT.le) hE.le
    rw [neg_mul]
    exact neg_le_neg hkey
  have hc : LocBd (F (t - m)) (convPow (P.map fun ω => (V 0 ω).2) (t - m)) := by
    rw [h.law_pas]; exact hF (t - m) (by omega)
  have hblock : ∀ j ∈ J, ∀ A, MeasurableSet A →
      P (S j ∩ {ω | gapKeys (fun i => (V i ω).2) t ∈ A}) ≤
        ENNReal.ofReal PP * (ENNReal.ofReal (F r) * volume A) := by
    intro j hj A hA
    have hjt : (j + 1) * m ≤ t := (Finset.mem_filter.1 hj).2
    have hjm : j * m + m ≤ t := by rw [add_one_mul] at hjt; exact hjt
    refine (h.iid.measure_active_block_inter_le (u := j * m) (m := m) (t := t) hjm hE'
      hc hA).trans ?_
    exact mul_le_mul' (hPS j) (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (hFa r (t - m) hr1 hrm)) _)
  refine le_withDensity_const_of_le fun A hA => ?_
  have hcyc := h.iid.actLen_sum_le_cyclic h.pos_act heps0 htpos hU hsub hA
  rw [pStopMeas_apply h.iid.measurable eps t hA]
  calc P {ω | actLen eps V ω = (t : ℕ∞) ∧ gapKeys (fun i => (V i ω).2) t ∈ A}
      ≤ 2 / (t : ℝ≥0∞) * P ((⋃ j ∈ J, S j) ∩ {ω | gapKeys (fun i => (V i ω).2) t ∈ A}) :=
        hcyc
    _ ≤ 2 / (t : ℝ≥0∞) * ∑ j ∈ J, P (S j ∩ {ω | gapKeys (fun i => (V i ω).2) t ∈ A}) := by
        gcongr
        rw [Set.iUnion₂_inter]
        exact measure_biUnion_finset_le J _
    _ ≤ 2 / (t : ℝ≥0∞) * ∑ j ∈ J, ENNReal.ofReal PP * (ENNReal.ofReal (F r) * volume A) := by
        gcongr with j hj
        exact hblock j hj A hA
    _ ≤ 2 / (t : ℝ≥0∞) * (16 * (ENNReal.ofReal PP * (ENNReal.ofReal (F r) * volume A))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        have : J.card ≤ 16 := (Finset.card_filter_le _ _).trans (Finset.card_range 16).le
        exact_mod_cast this
    _ = ENNReal.ofReal (2 / t) * ENNReal.ofReal PP * ENNReal.ofReal (F r) * 16 * volume A := by
        rw [two_div_natCast_eq_ofReal htpos]
        ring
    _ = ENNReal.ofReal (32 * At / t * Real.exp (-(aT / 16) * (t / eps ^ 2)) * F r) *
          volume A := by
        congr 1
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_ofNat 16, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hPP]
        ring

/-! ## Spatial localisation of the passive sum -/

/-- The spatial bound of the passive sum (the iid part of `stopMeas_le_spatial`). -/
theorem iidLaw_gapKeys_le_spatial {b β vmin θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁)
    {ρ : ProbabilityMeasure ℝ} (hρ : MomClass b β vmin ρ) (hexp : ExpMom θ₁ B₁ ρ)
    {F : ℕ → ℝ} (hF : ∀ n, 1 ≤ n → LocBd (F n) (convPow (ρ : Measure ℝ) n))
    (hFa : ∀ n m, 1 ≤ n → n ≤ m → F m ≤ F n) {t : ℕ} (ht16 : 16 < t) {A : Set ℝ}
    (hA : MeasurableSet A) :
    iidLaw ρ {g | gapKeys g t ∈ A} ≤
      ∫⁻ x in A, ENNReal.ofReal (4 * F (t / 2) *
        Real.exp (-(bernsteinRate θ₁ B₁ / 16) * qdev t x)) := by
  have htpos : 0 < t := by omega
  have htpos' : (0 : ℝ) < t := by exact_mod_cast htpos
  set r := t / 2 with hr
  set s := t - t / 2 with hs
  have hr1 : 1 ≤ r := by omega
  have hrs : r ≤ s := by omega
  have hs1 : 1 ≤ s := by omega
  have hrst : r + s = t := by omega
  set c := bernsteinRate θ₁ B₁ with hc
  have hB₁ : 0 < B₁ := (integral_exp_pos hexp.integrable).trans_le hexp.le
  have hc0 : 0 < c := bernsteinRate_pos hθ₁ hB₁
  have hFr0 : 0 ≤ F r := (hF r hr1).const_nonneg
  have hFs : F s ≤ F r := hFa r s hr1 hrs
  have hb : ∀ n : ℕ, 1 ≤ n → n ≤ t → ∀ x : ℝ,
      (iidLaw ρ).real {g | |x - t| / 2 ≤ |gapKeys g n - n|} ≤
        2 * Real.exp (-(c / 16) * qdev t x) := by
    intro n hn1 hnt x
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnt' : (n : ℝ) ≤ t := by exact_mod_cast hnt
    refine (iid_endpoint_bernstein hθ₁ hρ.pos hρ.mean hexp n hn1 (by positivity)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have hq1 : qdev t x ≤ (x - t) ^ 2 / t := min_le_left _ _
    have hq2 : qdev t x ≤ |x - t| := min_le_right _ _
    have hm : qdev t x / 4 ≤ min ((|x - t| / 2) ^ 2 / n) (|x - t| / 2) := by
      refine le_min ?_ ?_
      · have e : (|x - t| / 2) ^ 2 / n = (x - t) ^ 2 / (4 * n) := by
          rw [div_pow, sq_abs]
          ring
        rw [e]
        calc qdev t x / 4 ≤ (x - t) ^ 2 / t / 4 := by linarith
          _ = (x - t) ^ 2 / (4 * t) := by ring
          _ ≤ (x - t) ^ 2 / (4 * n) :=
            div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
      · have := abs_nonneg (x - (t : ℝ))
        linarith
    have := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ c / 4)
    linarith
  have h2 := measure_gapKeys_le_spatial ρ (r := r) (s := s) (hF r hr1) (hF s hs1) hA
  rw [hrst] at h2
  have hpt : ∀ x : ℝ, ENNReal.ofReal
      (F s * (iidLaw ρ).real {g | |x - t| / 2 ≤ |gapKeys g r - r|} +
        F r * (iidLaw ρ).real {g | |x - t| / 2 ≤ |gapKeys g s - s|}) ≤
      ENNReal.ofReal (4 * F r * Real.exp (-(c / 16) * qdev t x)) := by
    intro x
    refine ENNReal.ofReal_le_ofReal ?_
    have p1 := hb r hr1 (by omega) x
    have p2 := hb s hs1 (by omega) x
    have hP1 : 0 ≤ (iidLaw ρ).real {g | |x - t| / 2 ≤ |gapKeys g r - r|} := measureReal_nonneg
    have q1 := mul_le_mul_of_nonneg_right hFs hP1
    have q2 := mul_le_mul_of_nonneg_left p1 hFr0
    have q3 := mul_le_mul_of_nonneg_left p2 hFr0
    linarith
  exact h2.trans (lintegral_mono hpt)

omit [IsProbabilityMeasure P] in
/-- **Paired spatial bound** (`memory-route.md` (paired-space)). -/
theorem PairedHyp.pStopMeas_le_spatial {eps At aT δ : ℝ} (h : PairedHyp P V ρ eps At aT δ)
    {b β vmin θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) (heps : 8 ≤ eps) (hρ : MomClass b β vmin ρ)
    (hexp : ExpMom θ₁ B₁ ρ) {F : ℕ → ℝ}
    (hF : ∀ n, 1 ≤ n → LocBd (F n) (convPow (ρ : Measure ℝ) n))
    (hFa : ∀ n m, 1 ≤ n → n ≤ m → F m ≤ F n) {t : ℕ} (ht : 2 * eps < t) :
    pStopMeas eps P V t ≤ volume.withDensity fun x =>
      ENNReal.ofReal (8 / t * Real.exp (-(bernsteinRate θ₁ B₁ / 16) * qdev t x) *
        F (t / 2)) := by
  have heps0 : 0 ≤ eps := by linarith
  have ht' : (16 : ℝ) < t := by linarith
  have ht16 : 16 < t := by exact_mod_cast ht'
  have htpos : 0 < t := by omega
  have hr1 : 1 ≤ t / 2 := by omega
  have hFr0 : 0 ≤ F (t / 2) := (hF _ hr1).const_nonneg
  rw [Measure.le_iff]
  intro A hA
  have h1 := h.iid.actLen_sum_le_cyclic h.pos_act heps0 htpos MeasurableSet.univ
    (fun ω _ _ => Set.mem_univ ω) hA
  rw [Set.univ_inter] at h1
  have hSm : MeasurableSet {g : ℕ → ℝ | gapKeys g t ∈ A} :=
    ((measurable_pi_apply t).comp measurable_gapKeys) hA
  have hlaw : P {ω | gapKeys (fun i => (V i ω).2) t ∈ A} = iidLaw ρ {g | gapKeys g t ∈ A} :=
    h.iid.measure_pas_eq h.law_pas hSm
  rw [pStopMeas_apply h.iid.measurable eps t hA, withDensity_apply _ hA]
  calc P {ω | actLen eps V ω = (t : ℕ∞) ∧ gapKeys (fun i => (V i ω).2) t ∈ A}
      ≤ 2 / (t : ℝ≥0∞) * P {ω | gapKeys (fun i => (V i ω).2) t ∈ A} := h1
    _ ≤ 2 / (t : ℝ≥0∞) * ∫⁻ x in A, ENNReal.ofReal (4 * F (t / 2) *
          Real.exp (-(bernsteinRate θ₁ B₁ / 16) * qdev t x)) := by
        rw [hlaw]
        gcongr
        exact iidLaw_gapKeys_le_spatial hθ₁ hρ hexp hF hFa ht16 hA
    _ = ∫⁻ x in A, ENNReal.ofReal (2 / t) * ENNReal.ofReal (4 * F (t / 2) *
          Real.exp (-(bernsteinRate θ₁ B₁ / 16) * qdev t x)) := by
        rw [two_div_natCast_eq_ofReal htpos, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ x in A, ENNReal.ofReal (8 / t * Real.exp (-(bernsteinRate θ₁ B₁ / 16) * qdev t x) *
          F (t / 2)) := by
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring


/-! ## The combined kernel -/

/-- The rate of the main kernel. -/
def pRate1 (c aT : ℝ) : ℝ := min (c / 144) (aT / 16) / 3

/-- The rate of the residual kernel. -/
def pRate2 (c aT : ℝ) : ℝ := min (aT / 16) (c / 16) / 4

theorem pRate1_pos {c aT : ℝ} (hc : 0 < c) (haT : 0 < aT) : 0 < pRate1 c aT := by
  unfold pRate1; have := lt_min (by positivity : 0 < c / 144) (by positivity : 0 < aT / 16)
  positivity

theorem pRate2_pos {c aT : ℝ} (hc : 0 < c) (haT : 0 < aT) : 0 < pRate2 c aT := by
  unfold pRate2; have := lt_min (by positivity : 0 < aT / 16) (by positivity : 0 < c / 16)
  positivity

/-- `min(a₁ + a₂, m) ≤ min(a₁, m) + min(a₂, m)` for nonnegative entries. -/
theorem min_add_le_add_min {a₁ a₂ m : ℝ} (h1 : 0 ≤ a₁) (h2 : 0 ≤ a₂) (hm : 0 ≤ m) :
    min (a₁ + a₂) m ≤ min a₁ m + min a₂ m := by
  rcases le_total a₁ m with h | h <;> rcases le_total a₂ m with h' | h'
  · rw [min_eq_left h, min_eq_left h']; exact min_le_left _ _
  · rw [min_eq_left h, min_eq_right h']; linarith [min_le_right (a₁ + a₂) m]
  · rw [min_eq_right h, min_eq_left h']; linarith [min_le_right (a₁ + a₂) m]
  · rw [min_eq_right h, min_eq_right h']; linarith [min_le_right (a₁ + a₂) m]

/-- The pointwise combination of the three paired bounds. -/
theorem paired_min_le {c aT At t E Q δ F : ℝ} (hc : 0 < c) (hAt : 0 ≤ At)
    (ht : 0 < t) (hE : 0 < E) (hQ : 0 ≤ Q) (hδ : 0 ≤ δ) (hF : 0 ≤ F) :
    min (min (8 / t * (Real.exp (-(c / 144) * (E / t)) + 72 * t * δ / E) * F)
        (32 * At / t * Real.exp (-(aT / 16) * (t / E)) * F))
      (8 / t * Real.exp (-(c / 16) * Q) * F) ≤
    (8 + 32 * At) / t * F * Real.exp (-pRate1 c aT * (E / t + t / E + Q)) +
      (584 + 32 * At) / t * F * Real.sqrt (t * δ / E) *
        Real.exp (-pRate2 c aT * (t / E + Q)) := by
  set X := E / t with hX
  set Y := t / E with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  set u := c / 144 * X with hu
  set v := aT / 16 * Y with hv
  set w := c / 16 * Q with hw
  set C₀ := 8 + 32 * At with hC₀
  have hC₀8 : 8 ≤ C₀ := by linarith
  have hC₀A : 32 * At ≤ C₀ := by linarith
  set x₁ := 8 / t * Real.exp (-u) * F with hx₁
  set x₂ := 8 / t * (72 * t * δ / E) * F with hx₂
  set L := 32 * At / t * Real.exp (-v) * F with hL
  set Sp := 8 / t * Real.exp (-w) * F with hSp
  have hx₁0 : 0 ≤ x₁ := by positivity
  have hx₂0 : 0 ≤ x₂ := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hSp0 : 0 ≤ Sp := by positivity
  have hsplit : 8 / t * (Real.exp (-(c / 144) * (E / t)) + 72 * t * δ / E) * F = x₁ + x₂ := by
    rw [hx₁, hx₂, hu, neg_mul]; ring
  have hLeq : 32 * At / t * Real.exp (-(aT / 16) * (t / E)) * F = L := by
    rw [hL, hv, neg_mul]
  have hSpeq : 8 / t * Real.exp (-(c / 16) * Q) * F = Sp := by
    rw [hSp, hw, neg_mul]
  rw [hsplit, hLeq, hSpeq, min_assoc]
  refine (min_add_le_add_min hx₁0 hx₂0 (le_min hL0 hSp0)).trans (add_le_add ?_ ?_)
  · -- the main kernel
    set G := pRate1 c aT * (X + Y + Q) with hG
    have hg1 : pRate1 c aT ≤ c / 144 / 3 := by
      have := min_le_left (c / 144) (aT / 16); unfold pRate1; linarith
    have hg2 : pRate1 c aT ≤ aT / 16 / 3 := by
      have := min_le_right (c / 144) (aT / 16); unfold pRate1; linarith
    have hsum : G ≤ (u + v + w) / 3 := by
      have a1 := mul_le_mul_of_nonneg_right hg1 hX0
      have a2 := mul_le_mul_of_nonneg_right hg2 hY0
      have a3 := mul_le_mul_of_nonneg_right hg1 hQ
      have a4 : c / 144 * Q ≤ c / 16 * Q := mul_le_mul_of_nonneg_right (by linarith) hQ
      have e1 : c / 144 / 3 * X = u / 3 := by rw [hu]; ring
      have e2 : aT / 16 / 3 * Y = v / 3 := by rw [hv]; ring
      have e3 : c / 144 / 3 * Q ≤ w / 3 := by rw [hw]; linarith
      rw [hG, mul_add, mul_add]
      linarith
    have key : ∀ k z : ℝ, k ≤ C₀ → G ≤ z →
        k / t * Real.exp (-z) * F ≤ C₀ / t * F * Real.exp (-G) := by
      intro k z hk hz
      have he : Real.exp (-z) ≤ Real.exp (-G) := Real.exp_le_exp.2 (by linarith)
      have hk0 : 0 ≤ k * Real.exp (-z) ∨ k * Real.exp (-z) < 0 := le_or_gt _ _
      calc k / t * Real.exp (-z) * F = (k * Real.exp (-z)) * (F / t) := by ring
        _ ≤ (C₀ * Real.exp (-G)) * (F / t) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rcases le_or_gt 0 k with hk0 | hk0
            · exact mul_le_mul hk he (Real.exp_pos _).le (by linarith)
            · have : k * Real.exp (-z) ≤ 0 :=
                mul_nonpos_of_nonpos_of_nonneg hk0.le (Real.exp_pos _).le
              have : 0 ≤ C₀ * Real.exp (-G) := by positivity
              linarith
        _ = C₀ / t * F * Real.exp (-G) := by ring
    have hGeq : C₀ / t * F * Real.exp (-pRate1 c aT * (E / t + t / E + Q)) =
        C₀ / t * F * Real.exp (-G) := by rw [hG, neg_mul]
    rw [hGeq]
    by_cases h1 : G ≤ u
    · exact (min_le_left _ _).trans (key 8 u hC₀8 h1)
    by_cases h2 : G ≤ v
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans (key _ v hC₀A h2)
    have h3 : G ≤ w := by linarith
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (key 8 w hC₀8 h3)
  · -- the residual kernel
    set sr := Real.sqrt (t * δ / E) with hsr
    have hsr0 : 0 ≤ sr := Real.sqrt_nonneg _
    have hsr2 : sr ^ 2 = t * δ / E := Real.sq_sqrt (by positivity)
    set q := Real.exp (-((v + w) / 4)) with hq
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hq2 : q ^ 2 = Real.exp (-((v + w) / 2)) := by
      rw [hq, pow_two, ← Real.exp_add]; congr 1; ring
    have hLS : min L Sp ≤ C₀ / t * F * q ^ 2 := by
      rw [hq2]
      rcases le_total v w with hvw | hvw
      · refine (min_le_right _ _).trans ?_
        have he : Real.exp (-w) ≤ Real.exp (-((v + w) / 2)) := Real.exp_le_exp.2 (by linarith)
        calc Sp = 8 * Real.exp (-w) * (F / t) := by rw [hSp]; ring
          _ ≤ C₀ * Real.exp (-((v + w) / 2)) * (F / t) := by gcongr
          _ = C₀ / t * F * Real.exp (-((v + w) / 2)) := by ring
      · refine (min_le_left _ _).trans ?_
        have he : Real.exp (-v) ≤ Real.exp (-((v + w) / 2)) := Real.exp_le_exp.2 (by linarith)
        calc L = 32 * At * Real.exp (-v) * (F / t) := by rw [hL]; ring
          _ ≤ C₀ * Real.exp (-((v + w) / 2)) * (F / t) := by gcongr
          _ = C₀ / t * F * Real.exp (-((v + w) / 2)) := by ring
    have hx₂eq : x₂ = 576 / t * F * sr ^ 2 := by
      rw [hx₂, hsr2]; field_simp; ring
    have hFt : 0 ≤ F / t := by positivity
    have hmin : min x₂ (min L Sp) ≤ (584 + 32 * At) / t * F * sr * q := by
      rcases le_total sr q with hsr_q | hsr_q
      · refine (min_le_left _ _).trans ?_
        rw [hx₂eq]
        have : sr ^ 2 ≤ sr * q := by rw [pow_two]; exact mul_le_mul_of_nonneg_left hsr_q hsr0
        calc 576 / t * F * sr ^ 2 = 576 * (F / t) * sr ^ 2 := by ring
          _ ≤ (584 + 32 * At) * (F / t) * (sr * q) := by
              gcongr
              linarith
          _ = (584 + 32 * At) / t * F * sr * q := by ring
      · refine (min_le_right _ _).trans (hLS.trans ?_)
        have : q ^ 2 ≤ sr * q := by rw [pow_two]; exact mul_le_mul_of_nonneg_right hsr_q hq0
        calc C₀ / t * F * q ^ 2 = C₀ * (F / t) * q ^ 2 := by ring
          _ ≤ (584 + 32 * At) * (F / t) * (sr * q) := by
              gcongr
              linarith
          _ = (584 + 32 * At) / t * F * sr * q := by ring
    refine hmin.trans ?_
    have hg1 : pRate2 c aT ≤ aT / 16 / 4 := by
      have := min_le_left (aT / 16) (c / 16); unfold pRate2; linarith
    have hg2 : pRate2 c aT ≤ c / 16 / 4 := by
      have := min_le_right (aT / 16) (c / 16); unfold pRate2; linarith
    have hqle : q ≤ Real.exp (-pRate2 c aT * (t / E + Q)) := by
      rw [hq]
      refine Real.exp_le_exp.2 ?_
      have a1 := mul_le_mul_of_nonneg_right hg1 hY0
      have a2 := mul_le_mul_of_nonneg_right hg2 hQ
      have e1 : aT / 16 / 4 * Y = v / 4 := by rw [hv]; ring
      have e2 : c / 16 / 4 * Q = w / 4 := by rw [hw]; ring
      have key : pRate2 c aT * (Y + Q) ≤ (v + w) / 4 := by rw [mul_add]; linarith
      rw [neg_mul]
      linarith
    have : 0 ≤ (584 + 32 * At) / t * F * sr := by positivity
    exact mul_le_mul_of_nonneg_left hqle this

/-- **The paired joint stopping bound**: early, long-time and spatial bounds combined. -/
theorem PairedHyp.pStopMeas_le_kernel {eps At aT δ : ℝ} (h : PairedHyp P V ρ eps At aT δ)
    {b β vmin θ₁ B₁ : ℝ} (hθ₁ : 0 < θ₁) (hAt : 0 ≤ At) (haT : 0 < aT) (heps : 8 ≤ eps)
    (hρ : MomClass b β vmin ρ) (hexp : ExpMom θ₁ B₁ ρ) {F : ℕ → ℝ}
    (hF : ∀ n, 1 ≤ n → LocBd (F n) (convPow (ρ : Measure ℝ) n))
    (hFa : ∀ n m, 1 ≤ n → n ≤ m → F m ≤ F n) {t : ℕ} (ht : 2 * eps < t) :
    pStopMeas eps P V t ≤ volume.withDensity fun a => ENNReal.ofReal
      ((8 + 32 * At) / t * F (t / 2) * Real.exp (-pRate1 (bernsteinRate θ₁ B₁) aT *
          (eps ^ 2 / t + t / eps ^ 2 + qdev t a)) +
        (584 + 32 * At) / t * F (t / 2) * Real.sqrt (t * δ / eps ^ 2) *
          Real.exp (-pRate2 (bernsteinRate θ₁ B₁) aT * (t / eps ^ 2 + qdev t a))) := by
  have hB₁ : 0 < B₁ := (integral_exp_pos hexp.integrable).trans_le hexp.le
  have hc0 : 0 < bernsteinRate θ₁ B₁ := bernsteinRate_pos hθ₁ hB₁
  have htpos : (0 : ℝ) < t := by linarith
  have hr1 : 1 ≤ t / 2 := by
    have : (2 : ℝ) < t := by linarith
    have : 2 < t := by exact_mod_cast this
    omega
  have hFr0 : 0 ≤ F (t / 2) := (hF _ hr1).const_nonneg
  have hq : Measurable fun x : ℝ => qdev t x :=
    Continuous.measurable (by unfold qdev; fun_prop)
  have hm3 : Measurable fun x : ℝ => ENNReal.ofReal
      (8 / t * Real.exp (-(bernsteinRate θ₁ B₁ / 16) * qdev t x) * F (t / 2)) := by
    fun_prop
  have h1 := h.pStopMeas_le_early hθ₁ heps hρ hexp hF hFa ht
  have h2 := h.pStopMeas_le_long hAt haT heps hF hFa ht
  have h3 := h.pStopMeas_le_spatial hθ₁ heps hρ hexp hF hFa ht
  have h12 := le_withDensity_min measurable_const measurable_const h1 h2
  have h123 := le_withDensity_min (measurable_const.min measurable_const) hm3 h12 h3
  refine h123.trans (withDensity_mono (Filter.Eventually.of_forall fun a => ?_))
  beta_reduce
  rw [← ENNReal.ofReal_min, ← ENNReal.ofReal_min]
  refine ENNReal.ofReal_le_ofReal ?_
  have hQ : 0 ≤ qdev t a := le_min (div_nonneg (sq_nonneg _) htpos.le) (abs_nonneg _)
  have hE : 0 < eps ^ 2 := by
    have : (0 : ℝ) < eps := by linarith
    positivity
  exact paired_min_le hc0 hAt htpos hE hQ h.delta_nonneg hFr0


end

end PGM
