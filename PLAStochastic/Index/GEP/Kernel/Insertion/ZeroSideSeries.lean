import PLAStochastic.Index.GEP.Kernel.Insertion.MovingJump
import PLAStochastic.Index.GEP.Kernel.Insertion.SignedSeries

/-! # Actual signed zero-side long insertion series, with their moving jump -/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

def krZeroInsertionDens (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w a : ℝ)
    (up left : Bool) (n : ℕ) (x : ℝ) : ℝ :=
  kernelMarkedFullDens (Icc 0 w) ν f 1 a x (if left then 0 else n)
    (if left then n else 0) (if up then 0 else w) (if up then w else 0)

def krZeroInsertionPin (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w a : ℝ)
    (up left : Bool) (n : ℕ) : ℝ :=
  if left then
    krDens (Icc 0 w) ν f (-1) (-a) n (if up then w else 0) (if up then 0 else w)
  else krDens (Icc 0 w) ν f 1 a n (if up then 0 else w) (if up then w else 0)

set_option maxHeartbeats 400000 in
theorem krZeroInsertion_row {X : Type*} [MeasurableSpace X] [Nonempty X]
    {D θ vlo vhi K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {a : X → ℝ} (ha : Measurable a) (ha0 : ∀ p, 0 ≤ a p)
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) 1 (a p))
    (up left : Bool) {n : ℕ} (hn : 12 ≤ n) {R : ℝ} (hWR : 2*R ≤ w) :
    ∃ h r : X → ℝ → ℂ, ∃ j : X → ℂ,
      Measurable (fun p : X × ℝ => h p.1 p.2) ∧
      Measurable (fun p : X × ℝ => r p.1 p.2) ∧ Measurable j ∧
      (∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 →
        (krZeroInsertionDens ν f w (a p) up left (n+1) x : ℂ) =
          h p x + (if a p*x < 1 then j p else 0) + r p x) ∧
      (∀ p x y, ‖h p x-h p y‖ ≤
        (4*D*krRowVarBudget D K L vlo vhi w A (n+1))*|x-y|) ∧
      (∀ p x, ‖r p x‖ ≤ 4*krRowRemBudget D K L vlo vhi A (n+1)) ∧
      (∀ p, ‖j p‖ ≤ krZeroInsertionPin ν f w (a p) up left (n+1) +
        4*krRowRemBudget D K L vlo vhi A (n+1)) ∧
      (∀ p x, ‖h p x‖ ≤ 2*krRowVarBudget D K L vlo vhi w A (n+1)) := by
  cases up with
  | false =>
    cases left with
    | false => exact krInsertion_zero_right_down_long ν ha H hn hWR
    | true => exact krInsertion_zero_left_down_long ν ha H hn hWR
  | true =>
    cases left with
    | false =>
      obtain ⟨h,r,j,hh,hr,hj,he,hl,hrem,hpin,hb⟩ := krInsertion_zero_right_up_long ν ha ha0 H hn
      exact ⟨h,r,j,hh,hr,hj,fun p x hx hc => he p x hx.1 hc,hl,hrem,hpin,hb⟩
    | true =>
      obtain ⟨h,r,j,hh,hr,hj,he,hl,hrem,hpin,hb⟩ := krInsertion_zero_left_up_long ν ha ha0 H hn
      exact ⟨h,r,j,hh,hr,hj,fun p x hx hc => he p x hx.1 hc,hl,hrem,hpin,hb⟩

theorem krLong_expw_pin_bound {D θ vlo vhi K L w A a β a' : ℝ}
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (hAw : A ≤ w)
    {b c : ℝ} (hb : b=0 ∨ b=w) (hc : c=0 ∨ c=w) (hbc : b ≠ c) (P : ℕ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi/16) :
    Summable (fun i : ℕ => Real.exp (ε*((P+1+i : ℕ) : ℝ)/w^2)*
      krDens (Icc 0 w) ν f β a' (P+1+i) b c) ∧
    (∑' i : ℕ, Real.exp (ε*((P+1+i : ℕ) : ℝ)/w^2)*
      krDens (Icc 0 w) ν f β a' (P+1+i) b c) ≤
      Real.exp (3*ε)*((krCP D θ K L vlo vhi+12*krC₂ D K L/krKappa D vlo vhi)*(1+A)^2/Real.sqrt w) := by
  refine ⟨summable_expw_krDens_long_row ν H hb P c hε0 hε, ?_⟩
  apply Real.tsum_le_of_sum_range_le (fun i => mul_nonneg (Real.exp_pos _).le (krDens_nonneg ν H.hf0 _ _ _))
  intro M
  refine le_trans ?_ (sum_expw_krDens_bdry_pin_le ν H hAw hb hc hbc hε0 hε (P+M))
  rw [Finset.sum_range_add]
  have hi : ∀ i : ℕ, P+1+i = P+i+1 := fun i => by omega
  simp_rw [hi]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ =>
    mul_nonneg (Real.exp_pos _).le (krDens_nonneg ν H.hf0 _ _ _))

theorem krZeroInsertionPin_expw {D θ vlo vhi K L w A a : ℝ}
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a 1 a) (hAw : A ≤ w)
    (up left : Bool) (P : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi/16) :
    Summable (fun i : ℕ => Real.exp (ε*((P+1+i : ℕ) : ℝ)/w^2)*
      krZeroInsertionPin ν f w a up left (P+1+i)) ∧
    (∑' i : ℕ, Real.exp (ε*((P+1+i : ℕ) : ℝ)/w^2)*
      krZeroInsertionPin ν f w a up left (P+1+i)) ≤
      Real.exp (3*ε)*((krCP D θ K L vlo vhi+12*krC₂ D K L/krKappa D vlo vhi)*(1+A)^2/Real.sqrt w) := by
  have hw : w ≠ 0 := H.hw0.ne'
  cases up <;> cases left <;> simp only [krZeroInsertionPin, Bool.false_eq_true, if_false, if_true]
  · exact krLong_expw_pin_bound ν H hAw (Or.inr rfl) (Or.inl rfl) hw P hε0 hε
  · exact krLong_expw_pin_bound ν H.rev hAw (Or.inl rfl) (Or.inr rfl) hw.symm P hε0 hε
  · exact krLong_expw_pin_bound ν H hAw (Or.inl rfl) (Or.inr rfl) hw.symm P hε0 hε
  · exact krLong_expw_pin_bound ν H.rev hAw (Or.inr rfl) (Or.inl rfl) hw P hε0 hε

set_option maxHeartbeats 800000 in
/-- All four actual zero-side long series with arbitrary signed slope weights. -/
theorem krInsertion_signed_zero_long {X : Type*} [MeasurableSpace X] [Nonempty X]
    {D θ vlo vhi K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {a : X → ℝ} (ha : Measurable a) (ha0 : ∀ p, 0 ≤ a p)
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) 1 (a p))
    (hAw : A ≤ w) (up left : Bool) {P : ℕ} (hP : 12 ≤ P) {R : ℝ} (hWR : 2*R ≤ w)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krEps D vlo vhi)
    {v : ℕ → X → ℝ} (hv : ∀ i, Measurable (v i))
    (hvb : ∀ i p, |v i p| ≤ Real.exp (ε*((P+1+i : ℕ) : ℝ)/w^2)) :
    let VB := 2*Real.exp (3*ε)*krCV D K L vlo vhi*(1+A)*(Real.sqrt w/krFourthRoot P+1)
    let RB := 2*Real.exp (5*ε)*krCR D K L vlo vhi*(1+A)*((1+kBVClassRho D vlo vhi)/2)^(P/3-1)
    let PB := Real.exp (3*ε)*((krCP D θ K L vlo vhi+12*krC₂ D K L/krKappa D vlo vhi)*(1+A)^2/Real.sqrt w)
    (∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 → Summable fun i : ℕ =>
      v i p*krZeroInsertionDens ν f w (a p) up left (P+1+i) x) ∧
    ∃ G E : X → ℝ → ℂ, ∃ j : X → ℂ,
      Measurable (fun p : X × ℝ => G p.1 p.2) ∧
      Measurable (fun p : X × ℝ => E p.1 p.2) ∧ Measurable j ∧
      (∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 →
        ((∑' i : ℕ, v i p*krZeroInsertionDens ν f w (a p) up left (P+1+i) x : ℝ) : ℂ) =
          G p x+(if a p*x < 1 then j p else 0)+E p x) ∧
      (∀ p x y, ‖G p x-G p y‖ ≤ (4*D*VB)*|x-y|) ∧
      (∀ p x, ‖E p x‖ ≤ 4*RB) ∧ (∀ p, ‖j p‖ ≤ PB+4*RB) ∧
      (∀ p x, ‖G p x‖ ≤ 2*VB) := by
  classical
  dsimp only
  have H₀ := H (Classical.choice ‹Nonempty X›)
  have hεκ : ε ≤ krKappa D vlo vhi/16 := by
    have := hε.trans H₀.krEps_le_kappa
    have := H₀.kappa_pos
    linarith
  let ω : ℕ → ℝ := fun i => Real.exp (ε*((P+1+i : ℕ) : ℝ)/w^2)
  let V : ℕ → ℝ := fun i => ω i*krRowVarBudget D K L vlo vhi w A (P+1+i)
  let E : ℕ → ℝ := fun i => ω i*krRowRemBudget D K L vlo vhi A (P+1+i)
  let T : X → ℕ → ℝ := fun p i => ω i*krZeroInsertionPin ν f w (a p) up left (P+1+i)
  let VB := 2*Real.exp (3*ε)*krCV D K L vlo vhi*(1+A)*(Real.sqrt w/krFourthRoot P+1)
  let RB := 2*Real.exp (5*ε)*krCR D K L vlo vhi*(1+A)*((1+kBVClassRho D vlo vhi)/2)^(P/3-1)
  let PB := Real.exp (3*ε)*((krCP D θ K L vlo vhi+12*krC₂ D K L/krKappa D vlo vhi)*(1+A)^2/Real.sqrt w)
  obtain ⟨hVs,hVB,hEs,hEB⟩ := krRow_expw_absolute_budgets ν H₀ hP hε0 hε
  change Summable V at hVs
  change Summable E at hEs
  change (∑' i, V i) ≤ VB at hVB
  change (∑' i, E i) ≤ RB at hEB
  have hTs : ∀ p, Summable (T p) := fun p => (krZeroInsertionPin_expw ν (H p) hAw up left P hε0 hεκ).1
  have hTB : ∀ p, (∑' i, T p i) ≤ PB := fun p => (krZeroInsertionPin_expw ν (H p) hAw up left P hε0 hεκ).2
  have hd : ∀ i : ℕ, ∃ g r : X → ℝ → ℂ, ∃ j : X → ℂ,
      Measurable (fun p : X × ℝ => g p.1 p.2) ∧
      Measurable (fun p : X × ℝ => r p.1 p.2) ∧ Measurable j ∧
      (∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 →
        (krZeroInsertionDens ν f w (a p) up left (P+1+i) x : ℂ) =
          g p x+(if a p*x < 1 then j p else 0)+r p x) ∧
      (∀ p x y, ‖g p x-g p y‖ ≤ (4*D*krRowVarBudget D K L vlo vhi w A (P+1+i))*|x-y|) ∧
      (∀ p x, ‖r p x‖ ≤ 4*krRowRemBudget D K L vlo vhi A (P+1+i)) ∧
      (∀ p, ‖j p‖ ≤ krZeroInsertionPin ν f w (a p) up left (P+1+i)+4*krRowRemBudget D K L vlo vhi A (P+1+i)) ∧
      (∀ p x, ‖g p x‖ ≤ 2*krRowVarBudget D K L vlo vhi w A (P+1+i)) := by
    intro i
    have hi : P+i+1=P+1+i := by omega
    simpa only [hi] using krZeroInsertion_row ν ha ha0 H up left (n := P+i) (by omega) hWR
  choose g r j hg hr hj he hl hrem hpin hnorm using hd
  let gf : ℕ → X → ℝ → ℂ := fun i p x => (v i p : ℂ)*g i p x
  let rf : ℕ → X → ℝ → ℂ := fun i p x => (v i p : ℂ)*r i p x
  let jf : ℕ → X → ℂ := fun i p => (v i p : ℂ)*j i p
  have hgm : ∀ i, Measurable (fun p : X × ℝ => gf i p.1 p.2) := fun i =>
    (Complex.measurable_ofReal.comp ((hv i).comp measurable_fst)).mul (hg i)
  have hrm : ∀ i, Measurable (fun p : X × ℝ => rf i p.1 p.2) := fun i =>
    (Complex.measurable_ofReal.comp ((hv i).comp measurable_fst)).mul (hr i)
  have hjm : ∀ i, Measurable (jf i) := fun i => (Complex.measurable_ofReal.comp (hv i)).mul (hj i)
  have hgn : ∀ i p x, ‖gf i p x‖ ≤ 2*V i := by
    intro i p x
    dsimp only [gf]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hh := mul_le_mul (hvb i p) (hnorm i p x) (norm_nonneg _) (Real.exp_pos _).le
    exact hh.trans_eq (by dsimp only [V,ω]; ring)
  have hrn : ∀ i p x, ‖rf i p x‖ ≤ 4*E i := by
    intro i p x
    dsimp only [rf]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hh := mul_le_mul (hvb i p) (hrem i p x) (norm_nonneg _) (Real.exp_pos _).le
    exact hh.trans_eq (by dsimp only [E,ω]; ring)
  have hjn : ∀ i p, ‖jf i p‖ ≤ T p i+4*E i := by
    intro i p
    dsimp only [jf]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hh := mul_le_mul (hvb i p) (hpin i p) (norm_nonneg _) (Real.exp_pos _).le
    exact hh.trans_eq (by dsimp only [T,E,ω]; ring)
  have hgl : ∀ i p x y, ‖gf i p x-gf i p y‖ ≤ (4*D*V i)*|x-y| := by
    intro i p x y
    dsimp only [gf]
    rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hh := mul_le_mul (hvb i p) (hl i p x y) (norm_nonneg _) (Real.exp_pos _).le
    exact hh.trans_eq (by dsimp only [V,ω]; ring)
  have hgs : ∀ p x, Summable fun i => gf i p x := fun p x =>
    (hVs.mul_left 2).of_norm_bounded (fun i => hgn i p x)
  have hrs : ∀ p x, Summable fun i => rf i p x := fun p x =>
    (hEs.mul_left 4).of_norm_bounded (fun i => hrn i p x)
  have hjs : ∀ p, Summable fun i => jf i p := fun p =>
    ((hTs p).add (hEs.mul_left 4)).of_norm_bounded (fun i => hjn i p)
  have hstep : ∀ p x, Summable fun i => if a p*x < 1 then jf i p else 0 := by
    intro p x
    split_ifs
    · exact hjs p
    · exact summable_zero
  have hsplit : ∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 → ∀ i,
      ((v i p*krZeroInsertionDens ν f w (a p) up left (P+1+i) x : ℝ) : ℂ) =
        gf i p x+(if a p*x < 1 then jf i p else 0)+rf i p x := by
    intro p x hx hc i
    rw [Complex.ofReal_mul, he i p x hx hc]
    dsimp only [gf,rf,jf]
    split_ifs <;> ring
  have hqs : ∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 → Summable fun i : ℕ =>
      ((v i p*krZeroInsertionDens ν f w (a p) up left (P+1+i) x : ℝ) : ℂ) := by
    intro p x hx hc
    exact (((hgs p x).add (hstep p x)).add (hrs p x)).congr (fun i => (hsplit p x hx hc i).symm)
  refine ⟨fun p x hx hc => Complex.summable_ofReal.mp (hqs p x hx hc),
    (fun p x => ∑' i, gf i p x), (fun p x => ∑' i, rf i p x), (fun p => ∑' i, jf i p),
    Measurable.tsum hgm, Measurable.tsum hrm, Measurable.tsum hjm, ?_, ?_, ?_, ?_, ?_⟩
  · intro p x hx hc
    rw [Complex.ofReal_tsum]
    simp_rw [hsplit p x hx hc]
    rw [((hgs p x).add (hstep p x)).tsum_add (hrs p x), (hgs p x).tsum_add (hstep p x)]
    split_ifs <;> simp only [tsum_zero]
  · intro p x y
    rw [← (hgs p x).tsum_sub (hgs p y)]
    refine (tsum_of_norm_bounded ((hVs.mul_left (4*D)).mul_right |x-y|).hasSum (fun i => hgl i p x y)).trans ?_
    rw [tsum_mul_right,tsum_mul_left]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVB (by linarith [H₀.hD0])) (abs_nonneg _)
  · intro p x
    refine (tsum_of_norm_bounded (hEs.mul_left 4).hasSum (fun i => hrn i p x)).trans ?_
    rw [tsum_mul_left]
    linarith
  · intro p
    refine (tsum_of_norm_bounded ((hTs p).add (hEs.mul_left 4)).hasSum (fun i => hjn i p)).trans ?_
    rw [(hTs p).tsum_add (hEs.mul_left 4),tsum_mul_left]
    linarith [hTB p]
  · intro p x
    refine (tsum_of_norm_bounded (hVs.mul_left 2).hasSum (fun i => hgn i p x)).trans ?_
    rw [tsum_mul_left]
    linarith

end
end PGM
