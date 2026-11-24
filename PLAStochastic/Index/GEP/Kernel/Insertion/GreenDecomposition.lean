import PLAStochastic.Index.GEP.Kernel.Insertion.LengthPartition
import PLAStochastic.Index.GEP.Kernel.Marked.Pin.ShortBridge

/-!
# The actual signed insertion Green decomposition

All length pairs are partitioned exactly into a finite short square, two
positive-side long regions, and the two zero-side long regions. The reward
may depend on the two lengths and every measurable external parameter.
-/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

set_option maxHeartbeats 1200000 in
theorem krInsertion_signed_full_of_short {X : Type*} [MeasurableSpace X] [Nonempty X]
    {D θ vlo vhi K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {a : X → ℝ} (ha : Measurable a) (ha0 : ∀ p, 0 ≤ a p)
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) 1 (a p))
    (hAw : A ≤ w) (up : Bool) {P : ℕ} (hP : 12 ≤ P) {R : ℝ} (hWR : 2*R ≤ w)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krEps D vlo vhi)
    {v : (ℕ × ℕ) → X → ℝ} (hv : ∀ q, Measurable (v q))
    (hvb : ∀ q p, |v q p| ≤ Real.exp (ε*(q.1 : ℝ)/w^2)*Real.exp (ε*(q.2 : ℝ)/w^2))
    {SB : ℝ}
    (hshort : ∀ p x, x ∈ Icc 0 R → ∀ l r : ℕ, l ≤ P → r ≤ P →
      kernelMarkedFullDens (Icc 0 w) ν f 1 (a p) x l r (if up then 0 else w) (if up then w else 0) ≤ SB) :
    let VB := 2*Real.exp (3*ε)*krCV D K L vlo vhi*(1+A)*(Real.sqrt w/krFourthRoot P+1)
    let RB := 2*Real.exp (5*ε)*krCR D K L vlo vhi*(1+A)*((1+kBVClassRho D vlo vhi)/2)^(P/3-1)
    let BB := Real.exp (3*ε)*((krCG D K L vlo vhi+4*krC₄ D K L/krKappa D vlo vhi)*(1+A)*(1+Real.log w))
    let OB := Real.exp (3*ε)*((krCO D K L vlo vhi+4*krC₃ D K L/krKappa D vlo vhi)*(1+A)*w)
    let PB := Real.exp (3*ε)*((krCP D θ K L vlo vhi+12*krC₂ D K L/krKappa D vlo vhi)*(1+A)^2/Real.sqrt w)
    let ST := ((P+1 : ℕ) : ℝ)^2*Real.exp (2*ε*(P : ℝ)/w^2)*SB
    (∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 → Summable fun q : ℕ × ℕ => v q p*
      kernelMarkedFullDens (Icc 0 w) ν f 1 (a p) x q.1 q.2 (if up then 0 else w) (if up then w else 0)) ∧
    ∃ G E : X → ℝ → ℂ, ∃ j : X → ℂ,
      Measurable (fun p : X × ℝ => G p.1 p.2) ∧
      Measurable (fun p : X × ℝ => E p.1 p.2) ∧ Measurable j ∧
      (∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 →
        ((∑' q : ℕ × ℕ, v q p*kernelMarkedFullDens (Icc 0 w) ν f 1 (a p) x
          q.1 q.2 (if up then 0 else w) (if up then w else 0) : ℝ) : ℂ) =
        G p x+(if a p*x < 1 then j p else 0)+E p x) ∧
      (∀ p x y, ‖G p x-G p y‖ ≤ (4*VB*BB+8*D*VB)*|x-y|) ∧
      (∀ p x, x ∈ Icc 0 R → ‖E p x‖ ≤ 8*RB*OB+8*RB+ST) ∧
      (∀ p, ‖j p‖ ≤ 2*PB+8*RB) ∧ (∀ p x, ‖G p x‖ ≤ 2*VB*OB+4*VB) := by
  classical
  dsimp only
  have H₀ := H (Classical.choice ‹Nonempty X›)
  let b : ℝ := if up then 0 else w
  let c : ℝ := if up then w else 0
  have hb : b=0 ∨ b=w := by cases up <;> simp [b]
  have hc : c=0 ∨ c=w := by cases up <;> simp [c]
  let F : (ℕ × ℕ) → X → ℝ → ℝ := fun q p x => v q p*
    kernelMarkedFullDens (Icc 0 w) ν f 1 (a p) x q.1 q.2 b c
  let vl : (ℕ × ℕ) → X → ℝ := fun q p => if q.1 < P then v (P+1+q.2,q.1+1) p else 0
  have hvl : ∀ q, Measurable (vl q) := by
    intro q
    by_cases hq : q.1 < P
    · simpa only [vl,if_pos hq] using hv (P+1+q.2,q.1+1)
    · simpa only [vl,if_neg hq] using (measurable_const : Measurable (fun _ : X => (0 : ℝ)))
  have hvlb : ∀ q p, |vl q p| ≤ Real.exp (ε*((q.1+1 : ℕ) : ℝ)/w^2)*Real.exp (ε*((P+1+q.2 : ℕ) : ℝ)/w^2) := by
    intro q p
    by_cases hq : q.1 < P
    · simpa only [vl,if_pos hq,mul_comm] using hvb (P+1+q.2,q.1+1) p
    · simp only [vl,if_neg hq,abs_zero]
      positivity
  obtain ⟨hSr, Gr, Er, hGr, hEr, eqr, lipr, remr, normr⟩ :=
    krInsertion_signed_long_right ν measurable_const ha H hb hc hP hε0 hε
      (fun q => hv (q.1+1,P+1+q.2)) (fun q p => hvb (q.1+1,P+1+q.2) p)
  obtain ⟨hSl, Gl, El, hGl, hEl, eql, lipl, reml, norml⟩ :=
    krInsertion_signed_long_left ν measurable_const ha H hb hc hP hε0 hε hvl hvlb
  have hvzl : ∀ i p, |v (0,P+1+i) p| ≤ Real.exp (ε*((P+1+i : ℕ) : ℝ)/w^2) := by
    intro i p
    simpa only [Nat.cast_zero,mul_zero,zero_div,Real.exp_zero,one_mul] using hvb (0,P+1+i) p
  have hvzr : ∀ i p, |v (P+1+i,0) p| ≤ Real.exp (ε*((P+1+i : ℕ) : ℝ)/w^2) := by
    intro i p
    simpa only [Nat.cast_zero,mul_zero,zero_div,Real.exp_zero,mul_one] using hvb (P+1+i,0) p
  obtain ⟨hSzl,Gzl,Ezl,jl,hGzl,hEzl,hjl,eqzl,lipzl,remzl,pinzl,normzl⟩ :=
    krInsertion_signed_zero_long ν ha ha0 H hAw up true hP hWR hε0 hε
      (fun i => hv (0,P+1+i)) hvzl
  obtain ⟨hSzr,Gzr,Ezr,jr,hGzr,hEzr,hjr,eqzr,lipzr,remzr,pinzr,normzr⟩ :=
    krInsertion_signed_zero_long ν ha ha0 H hAw up false hP hWR hε0 hε
      (fun i => hv (P+1+i,0)) hvzr
  have hmask : ∀ p x, Summable fun q : ℕ × ℕ => if q.1<P then F (P+1+q.2,q.1+1) p x else 0 := by
    intro p x
    exact (hSl p x).congr (fun q => by dsimp only [vl,F]; split_ifs <;> simp only [zero_mul])
  have hfinite := fun p x => krInsertion_mask_finite (fun q : ℕ × ℕ => F (P+1+q.2,q.1+1) p x) P (hmask p x)
  have hpart : ∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 →
      Summable (fun q => F q p x) ∧ (∑' q, F q p x) =
        (∑ q : Fin (P+1) × Fin (P+1), F (q.1,q.2) p x)+
        (∑' i, F (0,P+1+i) p x)+(∑' i, F (P+1+i,0) p x)+
        (∑' q : ℕ × ℕ, F (q.1+1,P+1+q.2) p x)+
        (∑' q : Fin P × ℕ, F (P+1+q.2,q.1+1) p x) := by
    intro p x hx hcross
    exact krInsertion_sum_partition (fun q => F q p x) P (hSzl p x hx hcross)
      (hSzr p x hx hcross) (hSr p x) (hfinite p x).1
  let short : X → ℝ → ℂ := fun p x => (∑ q : Fin (P+1) × Fin (P+1), F (q.1,q.2) p x : ℝ)
  have hshortM : Measurable (fun p : X × ℝ => short p.1 p.2) :=
    Complex.measurable_ofReal.comp (Finset.measurable_sum _ fun q _ =>
      ((hv (q.1,q.2)).comp measurable_fst).mul
        (measurable_kernelMarkedFullDens_param ν (H₀.hJ) H₀.hf measurable_const
          (ha.comp measurable_fst) measurable_snd measurable_const measurable_const q.1 q.2))
  have hshortB : ∀ p x, x ∈ Icc 0 R → ‖short p x‖ ≤
      ((P+1 : ℕ) : ℝ)^2*Real.exp (2*ε*(P : ℝ)/w^2)*SB := by
    intro p x hx
    have hterm : ∀ q : Fin (P+1) × Fin (P+1), ‖(F (q.1,q.2) p x : ℂ)‖ ≤
        Real.exp (2*ε*(P : ℝ)/w^2)*SB := by
      intro q
      have hl : (q.1 : ℕ) ≤ P := by omega
      have hr : (q.2 : ℕ) ≤ P := by omega
      have hω : Real.exp (ε*((q.1 : ℕ) : ℝ)/w^2)*Real.exp (ε*((q.2 : ℕ) : ℝ)/w^2) ≤
          Real.exp (2*ε*(P : ℝ)/w^2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hl' : ((q.1 : ℕ) : ℝ) ≤ P := by exact_mod_cast hl
        have hr' : ((q.2 : ℕ) : ℝ) ≤ P := by exact_mod_cast hr
        have hh : ε*((q.1 : ℕ) : ℝ)+ε*((q.2 : ℕ) : ℝ) ≤ 2*ε*(P : ℝ) := by nlinarith
        simpa only [add_div] using div_le_div_of_nonneg_right hh (sq_nonneg w)
      have hn := kernelMarkedFullDens_nonneg (J := Icc 0 w) ν (H p).hf0 1 (a p) x (q.1 : ℕ) (q.2 : ℕ) b c
      have hs := hshort p x hx (q.1 : ℕ) (q.2 : ℕ) hl hr
      simp only [F,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg hn]
      exact mul_le_mul ((hvb ((q.1 : ℕ),(q.2 : ℕ)) p).trans hω) hs hn (Real.exp_pos _).le
    dsimp only [short]
    rw [Complex.ofReal_sum]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun q _ => hterm q)).trans_eq ?_)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
    ring
  let G : X → ℝ → ℂ := fun p x => Gr p x+Gl p x+Gzl p x+Gzr p x
  let E : X → ℝ → ℂ := fun p x => Er p x+El p x+Ezl p x+Ezr p x+short p x
  let j : X → ℂ := fun p => jl p+jr p
  refine ⟨fun p x hx hc => (hpart p x hx hc).1, G,E,j,
    ((hGr.add hGl).add hGzl).add hGzr, (((hEr.add hEl).add hEzl).add hEzr).add hshortM,
    hjl.add hjr, ?_, ?_, ?_, ?_, ?_⟩
  · intro p x hx hcross
    have hlEq : ((∑' q : Fin P × ℕ, F (P+1+q.2,q.1+1) p x : ℝ) : ℂ)=Gl p x+El p x := by
      rw [(hfinite p x).2]
      convert eql p x using 1
      congr 1
      apply tsum_congr
      intro q
      dsimp only [vl,F]
      split_ifs <;> simp only [zero_mul]
    change ((∑' q, F q p x : ℝ) : ℂ)=_
    rw [(hpart p x hx hcross).2]
    simp only [Complex.ofReal_add]
    have hzlEq : ((∑' i, F (0,P+1+i) p x : ℝ) : ℂ) =
        Gzl p x+(if a p*x<1 then jl p else 0)+Ezl p x := by
      simpa only [F,b,c,krZeroInsertionDens,if_true] using eqzl p x hx hcross
    have hzrEq : ((∑' i, F (P+1+i,0) p x : ℝ) : ℂ) =
        Gzr p x+(if a p*x<1 then jr p else 0)+Ezr p x := by
      simpa only [F,b,c,krZeroInsertionDens,Bool.false_eq_true,if_false] using eqzr p x hx hcross
    rw [hlEq,eqr p x,hzlEq,hzrEq]
    dsimp only [G,E,j,short]
    split_ifs <;> ring
  · intro p x y
    have hid : G p x-G p y =
        (Gr p x-Gr p y)+(Gl p x-Gl p y)+(Gzl p x-Gzl p y)+(Gzr p x-Gzr p y) := by dsimp only [G]; ring
    rw [hid]
    refine norm_add₄_le.trans ?_
    have hh := add_le_add (add_le_add (add_le_add (lipr p x y) (lipl p x y)) (lipzl p x y)) (lipzr p x y)
    exact hh.trans_eq (by ring)
  · intro p x hx
    change ‖(Er p x+El p x+Ezl p x+Ezr p x)+short p x‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    have hh := add_le_add (norm_add₄_le.trans
      (add_le_add (add_le_add (add_le_add (remr p x) (reml p x)) (remzl p x)) (remzr p x))) (hshortB p x hx)
    exact hh.trans_eq (by ring)
  · intro p
    exact (norm_add_le (jl p) (jr p)).trans ((add_le_add (pinzl p) (pinzr p)).trans_eq (by ring))
  · intro p x
    exact (norm_add₄_le (a := Gr p x) (b := Gl p x) (c := Gzl p x) (d := Gzr p x)).trans
      ((add_le_add (add_le_add (add_le_add (normr p x) (norml p x)) (normzl p x)) (normzr p x)).trans_eq (by ring))

set_option maxHeartbeats 1200000 in
/-- Class-uniform short constants close the complete actual signed Green split. -/
theorem krInsertion_signed_full (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∃ cS KS : ℝ, 0 < cS ∧ 0 < KS ∧
    ∀ {X : Type*} [MeasurableSpace X] [Nonempty X] {K L w A : ℝ}
      (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {a : X → ℝ}
      (_ha : Measurable a) (_ha0 : ∀ p, 0 ≤ a p)
      (_H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) 1 (a p))
      (_hAw : A ≤ w) (up : Bool) {P : ℕ} (_hP : 12 ≤ P) (_hPw : (P : ℝ) ≤ w/8)
      {R : ℝ} (_hRw : R ≤ w/8) {ε : ℝ} (_hε0 : 0 ≤ ε) (_hε : ε ≤ krEps D vlo vhi)
      {v : (ℕ × ℕ) → X → ℝ} (_hv : ∀ q, Measurable (v q))
      (_hvb : ∀ q p, |v q p| ≤ Real.exp (ε*(q.1 : ℝ)/w^2)*Real.exp (ε*(q.2 : ℝ)/w^2)),
    let VB := 2*Real.exp (3*ε)*krCV D K L vlo vhi*(1+A)*(Real.sqrt w/krFourthRoot P+1)
    let RB := 2*Real.exp (5*ε)*krCR D K L vlo vhi*(1+A)*((1+kBVClassRho D vlo vhi)/2)^(P/3-1)
    let BB := Real.exp (3*ε)*((krCG D K L vlo vhi+4*krC₄ D K L/krKappa D vlo vhi)*(1+A)*(1+Real.log w))
    let OB := Real.exp (3*ε)*((krCO D K L vlo vhi+4*krC₃ D K L/krKappa D vlo vhi)*(1+A)*w)
    let PB := Real.exp (3*ε)*((krCP D θ K L vlo vhi+12*krC₂ D K L/krKappa D vlo vhi)*(1+A)^2/Real.sqrt w)
    let ST := ((P+1 : ℕ) : ℝ)^2*Real.exp (2*ε*(P : ℝ)/w^2)*(KS*Real.exp (-cS*w))
    (∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 → Summable fun q : ℕ × ℕ => v q p*
      kernelMarkedFullDens (Icc 0 w) ν f 1 (a p) x q.1 q.2 (if up then 0 else w) (if up then w else 0)) ∧
    ∃ G E : X → ℝ → ℂ, ∃ j : X → ℂ,
      Measurable (fun p : X × ℝ => G p.1 p.2) ∧
      Measurable (fun p : X × ℝ => E p.1 p.2) ∧ Measurable j ∧
      (∀ p x, x ∈ Icc 0 R → a p*x ≠ 1 →
        ((∑' q : ℕ × ℕ, v q p*kernelMarkedFullDens (Icc 0 w) ν f 1 (a p) x
          q.1 q.2 (if up then 0 else w) (if up then w else 0) : ℝ) : ℂ) =
        G p x+(if a p*x < 1 then j p else 0)+E p x) ∧
      (∀ p x y, ‖G p x-G p y‖ ≤ (4*VB*BB+8*D*VB)*|x-y|) ∧
      (∀ p x, x ∈ Icc 0 R → ‖E p x‖ ≤ 8*RB*OB+8*RB+ST) ∧
      (∀ p, ‖j p‖ ≤ 2*PB+8*RB) ∧ (∀ p x, ‖G p x‖ ≤ 2*VB*OB+4*VB) := by
  obtain ⟨cS,KS,hcS,hKS,hsmall⟩ := kernel_regLaw_full_marked_down_short D θ vlo vhi hD hθ hvlo hvhi
  refine ⟨cS,KS,hcS,hKS,?_⟩
  intro X _ _ K L w A ν f a ha ha0 H hAw up P hP hPw R hRw ε hε0 hε v hv hvb
  have H₀ := H (Classical.choice ‹Nonempty X›)
  have hwr : 2*R ≤ w := by linarith [H₀.hw0]
  apply krInsertion_signed_full_of_short ν ha ha0 H hAw up hP hwr hε0 hε hv hvb
  intro p x hx l r hl hr
  have halo : 1/2 ≤ a p := by simpa only [abs_of_nonneg (ha0 p)] using (H p).ha₁
  have hahi : a p ≤ 2 := (le_abs_self _).trans (H p).ha₂
  have hl' : (l : ℝ) ≤ P := by exact_mod_cast hl
  have hr' : (r : ℝ) ≤ P := by exact_mod_cast hr
  cases up with
  | false =>
    exact hsmall ν (H p).hν f (H p).hf (H p).hf0 (H p).hfz (H p).hfe (H p).hνf
      (a p) w x halo hahi H₀.hw0 hx.1 (hx.2.trans hRw) l r (by linarith)
  | true =>
    have hP' : (12 : ℝ) ≤ P := by exact_mod_cast hP
    have hz := kernel_full_marked_up_short_zero (w := w) (x := x) (H p).hν hθ hvlo (H p).hfz
      (by linarith : 0 < a p) hx.1 l r (by linarith)
    change kernelMarkedFullDens (Icc 0 w) ν f 1 (a p) x l r 0 w ≤ _
    rw [hz]
    positivity

end
end PGM
