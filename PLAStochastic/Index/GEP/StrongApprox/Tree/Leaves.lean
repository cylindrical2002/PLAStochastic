import PLAStochastic.Index.GEP.StrongApprox.Tree.SharedNoise

/-! # Flattening the dyadic product into an actual finite iid leaf vector -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Function
open scoped ENNReal

/-- Recursive left/right leaf addresses. -/
def SATreeIndex : ℕ → Type
  | 0 => PUnit
  | J + 1 => SATreeIndex J ⊕ SATreeIndex J

instance instFintypeSATreeIndex (J : ℕ) : Fintype (SATreeIndex J) := by
  induction J with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ J ih =>
    letI := ih
    exact inferInstanceAs (Fintype (SATreeIndex J ⊕ SATreeIndex J))

/-- Flatten the nested pair of leaves to its coordinate function. -/
def saTreeFlatten : (J : ℕ) → SATreeValues J → SATreeIndex J → ℝ
  | 0, x, _ => x
  | J + 1, x, Sum.inl i => saTreeFlatten J x.1 i
  | J + 1, x, Sum.inr i => saTreeFlatten J x.2 i

theorem measurable_saTreeFlatten (J : ℕ) : Measurable (saTreeFlatten J) := by
  induction J with
  | zero => exact measurable_pi_lambda _ fun _ => measurable_id
  | succ J ih =>
    apply measurable_pi_lambda
    intro i
    cases i with
    | inl i => exact (measurable_pi_apply i).comp (ih.comp measurable_fst)
    | inr i => exact (measurable_pi_apply i).comp (ih.comp measurable_snd)

/-- The leaf-coordinate law is the finite iid product measure. -/
theorem saTreeFlatten_leafLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (J : ℕ) :
    (saTreeLeafLaw μ J).map (saTreeFlatten J) = Measure.pi (fun _ : SATreeIndex J => μ) := by
  induction J with
  | zero =>
    have he := (measurePreserving_piUnique (fun _ : PUnit => μ)).symm.map_eq
    exact he
  | succ J ih =>
    have he := (measurePreserving_sumPiEquivProdPi_symm
      (fun _ : SATreeIndex J ⊕ SATreeIndex J => μ)).map_eq
    rw [← ih, map_prod_map _ _ (measurable_saTreeFlatten J) (measurable_saTreeFlatten J)] at he
    rw [Measure.map_map (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)).symm.measurable
      ((measurable_saTreeFlatten J).prodMap (measurable_saTreeFlatten J))] at he
    have hfun : saTreeFlatten (J + 1) =
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : SATreeIndex J ⊕ SATreeIndex J => ℝ)).symm ∘
          Prod.map (saTreeFlatten J) (saTreeFlatten J) := by
      funext x i
      cases i <;> rfl
    rw [hfun]
    exact he

/-- Recursive addresses have exactly `2^J` leaves. -/
theorem card_saTreeIndex (J : ℕ) : Fintype.card (SATreeIndex J) = 2 ^ J := by
  induction J with
  | zero => rfl
  | succ J ih =>
    change Fintype.card (SATreeIndex J ⊕ SATreeIndex J) = _
    rw [Fintype.card_sum, ih, pow_succ]
    omega

/-- Flattening the random tree reconstructs the actual iid coordinate law. -/
theorem saTreeRun_flatten_law {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J : ℕ) :
    (((hp J).law : Measure ℝ).prod (saTreeNoiseLaw J)).map
      (fun z => saTreeFlatten J (saTreeRun hp J z.1 z.2)) =
        Measure.pi (fun _ : SATreeIndex J => (hp 0).law) := by
  rw [← saTreeFlatten_leafLaw ((hp 0).law : Measure ℝ) J, ← saTreeRun_law hp hstep J,
    Measure.map_map (measurable_saTreeFlatten J) (measurable_saTreeRun hp J)]
  rfl

/-- The standard left-to-right numbering of the recursive leaf addresses. -/
def saTreeIndexEquivFin : (J : ℕ) → SATreeIndex J ≃ Fin (2 ^ J)
  | 0 => (Equiv.equivPUnit (Fin 1)).symm
  | J + 1 => ((Equiv.sumCongr (saTreeIndexEquivFin J) (saTreeIndexEquivFin J)).trans
      finSumFinEquiv).trans (finCongr (by rw [pow_succ]; omega))

/-- A conventional `Fin (2^J)` leaf vector, in left-to-right order. -/
def saTreeFlattenFin (J : ℕ) (x : SATreeValues J) (i : Fin (2 ^ J)) : ℝ :=
  saTreeFlatten J x ((saTreeIndexEquivFin J).symm i)

theorem measurable_saTreeFlattenFin (J : ℕ) : Measurable (saTreeFlattenFin J) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply _).comp (measurable_saTreeFlatten J)

theorem saTreeFlattenFin_leafLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (J : ℕ) :
    (saTreeLeafLaw μ J).map (saTreeFlattenFin J) = Measure.pi (fun _ : Fin (2 ^ J) => μ) := by
  have he := Measure.pi_map_piCongrLeft (saTreeIndexEquivFin J) (fun _ : Fin (2 ^ J) => μ)
  rw [← saTreeFlatten_leafLaw μ J, Measure.map_map
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 ^ J) => ℝ) (saTreeIndexEquivFin J)).measurable
    (measurable_saTreeFlatten J)] at he
  have hfun : saTreeFlattenFin J =
      MeasurableEquiv.piCongrLeft (fun _ : Fin (2 ^ J) => ℝ) (saTreeIndexEquivFin J) ∘
        saTreeFlatten J := by
    funext x i
    obtain ⟨j, rfl⟩ := (saTreeIndexEquivFin J).surjective i
    rw [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
    simp [saTreeFlattenFin]
  rw [hfun]
  exact he

theorem saTreeFlatten_sum (J : ℕ) (x : SATreeValues J) :
    (∑ i : SATreeIndex J, saTreeFlatten J x i) = saTreeSum J x := by
  induction J with
  | zero =>
    change ℝ at x
    change (∑ _ : PUnit, x) = x
    simp only [Finset.univ_unique, Finset.sum_singleton]
  | succ J ih =>
    calc
      _ = ∑ i : SATreeIndex J ⊕ SATreeIndex J,
          Sum.elim (saTreeFlatten J x.1) (saTreeFlatten J x.2) i := by
        congr 1
        funext i
        cases i <;> rfl
      _ = saTreeSum J x.1 + saTreeSum J x.2 := by
        rw [Fintype.sum_sum_type]
        exact congrArg₂ (· + ·) (ih x.1) (ih x.2)
      _ = _ := rfl

theorem saTreeFlattenFin_sum (J : ℕ) (x : SATreeValues J) :
    (∑ i : Fin (2 ^ J), saTreeFlattenFin J x i) = saTreeSum J x := by
  change (∑ i : Fin (2 ^ J), saTreeFlatten J x ((saTreeIndexEquivFin J).symm i)) = _
  rw [(saTreeIndexEquivFin J).symm.sum_comp]
  exact saTreeFlatten_sum J x

/-- The common-uniform tree has a genuine iid finite-vector marginal. -/
theorem saTreeFromUniform_flattenFin_law {p : ℕ → ℝ → ℝ} (hp : ∀ j, SADensity (p j))
    (hstep : ∀ j, ((hp (j + 1)).law : Measure ℝ) = ((hp j).sumDensity.law : Measure ℝ))
    (J : ℕ) :
    (saTreeSharedLaw J).map (fun z => saTreeFlattenFin J (saTreeFromUniform hp J z)) =
      Measure.pi (fun _ : Fin (2 ^ J) => (hp 0).law) := by
  rw [← saTreeFlattenFin_leafLaw ((hp 0).law : Measure ℝ) J, ← saTreeFromUniform_law hp hstep J,
    Measure.map_map (measurable_saTreeFlattenFin J) (measurable_saTreeFromUniform hp J)]
  rfl

end

end PGM
