import PLAStochastic.Index.GEP.Kernel.Insertion.ZeroSideSeries
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # Exact disjoint partition of all marked insertion lengths -/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

abbrev KrInsertionPieces (P : ℕ) :=
  (Fin (P+1) × Fin (P+1)) ⊕ ℕ ⊕ ℕ ⊕ (ℕ × ℕ) ⊕ (Fin P × ℕ)

def krInsertionPieceMap (P : ℕ) : KrInsertionPieces P → ℕ × ℕ
  | .inl q => (q.1, q.2)
  | .inr (.inl i) => (0, P+1+i)
  | .inr (.inr (.inl i)) => (P+1+i, 0)
  | .inr (.inr (.inr (.inl q))) => (q.1+1, P+1+q.2)
  | .inr (.inr (.inr (.inr q))) => (P+1+q.2, q.1+1)

theorem krInsertionPieceMap_injective (P : ℕ) : Function.Injective (krInsertionPieceMap P) := by
  rintro (⟨l,r⟩ | i | i | ⟨l,i⟩ | ⟨r,i⟩) (⟨l',r'⟩ | j | j | ⟨l',j⟩ | ⟨r',j⟩) he
  all_goals simp only [krInsertionPieceMap, Prod.mk.injEq] at he
  all_goals first | (exfalso; omega) | (congr <;> ext <;> omega) | (congr <;> omega)

theorem krInsertionPieceMap_surjective (P : ℕ) : Function.Surjective (krInsertionPieceMap P) := by
  rintro ⟨l,r⟩
  by_cases hr : r ≤ P
  · by_cases hl : l ≤ P
    · refine ⟨.inl (⟨l,by omega⟩,⟨r,by omega⟩), rfl⟩
    · by_cases hr0 : r=0
      · refine ⟨.inr (.inr (.inl (l-(P+1)))), ?_⟩
        simp only [krInsertionPieceMap,Prod.mk.injEq]
        omega
      · refine ⟨.inr (.inr (.inr (.inr (⟨r-1,by omega⟩,l-(P+1))))), ?_⟩
        simp only [krInsertionPieceMap,Prod.mk.injEq]
        omega
  · by_cases hl0 : l=0
    · refine ⟨.inr (.inl (r-(P+1))), ?_⟩
      simp only [krInsertionPieceMap,Prod.mk.injEq]
      omega
    · refine ⟨.inr (.inr (.inr (.inl (l-1,r-(P+1))))), ?_⟩
      simp only [krInsertionPieceMap,Prod.mk.injEq]
      omega

def krInsertionPieceEquiv (P : ℕ) : KrInsertionPieces P ≃ ℕ × ℕ :=
  Equiv.ofBijective (krInsertionPieceMap P)
    ⟨krInsertionPieceMap_injective P,krInsertionPieceMap_surjective P⟩

theorem krInsertion_sum_partition {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    (F : ℕ × ℕ → 𝕜) (P : ℕ)
    (hzl : Summable fun i => F (0,P+1+i))
    (hzr : Summable fun i => F (P+1+i,0))
    (hlr : Summable fun q : ℕ × ℕ => F (q.1+1,P+1+q.2))
    (hll : Summable fun q : Fin P × ℕ => F (P+1+q.2,q.1+1)) :
    Summable F ∧
      ∑' q, F q = (∑ q : Fin (P+1) × Fin (P+1), F (q.1,q.2)) +
        (∑' i, F (0,P+1+i)) + (∑' i, F (P+1+i,0)) +
        (∑' q : ℕ × ℕ, F (q.1+1,P+1+q.2)) +
        (∑' q : Fin P × ℕ, F (P+1+q.2,q.1+1)) := by
  have hp : HasSum (fun q : KrInsertionPieces P => F (krInsertionPieceMap P q))
      ((∑ q : Fin (P+1) × Fin (P+1), F (q.1,q.2)) +
        ((∑' i, F (0,P+1+i)) + ((∑' i, F (P+1+i,0)) +
          ((∑' q : ℕ × ℕ, F (q.1+1,P+1+q.2)) +
            (∑' q : Fin P × ℕ, F (P+1+q.2,q.1+1)))))) :=
    (hasSum_fintype (fun q : Fin (P+1) × Fin (P+1) => F (q.1,q.2))).sum
      (hzl.hasSum.sum (hzr.hasSum.sum (hlr.hasSum.sum hll.hasSum)))
  have hmain := (krInsertionPieceEquiv P).hasSum_iff.mp hp
  exact ⟨hmain.summable,hmain.tsum_eq.trans (by abel)⟩

theorem krInsertion_mask_finite {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    (F : ℕ × ℕ → 𝕜) (P : ℕ)
    (hm : Summable fun q : ℕ × ℕ => if q.1 < P then F q else 0) :
    Summable (fun q : Fin P × ℕ => F (q.1,q.2)) ∧
      (∑' q : Fin P × ℕ, F (q.1,q.2)) =
        ∑' q : ℕ × ℕ, if q.1 < P then F q else 0 := by
  let e : Fin P × ℕ → ℕ × ℕ := fun q => (q.1,q.2)
  have hei : Function.Injective e := by
    intro x y he
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst he)
    · exact congrArg (fun q : ℕ × ℕ => q.2) he
  have hz : ∀ q : ℕ × ℕ, q ∉ range e → (if q.1 < P then F q else 0) = 0 := by
    intro q hq
    have hn : ¬ q.1 < P := by
      intro hp
      exact hq ⟨(⟨q.1,hp⟩,q.2),rfl⟩
    rw [if_neg hn]
  have ht := (hei.hasSum_iff hz).mpr hm.hasSum
  have ht' : HasSum (fun q : Fin P × ℕ => F (q.1,q.2))
      (∑' q : ℕ × ℕ, if q.1 < P then F q else 0) := by
    exact ht.congr (fun q => by simp [e])
  exact ⟨ht'.summable,ht'.tsum_eq⟩

end
end PGM
