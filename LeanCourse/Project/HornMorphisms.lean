import LeanCourse.Common
-- import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.Quasicategory


open CategoryTheory Simplicial
open SSet
open SimplexCategory
open Simplicial
open Opposite


noncomputable section

-- here we define a morphism from the nth standard simplex to a simplicial set S by giving its image on the "interior" element in Δ[n] _n

namespace SSet

def hom_by_interior {S : SSet} {n : ℕ} (σ : S _[n]) : Δ[n] ⟶ S where
  app m := by{
    intro f
    use S.map (SimplexCategory.mkHom f.toOrderHom).op (σ)
  }
  naturality := by{
    intro k m f
    simp
    refine (types_ext ((fun f ↦ S.map f.op σ) ≫ S.map f) (Δ[n].map f ≫ fun f ↦ S.map f.op σ) ?h).symm
    intro b
    simp
    rw [← @FunctorToTypes.map_comp_apply]
    simp
    rw[(FunctorToTypes.map_comp_apply S b.op f σ).symm]
    exact rfl
  }

-- we can define a morphism from a horn by just giving the image on suitable faces

def hom_by_faces_1th_3horn {S : SSet} [Quasicategory S] (σ : Fin (4) → S _[2]) (compatible : S.map (δ 2).op (σ 3) = S.map (δ 2).op (σ 2) ∧ S.map (δ 0).op (σ 3) = S.map (δ 2).op (σ 0) ∧ S.map (δ 0).op (σ 2) = S.map (δ 1).op (σ 0)): Λ[3,1] ⟶ S where
  app m := by{
    intro f
    have h : ∃ j : Fin (4), (¬j = 1 ∧ ∀ k, f.1.toOrderHom k ≠ j) := by{
      simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or] using f.2
    }
    let j := Classical.choose h
    have hj : ¬j = 1 := (Classical.choose_spec h).1
    have hji : ∀ k, f.1.toOrderHom k ≠ j := (Classical.choose_spec h).2
    have H : f = (Λ[2+1, 1].map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op) (horn.face 1 j hj) := by
      apply Subtype.ext
      exact (factor_δ_spec (SimplexCategory.mkHom f.1.toOrderHom) j hji).symm
    use S.map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op (σ j)
  }
  naturality := by{
    intro l m f
    simp
    sorry
  }

def hom_by_faces_2th_3horn {S : SSet} [Quasicategory S] (σ : Fin (4) → S _[2]) (compatible : S.map (δ 0).op (σ 3) = S.map (δ 2).op (σ 0) ∧ S.map (δ 1).op (σ 3) = S.map (δ 2).op (σ 1) ∧ S.map (δ 0).op (σ 1) = S.map (δ 0).op (σ 0)) : Λ[3,2] ⟶ S where
  app m := by{
    intro f
    have h : ∃ j : Fin (4), (¬j = 2 ∧ ∀ k, f.1.toOrderHom k ≠ j) := by{
      simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or] using f.2
    }
    let j := Classical.choose h
    have hj : ¬j = 2 := (Classical.choose_spec h).1
    have hji : ∀ k, f.1.toOrderHom k ≠ j := (Classical.choose_spec h).2
    have H : f = (Λ[2+1, 2].map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op) (horn.face 2 j hj) := by
      apply Subtype.ext
      exact (factor_δ_spec (SimplexCategory.mkHom f.1.toOrderHom) j hji).symm
    use S.map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op (σ j)
  }
  naturality := by{
    intro l m f
    simp
    sorry
  }

-- define `hom_by_faces` in more generality

-- in the following definition, the compatibility condition is still missing `(compatible : S.map (δ 2 2) (σ 3) = S.map (δ 2 2) (σ 2) etc.)` but it's more difficult to state this (finitely) in the general case
-- this condition is necessary to prove naturality

def hom_by_faces {S : SSet} [Quasicategory S] {n : ℕ} {i : Fin (n+1)} (σ : Fin (n+2) → S _[n]) : Λ[n+1,i] ⟶ S where
  app m := by{
    intro f
    have h : ∃ j, (¬j = Fin.castSucc i ∧ ∀ k, f.1.toOrderHom k ≠ j) := by{
      simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or] using f.2
    }
    let h₁ : Set.Nonempty {j : Fin (n+1+1) | ¬j = Fin.castSucc i ∧ ∀ k, f.1.toOrderHom k ≠ j} := h
    let h₂ : Set.IsWF {j : Fin (n+1+1) | ¬j = Fin.castSucc i ∧ ∀ k, f.1.toOrderHom k ≠ j} := by sorry
    let j := Set.IsWF.min h₂ h₁
    have hj : j ≠ Fin.castSucc i := sorry
    have hj' : j ≠ (@Nat.cast (Fin (n+2)) Semiring.toNatCast i) := by sorry
    have hji : ∀ k, f.1.toOrderHom k ≠ j := sorry
    have H : f = (Λ[n+1, i].map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op) (horn.face i j hj') := by
      apply Subtype.ext
      exact (factor_δ_spec (SimplexCategory.mkHom f.1.toOrderHom) j hji).symm
    use S.map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op (σ j)
  }
  naturality := by{
    intro l m f
    sorry
  }

-- some lemmata and constructions that I shouldn't need
def makefunction {S : SSet} (σ₀ σ₁ σ₂ σ₃ : S _[2]) : Fin (4) → (S _[2])
  | 0 => σ₀
  | 1 => σ₁
  | 2 => σ₂
  | 3 => σ₃

lemma temp02 {n} : @OfNat.ofNat (Fin (n + 1)) 0 Fin.instOfNatFin ≤ 2 := sorry
lemma temp12 {n} : @OfNat.ofNat (Fin (n + 1)) 1 Fin.instOfNatFin ≤ 2 := sorry
lemma temp23 {n} : @OfNat.ofNat (Fin (n + 1)) 2 Fin.instOfNatFin ≤ 3 := sorry
lemma neq01 {n} : @OfNat.ofNat (Fin (n + 1)) 0 Fin.instOfNatFin ≠ 1 := sorry

lemma hom_by_faces_13_works_fine_0 {S : SSet} [Quasicategory S] (σ : Fin (4) → S _[2]) (compatible : S.map (δ 2).op (σ 3) = S.map (δ 2).op (σ 2) ∧ S.map (δ 0).op (σ 3) = S.map (δ 2).op (σ 0) ∧ S.map (δ 0).op (σ 2) = S.map (δ 1).op (σ 0)) : (hom_by_faces_1th_3horn σ compatible).app (op (SimplexCategory.mk 2)) (horn.face 1 0 neq01) = σ 0 := by{
  have e : ∃ j : Fin (4), (¬j = 1 ∧ ∀ k, (horn.face 1 0 neq01).1.toOrderHom k ≠ j) := by{
    use 0
    constructor
    · exact neq01
    · intro k
      exact (bne_iff_ne ((Hom.toOrderHom (horn.face 1 0 neq01).1) k) 0).mp rfl
  }
  let j := Classical.choose e
  have j0 : j = 0 := by sorry -- j is indeed unique and is zero, but it might be tedious to show
  have e2 : (¬0 = 1 ∧ ∀ (k : Fin (len (SimplexCategory.mk 2))), (horn.face 1 0 neq01).1.toOrderHom k ≠ 0) := by{
    constructor
    · exact Nat.zero_ne_one
    · intro k
      exact (bne_iff_ne ((Hom.toOrderHom (horn.face 1 0 neq01).1) k) 0).mp rfl
  }
  have h : (hom_by_faces_1th_3horn σ compatible).app (op [2]) (horn.face 1 0 neq01) = S.map (factor_δ (SimplexCategory.mkHom (horn.face 1 0 neq01).1.toOrderHom) j).op (σ j) := by {
    exact rfl
  }
  rw[h]
  rw[j0]
  simp
  have hid : (factor_δ (δ 0) 0).op = op (SimplexCategory.Hom.id [2]) := by sorry -- something hom_ext?
  rw[hid]
  have h2id : S.map (op (SimplexCategory.Hom.id [2])) = 𝟙 (S _[2]) := by sorry -- should be possible to find
  rw[h2id]
  exact rfl
}


end SSet
