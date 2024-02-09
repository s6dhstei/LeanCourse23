import LeanCourse.Common
import Mathlib.AlgebraicTopology.Quasicategory
import LeanCourse.Project.AuxiliaryLemmas


open CategoryTheory Simplicial
open SSet
open SimplexCategory
open Simplicial
open Opposite


noncomputable section

/-
# Definition of morphisms between Simplicial Sets

In this file, we define morphisms from the Simplicial Sets `Δ[n]` and `Λ[3, i]` to any Simplicial Set `S`.

I managed to give a full definition (including naturality) of a morphism from the standard Simplex `Δ[n]` to `S`.
For the most interesting cases of morphisms from the inner `3`-horns `Λ[3,1]` and `Λ[3,2]`, I define a morphism for given elements in `S _[2]` that satisfy a compatibility condition, but the proof for the naturality (which has to use the compatibility condition) is missing.
For the general case of morphisms from any horn `Λ[n,i]`, I give a definition, but compatibility condition and naturality are missing.

Then I give lemmas to state that the morphisms from the `1`th `3`-horns satisfy the condition that they were defined for. These lemmas are each missing one technical detail.
-/


-- ## Defining a morphism from the nth standard simplex to a simplicial set S by giving its image on the "interior" element in Δ[n] _n

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


/-
## Defining a morphism from a horn to a simplicial set S by giving the image on suitable faces
-- Three elements of `S _[2]` can only be the image of the three non-degenerate faces of an `i`th `3`-horn if they agree along the three edges that have `1` as an endpoint.
-- Only in this case, we can use them to define a morphism `Λ[3,1] → S`.
-- Elements `σ0, σ2, σ` of `S _[2]` are called `horn1_compatible` if they are compatible with the structure maps `δ` of `S`:
-/

def horn1_compatible {S : SSet} (σ0 σ2 σ3 : S _[2]) : Prop := S.map (δ 2).op (σ3) = S.map (δ 2).op (σ2) ∧ S.map (δ 0).op (σ3) = S.map (δ 2).op (σ0) ∧ S.map (δ 0).op (σ2) = S.map (δ 1).op (σ0)


-- We define a morphism from a horn `Λ[3,1]` to `S` by giving the image on the three non-degenerate faces:

def hom_by_faces_1th_3horn {S : SSet} (σ : Fin (4) → S _[2]) (h : horn1_compatible (σ 0) (σ 2) (σ 3)) : Λ[3,1] ⟶ S where
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


-- Similarly, three elements of `S _[2]` are called `horn2_compatible` if they agree along the three edges that have `2` as an endpoint:

def horn2_compatible {S : SSet} (σ0 σ1 σ3 : S _[2]) : Prop := S.map (δ 0).op (σ3) = S.map (δ 2).op (σ0) ∧ S.map (δ 1).op (σ3) = S.map (δ 2).op (σ1) ∧ S.map (δ 0).op (σ1) = S.map (δ 0).op (σ0)


-- We define a morphism from a horn `Λ[3,2]` to `S` by giving the image on the three faces:

def hom_by_faces_2th_3horn {S : SSet} [Quasicategory S] (σ : Fin (4) → S _[2]) (h : horn2_compatible (σ 0) (σ 1) (σ 3)) : Λ[3,2] ⟶ S where
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


-- Defining `hom_by_faces` in more generality

-- In the following definition, the compatibility condition is still missing because it is more difficult to even state it (in a finite expression) in the general case.
-- This condition would be necessary to prove naturality


def hom_by_faces {S : SSet} [Quasicategory S] {n : ℕ} {i : Fin (n+1)} (σ : Fin (n+2) → S _[n]) : Λ[n+1,i] ⟶ S where
  app m := by{
    intro f
    have h : ∃ j, (¬j = Fin.castSucc i ∧ ∀ k, f.1.toOrderHom k ≠ j) := by{
      simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or] using f.2
    }
    let j := Classical.choose h
    have hj : j ≠ Fin.castSucc i := (Classical.choose_spec h).1
    have hjj : @Ne (Fin (n + 2)) j ↑↑i := sorry -- a 'cast'ing issue
    have hji : ∀ k, f.1.toOrderHom k ≠ j := (Classical.choose_spec h).2
    have H : f = (Λ[n+1, i].map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op) (horn.face i j hjj) := by
      apply Subtype.ext
      exact (factor_δ_spec (SimplexCategory.mkHom f.1.toOrderHom) j hji).symm
    use S.map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op (σ j)
  }
  naturality := by{
    intro l m f
    sorry
  }


-- The following lemmas serve to access the defining property of the morphisms from the `Λ[3,1]`-horn we just defined.
-- Given three elements `σ0, σ2, σ3` of `S _[2]`, the faces of `Λ[3,1]` are indeed sent to `σ0, σ2` and `σ3` respectively.

lemma hom_by_faces_13_works_fine_0 {S : SSet} [Quasicategory S] (σ : Fin (4) → S _[2]) (compatible : horn1_compatible (σ 0) (σ 2) (σ 3)) : (hom_by_faces_1th_3horn σ compatible).app (op (SimplexCategory.mk 2)) (horn.face 1 0 neq01) = σ 0 := by{
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
  have hid : (factor_δ (δ 0) 0).op = op (SimplexCategory.Hom.id [2]) := by {
    apply eq_if_op_eq
    refine Hom.ext' (factor_δ (δ 0) 0) (Hom.id [2]) ?_
    refine OrderHom.ext (Hom.toOrderHom (factor_δ (δ 0) 0)) (Hom.toOrderHom (Hom.id [2])) ?_
    exact List.ofFn_inj.mp rfl
  }
  rw[hid]
  rw[id_2_S]
  exact rfl
}


lemma hom_by_faces_13_works_fine_2 {S : SSet} [Quasicategory S] (σ : Fin (4) → S _[2]) (compatible : horn1_compatible (σ 0) (σ 2) (σ 3)) : (hom_by_faces_1th_3horn σ compatible).app (op (SimplexCategory.mk 2)) (horn.face 1 2 neq12.symm) = σ 2 := by{

  have e : ∃ j : Fin (4), (¬j = 1 ∧ ∀ k, (horn.face 1 2 neq12.symm).1.toOrderHom k ≠ j) := by{
    use 2
    constructor
    · exact neq12.symm
    · intro k
      apply (bne_iff_ne ((Hom.toOrderHom (horn.face 1 2 neq12.symm).1) k) 2).mp
      simp[δ]
      exact Fin.succAbove_ne 2 k
  }
  let j := Classical.choose e
  have j2 : j = 2 := by sorry
  have e2 : (¬2 = 1 ∧ ∀ (k : Fin (len (SimplexCategory.mk 2))), (horn.face 1 2 neq12.symm).1.toOrderHom k ≠ 2) := by{
    constructor
    · exact Nat.succ_succ_ne_one 0
    · intro k
      apply (bne_iff_ne ((Hom.toOrderHom (horn.face 1 2 neq12.symm).1) k) 2).mp
      simp[δ]
      exact Fin.succAbove_ne 2 k
      }
  have h : (hom_by_faces_1th_3horn σ compatible).app (op [2]) (horn.face 1 2 neq12.symm) = S.map (factor_δ (SimplexCategory.mkHom (horn.face 1 2 neq12.symm).1.toOrderHom) j).op (σ j) := by {
    exact rfl
  }
  rw[h]
  rw[j2]
  simp
  have hid : (factor_δ (δ 2) 2).op = op (SimplexCategory.Hom.id [2]) := by {
    apply eq_if_op_eq
    refine Hom.ext' (factor_δ (δ 2) 2) (Hom.id [2]) ?_
    refine OrderHom.ext (Hom.toOrderHom (factor_δ (δ 2) 2)) (Hom.toOrderHom (Hom.id [2])) ?_
    exact List.ofFn_inj.mp rfl
  }
  rw[hid]
  rw[id_2_S]
  exact rfl

}


lemma hom_by_faces_13_works_fine_3 {S : SSet} [Quasicategory S] (σ : Fin (4) → S _[2]) (compatible : horn1_compatible (σ 0) (σ 2) (σ 3)) : (hom_by_faces_1th_3horn σ compatible).app (op (SimplexCategory.mk 2)) (horn.face 1 3 neq13.symm) = σ 3 := by{
  have e : ∃ j : Fin (4), (¬j = 1 ∧ ∀ k, (horn.face 1 3 neq13.symm).1.toOrderHom k ≠ j) := by{
    use 3
    constructor
    · exact neq13.symm
    · intro k
      apply (bne_iff_ne ((Hom.toOrderHom (horn.face 1 3 neq13.symm).1) k) 3).mp
      simp[δ]
      exact Fin.succAbove_ne 3 k  }
  let j := Classical.choose e
  have j3 : j = 3 := by sorry
  have e2 : (¬3 = 1 ∧ ∀ (k : Fin (len (SimplexCategory.mk 2))), (horn.face 1 3 neq13.symm).1.toOrderHom k ≠ 3) := by{
    constructor
    · exact Nat.succ_succ_ne_one 1
    · intro k
      exact (bne_iff_ne ((Hom.toOrderHom (horn.face 1 0 neq01).1) k) 0).mp rfl
  }
  have h : (hom_by_faces_1th_3horn σ compatible).app (op [2]) (horn.face 1 3 neq13.symm) = S.map (factor_δ (SimplexCategory.mkHom (horn.face 1 3 neq13.symm).1.toOrderHom) j).op (σ j) := by {
    exact rfl
  }
  rw[h]
  rw[j3]
  simp
  have hid : (factor_δ (δ 3) 3).op = op (SimplexCategory.Hom.id [2]) := by
    apply eq_if_op_eq
    refine Hom.ext' (factor_δ (δ 3) 3) (Hom.id [2]) ?_
    refine OrderHom.ext (Hom.toOrderHom (factor_δ (δ 3) 3)) (Hom.toOrderHom (Hom.id [2])) ?_
    exact List.ofFn_inj.mp rfl
  rw[hid]
  rw[id_2_S]
  exact rfl
}


-- Similar lemmas would be needed for `hom_by_faces_2th_3horn`, I did not have the time to prove them

lemma hom_by_faces_23_works_fine_3 {S : SSet} [Quasicategory S] (σ : Fin (4) → S _[2]) (compatible : horn2_compatible (σ 0) (σ 1) (σ 3)) : (hom_by_faces_2th_3horn σ compatible).app (op (SimplexCategory.mk 2)) (horn.face 2 3 neq23.symm) = σ 3 := sorry


end SSet


-- Note: in the `hom_by_faces_13_works_fine_i` lemmas, the `ji` for `i = 0, 2, 3` are missing; they could be proved by case distinction using the definition of `(horn.face _ _ _).toOrderHom`.
