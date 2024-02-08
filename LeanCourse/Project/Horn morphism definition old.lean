import LeanCourse.Common
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.Quasicategory


open CategoryTheory Simplicial
open SSet
open SimplexCategory
open Simplicial
open Opposite


noncomputable section

-- here we define a morphism from the nth standard simplex to a simplicial set S by giving its image on the "interior" element in Δ[n] _n

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
    let h₁ : Set.Nonempty {j : Fin (4) | ¬j = 1 ∧ ∀ k, f.1.toOrderHom k ≠ j} := by exact h
--    let h₂ : Set.IsWF {j : Fin (4) | ¬j = 1 ∧ ∀ k, f.1.toOrderHom k ≠ j} := by sorry -- Fin (4) is well-founded! But apparently it is not a Set
    let j := Classical.choose h
    have hj : ¬j = 1 := (Classical.choose_spec h).1
    have hji : ∀ k, f.1.toOrderHom k ≠ j := (Classical.choose_spec h).2
    let f₁ := f.1
    have H : f = (Λ[2+1, 1].map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op) (horn.face 1 j hj) := by
      apply Subtype.ext
      exact (factor_δ_spec (SimplexCategory.mkHom f.1.toOrderHom) j hji).symm
    use S.map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op (σ j)
  }
  naturality := by{
    intro l m f
    simp
    sorry
--    refine types_ext ((fun f ↦ S.map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op (σ j)) ≫ S.map f)
  }

-- in the following definition, the compatibility condition is still missing `(compatible : S.map (δ 2 2) (σ 3) = S.map (δ 2 2) (σ 2) etc.)` because of type mismatches that I don't understand
-- this condition will be necessary to prove naturality

def hom_by_faces_2th_3horn {S : SSet} [Quasicategory S] (σ : Fin (4) → S _[2]) : Λ[3,2] ⟶ S where
  app m := by{
    intro f
    have h : ∃ j : Fin (4), (¬j = 2 ∧ ∀ k, f.1.toOrderHom k ≠ j) := by{
      simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or] using f.2
    }
    let h₁ : Set.Nonempty {j : Fin (4) | ¬j = 2 ∧ ∀ k, f.1.toOrderHom k ≠ j} := by exact h
    let h₂ : Set.IsWF {j : Fin (4) | ¬j = 2 ∧ ∀ k, f.1.toOrderHom k ≠ j} := by sorry
    let j := Set.IsWF.min h₂ h₁
    have hj : ¬j = 2 := sorry
    have hji : ∀ k, f.1.toOrderHom k ≠ j := sorry
    let f₁ := f.1
    have H : f = (Λ[2+1, 2].map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op) (horn.face 2 j hj) := by
      apply Subtype.ext
      exact (factor_δ_spec (SimplexCategory.mkHom f.1.toOrderHom) j hji).symm
    use S.map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op (σ j)
  }
  naturality := by{
    intro l m f
    sorry
  }

-- define `hom_by_faces` in more generality

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


#check horn.hom_ext
