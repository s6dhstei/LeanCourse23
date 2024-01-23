import LeanCourse.Common
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.Quasicategory



open CategoryTheory Simplicial
open SSet
open SimplexCategory
open Simplicial
open Opposite


#check Quasicategory

/-
1. We introduce some basic notions for the lower dimensions of a quasi-category:
* homotopies between "morphisms", i.e. elements of S₁
-/

variable (S : SSet) [Quasicategory S]
variable (n : Nat)
variable (f g : S _[1])
#check S.obj (op [n])
-- more convenient notation for this:
#check S _[n]
#check (δ 4)
#check δ

#check S.map (SimplexCategory.δ 0).op
-- for some reason the definition from SimplicialObject, l.87 doesn't work well, so I introduce new notations for the face and degeneracy maps


/-
some horn calculations
-/
open SimplexCategory

def const (n : ℕ) {p : 0 < n} (j k : Fin (n+1)) (m : SimplexCategoryᵒᵖ) : Λ[n,j].obj m := by{
  let a : Δ[n].obj m := Hom.mk <| OrderHom.const _ k
  have h : Set.range (asOrderHom a) ∪ {j} ≠ Set.univ := by {
    have h₁ : ∀ z ∈ Set.range ⇑(asOrderHom a), z = k := by
      simp only [len_mk, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
      intro b
      rfl
    have h₂ : Set.range ⇑(asOrderHom a) = {k} := by
      apply Set.Subset.antisymm h₁ ?h₂
      apply Set.singleton_subset_iff.mpr ?h₂.a
      apply Set.mem_range.mpr ?h₂.a.a
      use 0
      rfl
    have h₃ : Set.range ⇑(asOrderHom a) ∪ {j}= {k} ∪ {j} := congrFun (congrArg Union.union h₂) {j}
    have h₄ : Set.range (asOrderHom a) ∪ {j} < Set.univ := by
      refine LT.lt.ssubset ?_
      simp only [len_mk, Set.union_singleton, Set.lt_eq_ssubset]
      -- so in Set.range (asOrderHom a) ∪ {j} there are at most 2 elements but Fin(n+1)=Set.univ has at least 3
      -- I don't know how cardinality of a finite set is called in Lean and I don't want to deal with it
      -- (there is card for Finset)
      sorry
    exact Set.ssubset_univ_iff.mp h₄
  }
  use a

}


#check asOrderHom

noncomputable section
-- (only because of the "well-founded"- why is it such an issue? should I try to avoid noncomputable?)


-- we can define a morphism from a horn by just giving the image on suitable faces

def hom_by_faces_1th_3horn {S : SSet} [Quasicategory S] (σ : Fin (4) → S _[2]) : Λ[3,1] ⟶ S where
  app m := by{
    intro f
    have h : ∃ j : Fin (4), (¬j = 1 ∧ ∀ k, f.1.toOrderHom k ≠ j) := by{
      simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or] using f.2
    }
    let h₁ : Set.Nonempty {j : Fin (4) | ¬j = 1 ∧ ∀ k, f.1.toOrderHom k ≠ j} := by exact h
    let h₂ : Set.IsWF {j : Fin (4) | ¬j = 1 ∧ ∀ k, f.1.toOrderHom k ≠ j} := by sorry -- Fin (4) is well-founded! But apparently it is not a Set
    let j := Set.IsWF.min h₂ h₁
    have hj : ¬j = 1 := sorry
    have hji : ∀ k, f.1.toOrderHom k ≠ j := sorry
    let f₁ := f.1
    have H : f = (Λ[2+1, 1].map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op) (horn.face 1 j hj) := by
      apply Subtype.ext
      exact (factor_δ_spec (SimplexCategory.mkHom f.1.toOrderHom) j hji).symm
    use S.map (factor_δ (SimplexCategory.mkHom f.1.toOrderHom) j).op (σ j)
  }
  naturality := by{
    intro l m f
    sorry
  }
-- remark: WHY IS IT SO HARD FOR LEAN TO MATCH APPLICATION TYPES WHEN THEY ARE LITERALLY DEFINED TO BE THE SAME
-- for example it expects something of type SimplexCategoryᵒᵖ but the argument is ℕᵒᵖ - The definition of SimplexCategory is ℕ, nothing more

def hom_by_faces_2th_3horn {S : SSet} [Quasicategory S] (σ : Fin (4) → S _[2]) : Λ[3,2] ⟶ S where
  app m := by{
    intro f
    have h : ∃ j : Fin (4), (¬j = 2 ∧ ∀ k, f.1.toOrderHom k ≠ j) := by{
      simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or] using f.2
    }
    let h₁ : Set.Nonempty {j : Fin (4) | ¬j = 2 ∧ ∀ k, f.1.toOrderHom k ≠ j} := by exact h
    let h₂ : Set.IsWF {j : Fin (4) | ¬j = 2 ∧ ∀ k, f.1.toOrderHom k ≠ j} := by sorry -- Fin (4) is well-founded! But apparently it is not a Set
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

-- here i try to make hom by faces in more generality

def hom_by_faces {S : SSet} [Quasicategory S] {n : ℕ} {i : Fin (n+1)} (σ : Fin (n+2) → S _[n]) : Λ[n+1,i] ⟶ S where
  app m := by{
    intro f
    have h : ∃ j, (¬j = Fin.castSucc i ∧ ∀ k, f.1.toOrderHom k ≠ j) := by{
      simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or] using f.2
    }
    let h₁ : Set.Nonempty {j : Fin (n+1+1) | ¬j = Fin.castSucc i ∧ ∀ k, f.1.toOrderHom k ≠ j} := h
    let h₂ : Set.IsWF {j : Fin (n+1+1) | ¬j = Fin.castSucc i ∧ ∀ k, f.1.toOrderHom k ≠ j} := by sorry -- Fin (4) is well-founded! But apparently it is not a Set
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
#check Δ[3].obj {unop := [n]}


-- # Homotopy

/- For f, g in S₁ with d₀f=d₀g and d₁f=d₁g, we say f and g are left homotopic
if there exists σ : S₂ such that d₀σ=f, d₁σ = g and d₂σ = s₀d₁f
-/

def right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : Prop := by{
  exact (S.δ 1) f = (S.δ 1) g ∧ (S.δ 0) f = (S.δ 0) g ∧ ∃ σ : S _[2], S.δ 0 σ = S.σ 0 (S.δ 1 f) ∧ S.δ 1 σ = g ∧ S.δ 2 σ = f
}
-- hmm I would like a definition where we have same_start, same_end and exists_filler as three lines (where (same_start : (S.δ 1) f = (S.δ 1) g) (same_end : (S.δ 0) f = (S.δ 0) g))
-- but the following  is not convenient to use
structure htpy {S : SSet} [Quasicategory S] (f g : S _[1]) where
  same_start : (S.δ 1) f = (S.δ 1) g
  same_end : (S.δ 0) f = (S.δ 0) g
  right_filler : ∃ σ : S _[2], S.δ 0 σ = S.σ 0 (S.δ 1 f) ∧ S.δ 1 σ = g ∧ S.δ 2 σ = f
  left_filler :  ∃ σ : S _[2], S.δ 0 σ = f ∧ S.δ 1 σ = g ∧ S.δ 2 σ = S.σ 0 (S.δ 1 f)

#check htpy.same_start

def left_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : Prop := by{
  exact (S.δ 1) f = (S.δ 1) g ∧ (S.δ 0) f = (S.δ 0) g ∧ ∃ σ : S _[2], S.δ 0 σ = f ∧ S.δ 1 σ = g ∧ S.δ 2 σ = S.σ 0 (S.δ 1 f)
}





-- left_homotopic and right_homotopic are equivalent

def makefunction {S : SSet} (σ₀ σ₁ σ₂ σ₃ : S _[2]) : Fin (4) → (S _[2])
  | 0 => σ₀
  | 1 => σ₁
  | 2 => σ₂
  | 3 => σ₃
-- "don't know how to synthesize placeholder" problem below:
-- this is the most brute force way to define the function `s`, but it still doesn't work! why?

lemma left_homotopic_iff_right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : left_homotopic f g ↔ right_homotopic f g := by{
  constructor
  · intro hleft
    rw[left_homotopic] at hleft
    obtain ⟨σ, hσ⟩ := hleft.2.2
    constructor
    · exact hleft.1
    · constructor
      · exact (hleft.2).1
      · let s : Fin 4 → (S _[2]) := makefunction (SimplicialObject.σ S 0 f) σ σ (SimplicialObject.σ S 1 f)
--        have a : Λ[3,1] ⟶ S := hom_by_faces_1th_3horn (s : Fin 4 → S _[2]) _
--        obtain ⟨b, hb⟩ := Quasicategory.hornFilling _ _ a
--        have temp1 : 0 ≤ 2 := by exact Nat.zero_le 2
--        have temp2 : 2 ≤ 3 := by exact Nat.AtLeastTwo.prop
--        use (b.app (op [2]) (standardSimplex.triangle 0 2 3 (temp1) (temp2)))
        sorry
  · intro hright
    constructor
    · exact hright.1
    · constructor
      · exact (hright.2).1
      · sorry
}
example : (0 : Fin 4) ≤ 2 := by exact Nat.zero_le 2




#check horn.hom_ext
-- for this proof, I need to find out how to explicitly define a map Λ _[k i] → S
-- oh maybe by horn.ext which doesn't work in this file

def qc_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : Prop := left_homotopic f g ∨ right_homotopic f g

#check (qc_homotopic f g)
#check horn.hom_ext
-- lemmas homotopic_of_right_homotopic and homotopic_of_left_homotopic would be useful to have

/-
The next steps are:
- the homotopy relation is an equivalence relation on the set of morphism with domain x and codomain y.
- Composition is unique up to homotopy: Let f : x → y and g : y → z and let h, h′ : x → z be two possible compositions. Prove h ∼ h′.
- Composition is associative up to homotopy: For three morphisms f : x → y, g : y → z, h : z → w, there exists a homotopy h ◦ (g ◦ f ) ∼ (h ◦ g) ◦ f .
- Identity maps: there are equivalences f ∼ f ◦ idx ∼ idy ◦ f where idx = S.σ 0 (S.δ 1 f)
- most challenging part up to here: define the Homotopy Category of a Quasicategory S
-/
