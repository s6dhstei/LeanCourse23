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
(I don't need the following, might delete it)
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

structure htpy {S : SSet} [Quasicategory S] (f g : S _[1]) where
  same_start : (S.δ 1) f = (S.δ 1) g
  same_end : (S.δ 0) f = (S.δ 0) g
  right_filler : ∃ σ : S _[2], S.δ 0 σ = S.σ 0 (S.δ 1 f) ∧ S.δ 1 σ = g ∧ S.δ 2 σ = f
  left_filler :  ∃ σ : S _[2], S.δ 0 σ = f ∧ S.δ 1 σ = g ∧ S.δ 2 σ = S.σ 0 (S.δ 1 f)


def left_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : Prop := by{
  exact ((S.δ 1) f = (S.δ 1) g ∧ (S.δ 0) f = (S.δ 0) g) ∧ ∃ σ : S _[2], S.δ 0 σ = f ∧ S.δ 1 σ = g ∧ S.δ 2 σ = S.σ 0 (S.δ 1 f)
}
def right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : Prop := by{
  exact ((S.δ 1) f = (S.δ 1) g ∧ (S.δ 0) f = (S.δ 0) g) ∧ ∃ σ : S _[2], S.δ 0 σ = S.σ 0 (S.δ 0 f) ∧ S.δ 1 σ = g ∧ S.δ 2 σ = f
}




-- left_homotopic and right_homotopic are equivalent

def makefunction {S : SSet} (σ₀ σ₁ σ₂ σ₃ : S _[2]) : Fin (4) → (S _[2])
  | 0 => σ₀
  | 1 => σ₁
  | 2 => σ₂
  | 3 => σ₃
-- "don't know how to synthesize placeholder" problem below: where did it come from? (never mind)

lemma temp02 {n} : @OfNat.ofNat (Fin (n + 1)) 0 Fin.instOfNatFin ≤ 2 := sorry
lemma temp12 {n} : @OfNat.ofNat (Fin (n + 1)) 1 Fin.instOfNatFin ≤ 2 := sorry
lemma temp23 {n} : @OfNat.ofNat (Fin (n + 1)) 2 Fin.instOfNatFin ≤ 3 := sorry
lemma neq01 {n} : @OfNat.ofNat (Fin (n + 1)) 0 Fin.instOfNatFin ≠ 1 := sorry

lemma standard_simplex_naturality {S : SSet} {n : ℕ} ⦃X Y : SimplexCategoryᵒᵖ⦄ (f : X ⟶ Y)  (a : Δ[n] ⟶ S) (x : Δ[n].obj X) : S.map f (a.app X x) = a.app Y (Δ[n].map f x) := by exact
  (FunctorToTypes.naturality Δ[n] S a f x).symm

-- I forgot how to rewrite when there is no equality lemma, so I'm making equality lemmata
lemma delta_is {S : SSet} {n} (i : Fin (n + 2)) : (SimplicialObject.δ S i : S _[n + 1] ⟶ S _[n]) = S.map (SimplexCategory.δ i).op := rfl



-- left homotopic to right homotopic

lemma left_homotopic_to_right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : left_homotopic f g → right_homotopic f g := by{
  intro hleft
  rw[left_homotopic] at hleft
  obtain ⟨σ, hσ⟩ := hleft.2
  obtain ⟨hleft1, hleft2, hleft3⟩ := hσ
  constructor
  · exact hleft.1
  · let s : Fin 4 → (S _[2]) := makefunction (SimplicialObject.σ S 0 f) σ σ (SimplicialObject.σ S 1 f)
    let a : Λ[3,1] ⟶ S := by {
    use fun m ↦ ((hom_by_faces_1th_3horn (s : Fin 4 → S _[2])).app m)
    apply (hom_by_faces_1th_3horn (s : Fin 4 → S _[2])).naturality}
    have temp_a0 : a.app (op [2]) (horn.face 1 0 neq01) = SimplicialObject.σ S 0 f := by sorry

--    have temp3 : @LT.lt (Fin (3 + 1)) instLTFin 0 1 := by exact Fin.one_pos
    have temp13l : @LT.lt (Fin (3 + 1)) instLTFin 1 (Fin.last 3) := by exact Fin.lt_last_iff_coe_castPred.mpr rfl
    obtain ⟨b, hb⟩ := Quasicategory.hornFilling Fin.one_pos (temp13l) a
--    have temp02 : 0 ≤ 2 := by exact Nat.zero_le 2
    let B := b.app (op [2]) (standardSimplex.triangle 0 2 3 (temp02) (temp23))
    use B
    have B_is : B = b.app (op [2]) (standardSimplex.triangle 0 2 3 temp02 (_ : OfNat.ofNat 2 ≤ 3)) := rfl
    constructor
    ·
--      have temp5 : SimplicialObject.δ S 0 B = SimplicialObject.δ S 0 (b.app (op [2]) (standardSimplex.triangle 1 2 3 (temp12) (temp23))) := by sorry
      have temp71 : SimplicialObject.δ Δ[3] 0 (standardSimplex.triangle 1 2 3 (temp12) (temp23)) = standardSimplex.edge 3 2 3 (temp23) := rfl
      have temp72 : SimplicialObject.δ Δ[3] 0 (standardSimplex.triangle 0 2 3 (temp02) (temp23)) = standardSimplex.edge 3 2 3 (temp23) := rfl
      have temp8 : SimplicialObject.δ S 0 (b.app (op [2]) (standardSimplex.triangle 1 2 3 (temp12) (temp23))) = b.app (op [1]) (SimplicialObject.δ Δ[3] 0 (standardSimplex.triangle 1 2 3 (temp12) (temp23))) := by{
        exact (FunctorToTypes.naturality Δ[2 + 1] S b (δ 0).op (standardSimplex.triangle 1 2 3 temp12 temp23)).symm
        -- standard_simplex_naturality (δ 0).op b
        }
      have temp9 : SimplicialObject.δ S 0 B = b.app (op [1]) (standardSimplex.edge 3 2 3 (temp23)) := by {
        rw[temp72.symm]
        rw[B_is]
        rw[delta_is, delta_is]
        exact standard_simplex_naturality (δ 0).op b (standardSimplex.triangle 0 2 3 temp02 temp23)
      }
      rw[temp9]
      have temp_incl : (standardSimplex.edge 3 2 3 (temp23)) = (hornInclusion _ _).app (op [1]) (horn.edge 3 1 2 3 temp23 Finset.card_le_three) := by exact temp71
      have temp_comp : ∀ x, b.app (op [1]) ((hornInclusion 3 1).app (op [1]) x) = a.app (op [1]) x := by sorry
      have temp6 : b.app (op [1]) (standardSimplex.edge 3 2 3 (_ : OfNat.ofNat 2 ≤ 3)) = a.app (op [1]) (horn.edge 3 1 2 3 temp23 Finset.card_le_three) := by {
        rw[temp_incl]
        exact temp_comp (horn.edge 3 1 2 3 temp23 Finset.card_le_three)
      }
      rw[temp6]
      have temp31 : horn.edge 3 1 2 3 (temp23) (Finset.card_le_three) = SimplicialObject.δ Λ[3,1] 0 (horn.face 1 0 neq01) := by sorry
      have temp3 : a.app (op [1]) (horn.edge 3 1 2 3 (temp23) (Finset.card_le_three)) = SimplicialObject.δ S 0 (a.app (op [2]) (horn.face 1 0 neq01)) := by{
        rw[temp31]
        apply (FunctorToTypes.naturality Λ[3,1] S a (δ 0).op (horn.face 1 0 neq01))
      }
      rw[temp3]
      rw[temp_a0]
      -- now this should really just be a simplicial identity
      sorry
    · constructor
      · sorry
      · sorry
}

-- the other direction
lemma left_homotopic_of_right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : right_homotopic f g → left_homotopic f g := sorry

lemma left_homotopic_iff_right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : right_homotopic f g ↔ left_homotopic f g := by {
  constructor
  · exact fun a ↦ left_homotopic_of_right_homotopic f g a
  · exact fun a ↦ left_homotopic_to_right_homotopic f g a
}


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
