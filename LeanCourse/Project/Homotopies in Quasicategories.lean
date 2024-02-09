import LeanCourse.Common
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.Quasicategory
import LeanCourse.Project.HornMorphisms



open CategoryTheory Simplicial
open SSet
open SimplexCategory
open Simplicial
open Opposite


#check Quasicategory
#check hom_by_faces_1th_3horn


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





noncomputable section
set_option maxHeartbeats 2000000


#check Δ[3].obj {unop := [n]}


-- # Homotopy

/- For f, g in S₁ with d₀f = d₀g and d₁f = d₁g, we say f and g are left homotopic
if there exists σ : S₂ such that d₀σ = f, d₁σ = g and d₂σ = s₀d₁f
-/

structure htpy {S : SSet} [Quasicategory S] (f g : S _[1]) where
  same_start : (S.δ 1) f = (S.δ 1) g
  same_end : (S.δ 0) f = (S.δ 0) g
  right_filler : ∃ σ : S _[2], S.δ 0 σ = S.σ 0 (S.δ 1 f) ∧ S.δ 1 σ = f ∧ S.δ 2 σ = g
  left_filler :  ∃ σ : S _[2], S.δ 0 σ = f ∧ S.δ 1 σ = g ∧ S.δ 2 σ = S.σ 0 (S.δ 1 f)


def left_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : Prop := by{
  exact ((S.δ 1) f = (S.δ 1) g ∧ (S.δ 0) f = (S.δ 0) g) ∧ ∃ σ : S _[2], S.δ 0 σ = f ∧ S.δ 1 σ = g ∧ S.δ 2 σ = S.σ 0 (S.δ 1 f)
}
def right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : Prop := by{
  exact ((S.δ 1) f = (S.δ 1) g ∧ (S.δ 0) f = (S.δ 0) g) ∧ ∃ σ : S _[2], S.δ 0 σ = S.σ 0 (S.δ 0 f) ∧ S.δ 1 σ = f ∧ S.δ 2 σ = g
}




-- left_homotopic and right_homotopic are equivalent



lemma standard_simplex_naturality {S : SSet} {n : ℕ} ⦃X Y : SimplexCategoryᵒᵖ⦄ (f : X ⟶ Y)  (a : Δ[n] ⟶ S) (x : Δ[n].obj X) : S.map f (a.app X x) = a.app Y (Δ[n].map f x) := by exact
  (FunctorToTypes.naturality Δ[n] S a f x).symm

-- I forgot how to rewrite when there is no equality lemma, so I'm making equality lemmata
lemma delta_is {S : SSet} {n} (i : Fin (n + 2)) : (SimplicialObject.δ S i : S _[n + 1] ⟶ S _[n]) = S.map (SimplexCategory.δ i).op := rfl
lemma sigma_is {S : SSet} {n} (i : Fin (n + 2)) : (SimplicialObject.σ S i : S _[n + 1] ⟶ S _[n + 1 + 1]) = S.map (SimplexCategory.σ i).op := rfl

lemma composition_gg_is_comp {S : SSet} {n m k : SimplexCategoryᵒᵖ } (a : n ⟶ m) (b : m ⟶ k): S.map a ≫ S.map b = S.map b ∘ S.map a := by exact rfl
lemma composition_functoriality {S : SSet} {n m k : SimplexCategoryᵒᵖ } (a : n ⟶ m) (b : m ⟶ k): S.map a ≫ S.map b = S.map (a ≫ b) := by exact (Functor.map_comp S a b).symm
lemma composition_functoriality_applied {n m k : SimplexCategoryᵒᵖ } (a : n ⟶ m) (b : m ⟶ k) (f : S _[len n.unop]) : (S.map a ≫ S.map b) f = S.map (a ≫ b) f := by rw[composition_functoriality a b]
lemma composition_applied {S : SSet} {m n : ℕ} (d1 : S _[m] ⟶ S _[n]) (s1 : S _[n] ⟶ S _[m]) (f : S _[n]) : d1 (s1 f) = (d1 ∘ s1) f := rfl
lemma composition_op {n m k : SimplexCategory} (a : n ⟶ m) (b : m ⟶ k) : (a ≫ b).op = b.op ≫ a.op := by exact rfl

-- some helpful standardSimplex calculations to rewrite
lemma d0_123_is_23 : SimplicialObject.δ Δ[3] 0 (standardSimplex.triangle 1 2 3 (temp12) (temp23)) = standardSimplex.edge 3 2 3 (temp23) := rfl
lemma d1_123_is_13 : SimplicialObject.δ Δ[3] 1 (standardSimplex.triangle 1 2 3 (temp12) (temp23)) = standardSimplex.edge 3 1 3 (temp13) := by sorry
lemma d2_123_is_12 : SimplicialObject.δ Δ[3] 2 (standardSimplex.triangle 1 2 3 (temp12) (temp23)) = standardSimplex.edge 3 1 2 (temp12) := by sorry
lemma d0_023_is_23 : SimplicialObject.δ Δ[3] 0 (standardSimplex.triangle 0 2 3 (temp02) (temp23)) = standardSimplex.edge 3 2 3 (temp23) := rfl
lemma d1_023_is_03 : SimplicialObject.δ Δ[3] 1 (standardSimplex.triangle 0 2 3 (temp02) (temp23)) = standardSimplex.edge 3 0 3 (temp03) := by sorry
lemma d2_023_is_02 : SimplicialObject.δ Δ[3] 2 (standardSimplex.triangle 0 2 3 (temp02) (temp23)) = standardSimplex.edge 3 0 2 (temp02) := by sorry

lemma hornincl_23 : (standardSimplex.edge 3 2 3 (temp23)) = (hornInclusion _ _).app (op [1]) (horn.edge 3 1 2 3 temp23 Finset.card_le_three) := by exact d0_123_is_23
lemma hornincl_03 : (standardSimplex.edge 3 0 3 (temp03)) = (hornInclusion _ _).app (op [1]) (horn.edge 3 1 0 3 temp03 Finset.card_le_three) := by exact rfl
lemma hornincl_02 : (standardSimplex.edge 3 0 2 (temp02)) = (hornInclusion _ _).app (op [1]) (horn.edge 3 1 0 2 temp02 Finset.card_le_three) := by exact rfl

lemma hornedge23_is_d0_hornface_0 : horn.edge 3 1 2 3 (temp23) (Finset.card_le_three) = SimplicialObject.δ Λ[3,1] 0 (horn.face 1 0 neq01) := by {
  let temp1 := (horn.edge 3 1 2 3 (temp23) (Finset.card_le_three)).val
  let temp2 := (SimplicialObject.δ Λ[3, 1] 0 (horn.face 1 0 (neq01))).val
  have temp3 : temp1 = temp2 := by sorry
  sorry
--the problem here is that the definition of horn.edge is complicated
}
lemma hornedge03_is_d1_hornface_2 : horn.edge 3 1 0 3 (temp03) (Finset.card_le_three) = SimplicialObject.δ Λ[3,1] 1 (horn.face 1 2 neq12.symm) := by {
  sorry
}
lemma hornedge02_is_d1_hornface_3 : horn.edge 3 1 0 2 (temp02) (Finset.card_le_three) = SimplicialObject.δ Λ[3,1] 1 (horn.face 1 3 neq13.symm) := by {
  sorry
}

-- if f and g are left homotopic, then they are right homotopic

lemma left_homotopic_to_right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : left_homotopic f g → right_homotopic f g := by{
  intro hleft
  rw[left_homotopic] at hleft
  obtain ⟨σ, hσ⟩ := hleft.2
  obtain ⟨hleft1, hleft2, hleft3⟩ := hσ
  constructor
  · exact hleft.1
  · let s : Fin 4 → (S _[2])
      | 0 => (SimplicialObject.σ S 1 f)
      | 1 => σ
      | 2 => (SimplicialObject.σ S 0 f)
      | 3 => σ
    have s0_s0 : s 0 = (SimplicialObject.σ S 1 f) := rfl
    have s2_s2 : s 2 = (SimplicialObject.σ S 0 f) := rfl
    have s3_s3 : s 3 = σ := rfl
    have compatible_s : horn1_compatible (s 0) (s 2) (s 3) := by{
      constructor
      · -- the 01-edge is (σ 0) ((δ 1) f)
        rewrite[s3_s3, s2_s2, ← delta_is, hleft3, composition_applied (SimplicialObject.σ S 0) (SimplicialObject.δ S 1)]
        rewrite[delta_is, delta_is, sigma_is]
        simp[SimplicialObject.σ]
        rewrite[composition_applied (S.map (SimplexCategory.σ 0).op) (S.map (SimplexCategory.δ 1).op), ← composition_gg_is_comp (SimplexCategory.δ 1).op (SimplexCategory.σ 0).op, composition_functoriality_applied S (δ 1).op (SimplexCategory.σ 0).op]
        rewrite[composition_applied (S.map (SimplexCategory.δ 2).op) (S.map (SimplexCategory.σ 0).op), ← composition_gg_is_comp (SimplexCategory.σ 0).op (SimplexCategory.δ 2).op, composition_functoriality_applied S (SimplexCategory.σ 0).op (δ 2).op]
        rewrite[← composition_op, ← composition_op]
        rewrite[← δ_comp_σ_of_gt _]
        simp
        exact Fin.coe_sub_iff_lt.mp rfl
      · constructor
        · -- the 12-edge is f
          rewrite[s3_s3, s0_s0, ← delta_is, hleft1, ← delta_is, composition_applied (SimplicialObject.δ S 2) (SimplicialObject.σ S 1), delta_is, sigma_is, ← composition_gg_is_comp (SimplexCategory.σ 1).op (SimplexCategory.δ 2).op, composition_functoriality_applied S (SimplexCategory.σ 1).op (δ 2).op]
          rewrite[← composition_op]
          rewrite[δ_comp_σ_succ' _]
          rewrite[op_id, FunctorToTypes.map_id_apply S f]
          exact rfl
          exact rfl
        · -- the 13-edge is f = (δ 0) ((σ 0) f) = (δ 1) ((σ 1) f)
          rewrite[s0_s0, s2_s2, ← delta_is, composition_applied (SimplicialObject.δ S 0) (SimplicialObject.σ S 0)]
          rewrite[sigma_is]
          simp[SimplicialObject.σ]
          rewrite[composition_applied (S.map (SimplexCategory.δ 1).op) (S.map (SimplexCategory.σ 1).op), ← composition_gg_is_comp (SimplexCategory.σ 1).op (SimplexCategory.δ 1).op, composition_functoriality_applied S (SimplexCategory.σ 1).op (δ 1).op]
          rewrite[delta_is, composition_applied (S.map (SimplexCategory.δ 0).op) (S.map (SimplexCategory.σ 0).op), ← composition_gg_is_comp (SimplexCategory.σ 0).op (SimplexCategory.δ 0).op, composition_functoriality_applied S (SimplexCategory.σ 0).op (δ 0).op]
          rewrite[← composition_op, ← composition_op]
          rewrite[δ_comp_σ_self' _, δ_comp_σ_self' _]
          exact rfl
          exact rfl
          exact rfl
    }
    let a : Λ[3,1] ⟶ S := by {
      use fun m ↦ ((hom_by_faces_1th_3horn (s : Fin 4 → S _[2]) compatible_s).app m)
      apply (hom_by_faces_1th_3horn (s : Fin 4 → S _[2]) compatible_s).naturality}
    have temp_a0 : a.app (op [2]) (horn.face 1 0 neq01) = SimplicialObject.σ S 1 f := by {
      apply hom_by_faces_13_works_fine_0
      exact compatible_s
    }
    have temp_a2 : a.app (op [2]) (horn.face 1 2 neq12.symm) = SimplicialObject.σ S 0 f := by {
      apply hom_by_faces_13_works_fine_2
      exact compatible_s
    }
    have temp_a3 : a.app (op [2]) (horn.face 1 3 neq13.symm) = σ := by {
      apply hom_by_faces_13_works_fine_3
      exact compatible_s
    }
    have weirdrfl : @Fin.val (2 + 1) (Fin.castPred 1) = @Fin.val (2 + 2) 1 := by exact rfl
    obtain ⟨b, hb⟩ := Quasicategory.hornFilling Fin.one_pos (Fin.lt_last_iff_coe_castPred.mpr weirdrfl) a
    let B := b.app (op [2]) (standardSimplex.triangle 0 2 3 (temp02) (temp23))
    use B
    constructor
    · have dS0_B_is_b_23 : SimplicialObject.δ S 0 B = b.app (op [1]) (standardSimplex.edge 3 2 3 (temp23)) := by {
        rewrite[d0_023_is_23.symm]
        simp[B]
        rewrite[delta_is, delta_is]
        exact standard_simplex_naturality (δ 0).op b (standardSimplex.triangle 0 2 3 temp02 temp23)
      }
      rewrite[dS0_B_is_b_23]
      have b_hornincl31_x_is_a_x : ∀ x, b.app (op [1]) ((hornInclusion 3 1).app (op [1]) x) = a.app (op [1]) x := by {
        intro x
        rewrite[← congrFun (congrArg NatTrans.app (id hb.symm)) (op [1])]
        exact rfl
      }
      have b_23_is_a_23 : b.app (op [1]) (standardSimplex.edge 3 2 3 (_ : OfNat.ofNat 2 ≤ 3)) = a.app (op [1]) (horn.edge 3 1 2 3 temp23 Finset.card_le_three) := by {
        rewrite[hornincl_23]
        exact b_hornincl31_x_is_a_x (horn.edge 3 1 2 3 temp23 Finset.card_le_three)
      }
      rewrite[b_23_is_a_23]
      have a_23_is_dS0_a_face0 : a.app (op [1]) (horn.edge 3 1 2 3 (temp23) (Finset.card_le_three)) = SimplicialObject.δ S 0 (a.app (op [2]) (horn.face 1 0 neq01)) := by{
        rewrite[hornedge23_is_d0_hornface_0]
        apply (FunctorToTypes.naturality Λ[3,1] S a (δ 0).op (horn.face 1 0 neq01))
      }
      rewrite[a_23_is_dS0_a_face0, temp_a0, delta_is, delta_is]
      simp[SimplicialObject.σ]
      rewrite[composition_applied (S.map (δ 0).op) (S.map (SimplexCategory.σ 1).op), composition_applied (S.map (SimplexCategory.σ 0).op) (S.map (δ 0).op)]
      rewrite[← composition_gg_is_comp _ _, ← composition_gg_is_comp _ _]
      rewrite[composition_functoriality _ _, composition_functoriality _ _]
      rewrite[← composition_op _ _, ← composition_op _ _]
      rewrite[← δ_comp_σ_of_le (Fin.zero_le (Fin.castSucc 0))]
      simp
    · constructor
      · have dS1_B_is_b_03 : SimplicialObject.δ S 1 B = b.app (op [1]) (standardSimplex.edge 3 0 3 (temp03)) := by {
          rewrite[d1_023_is_03.symm]
          simp[B]
          rewrite[delta_is, delta_is]
          exact standard_simplex_naturality (δ 1).op b (standardSimplex.triangle 0 2 3 temp02 temp23)
        }
        rewrite[dS1_B_is_b_03]
        have b_hornincl31_x_is_a_x : ∀ x, b.app (op [1]) ((hornInclusion 3 1).app (op [1]) x) = a.app (op [1]) x := by {
          intro x
          rewrite[← congrFun (congrArg NatTrans.app (id hb.symm)) (op [1])]
          exact rfl
        }
        have b_03_is_a_03 : b.app (op [1]) (standardSimplex.edge 3 0 3 (_ : OfNat.ofNat 0 ≤ 3)) = a.app (op [1]) (horn.edge 3 1 0 3 temp03 Finset.card_le_three) := by {
          rewrite[hornincl_03]
          exact b_hornincl31_x_is_a_x (horn.edge 3 1 0 3 temp03 Finset.card_le_three)
        }
        rewrite[b_03_is_a_03]
        have a_03_is_dS1_a_face2 : a.app (op [1]) (horn.edge 3 1 0 3 (temp03) (Finset.card_le_three)) = SimplicialObject.δ S 1 (a.app (op [2]) (horn.face 1 2 neq12.symm)) := by{
          rewrite[hornedge03_is_d1_hornface_2]
          apply (FunctorToTypes.naturality Λ[3,1] S a (δ 1).op (horn.face 1 2 neq12.symm))
        }
        rewrite[a_03_is_dS1_a_face2, temp_a2, delta_is]
        simp[SimplicialObject.σ]
        rewrite[composition_applied (S.map (δ 1).op) (S.map (SimplexCategory.σ 0).op)]
        rewrite[← composition_gg_is_comp _ _]
        rewrite[composition_functoriality _ _]
        rewrite[← composition_op _ _]
        rewrite[δ_comp_σ_succ' _]
        rewrite[op_id, FunctorToTypes.map_id_apply S f]
        exact rfl
        exact rfl
      · have dS2_B_is_b_02 : SimplicialObject.δ S 2 B = b.app (op [1]) (standardSimplex.edge 3 0 2 (temp02)) := by {
          rewrite[d2_023_is_02.symm]
          simp[B]
          rewrite[delta_is, delta_is]
          exact standard_simplex_naturality (δ 2).op b (standardSimplex.triangle 0 2 3 temp02 temp23)
        }
        rewrite[dS2_B_is_b_02]
        have b_hornincl31_x_is_a_x : ∀ x, b.app (op [1]) ((hornInclusion 3 1).app (op [1]) x) = a.app (op [1]) x := by {
          intro x
          rewrite[← congrFun (congrArg NatTrans.app (id hb.symm)) (op [1])]
          exact rfl
        }
        have b_02_is_a_02 : b.app (op [1]) (standardSimplex.edge 3 0 2 (_ : OfNat.ofNat 0 ≤ 2)) = a.app (op [1]) (horn.edge 3 1 0 2 temp02 Finset.card_le_three) := by {
          rewrite[hornincl_02]
          exact b_hornincl31_x_is_a_x (horn.edge 3 1 0 2 temp02 Finset.card_le_three)
        }
        rewrite[b_02_is_a_02]
        have a_02_is_dS1_a_face3 : a.app (op [1]) (horn.edge 3 1 0 2 (temp02) (Finset.card_le_three)) = SimplicialObject.δ S 1 (a.app (op [2]) (horn.face 1 3 neq13.symm)) := by{
          rewrite[hornedge02_is_d1_hornface_3]
          apply (FunctorToTypes.naturality Λ[3,1] S a (δ 1).op (horn.face 1 3 neq13.symm))
        }
        rw[a_02_is_dS1_a_face3, temp_a3, hleft2]
        }

-- the other direction
lemma left_homotopic_of_right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : right_homotopic f g → left_homotopic f g := sorry

lemma left_homotopic_iff_right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : right_homotopic f g ↔ left_homotopic f g := by {
  constructor
  · exact fun a ↦ left_homotopic_of_right_homotopic f g a
  · exact fun a ↦ left_homotopic_to_right_homotopic f g a
}


def qc_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : Prop := left_homotopic f g ∨ right_homotopic f g

#check (qc_homotopic f g)













/-
Note about the sorry's:
- In `HornMorphisms`, naturality in the definition of `hom_by_faces_1th_3horn` is missing.
- In `HornMorphisms`, the `tempij` lemmas should only be temporary, but there are places in which e.g. `i ≤ j : Prop` is needed and I can't find them

-/
