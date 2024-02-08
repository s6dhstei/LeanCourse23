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
-- set_option maxHeartbeats 2000000



/-
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
-/

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



lemma standard_simplex_naturality {S : SSet} {n : ℕ} ⦃X Y : SimplexCategoryᵒᵖ⦄ (f : X ⟶ Y)  (a : Δ[n] ⟶ S) (x : Δ[n].obj X) : S.map f (a.app X x) = a.app Y (Δ[n].map f x) := by exact
  (FunctorToTypes.naturality Δ[n] S a f x).symm

-- I forgot how to rewrite when there is no equality lemma, so I'm making equality lemmata
lemma delta_is {S : SSet} {n} (i : Fin (n + 2)) : (SimplicialObject.δ S i : S _[n + 1] ⟶ S _[n]) = S.map (SimplexCategory.δ i).op := rfl
lemma sigma_is {S : SSet} {n} (i : Fin (n + 2)) : (SimplicialObject.σ S i : S _[n + 1] ⟶ S _[n + 1 + 1]) = S.map (SimplexCategory.σ i).op := rfl

lemma composition_gg_is_comp {S : SSet} {n m k : SimplexCategoryᵒᵖ } (a : n ⟶ m) (b : m ⟶ k): S.map a ≫ S.map b = S.map b ∘ S.map a := by exact rfl
lemma composition_functoriality {S : SSet} {n m k : SimplexCategoryᵒᵖ } (a : n ⟶ m) (b : m ⟶ k): S.map a ≫ S.map b = S.map (a ≫ b) := by exact (Functor.map_comp S a b).symm
lemma composition_functoriality_applied {n m k : SimplexCategoryᵒᵖ } (a : n ⟶ m) (b : m ⟶ k) (f : S _[len n.unop]) : (S.map a ≫ S.map b) f = S.map (a ≫ b) f := by rw[composition_functoriality a b]
lemma composition_applied {S : SSet} (d1 : S _[1 + 1] ⟶ S _[1]) (s1 : S _[1] ⟶ S _[1 + 1]) (f : S _[1]) : d1 (s1 f) = (d1 ∘ s1) f := rfl
lemma composition_op {n m k : SimplexCategory} (a : n ⟶ m) (b : m ⟶ k) : (a ≫ b).op = b.op ≫ a.op := by exact rfl

-- simplicial identities, sorried out
lemma simpl_id_σ1_δ2 : (SimplexCategory.σ 1).op ≫ (δ 2).op = 𝟙 (op [1] : SimplexCategoryᵒᵖ) := by {
  rw[← composition_op (δ 2) (SimplexCategory.σ 1)]
--  rw[δ_comp_σ_succ] doesn't work because 2 = 1 + 1 is too hard or something
  sorry
}
lemma simpl_id_δ1_σ0 : (SimplexCategory.δ 1).op ≫ (SimplexCategory.σ 0).op = 𝟙 (op [1] : SimplexCategoryᵒᵖ) := by {
  rw[← composition_op (SimplexCategory.σ 0) (δ 1), ← op_id]
  sorry
}
lemma simpl_id_σ1_δ0 : (SimplexCategory.σ 1).op ≫ (SimplexCategory.δ 0).op = 𝟙 (op [1] : SimplexCategoryᵒᵖ) := by {
  rw[← composition_op (SimplexCategory.δ 0) (σ 1), ← op_id]
  sorry
}

lemma temp02 {n} : @OfNat.ofNat (Fin (n + 1)) 0 Fin.instOfNatFin ≤ 2 := sorry
lemma temp12 {n} : @OfNat.ofNat (Fin (n + 1)) 1 Fin.instOfNatFin ≤ 2 := sorry
lemma temp23 {n} : @OfNat.ofNat (Fin (n + 1)) 2 Fin.instOfNatFin ≤ 3 := sorry
lemma neq01 {n} : @OfNat.ofNat (Fin (n + 1)) 0 Fin.instOfNatFin ≠ 1 := sorry

-- if f and g are left homotopic, then they are right homotopic

lemma left_homotopic_to_right_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : left_homotopic f g → right_homotopic f g := by{
  intro hleft
  rw[left_homotopic] at hleft
  obtain ⟨σ, hσ⟩ := hleft.2
  obtain ⟨hleft1, hleft2, hleft3⟩ := hσ
  constructor
  · exact hleft.1
  · let s : Fin 4 → (S _[2])
      | 0 => (SimplicialObject.σ S 0 f)
      | 1 => σ
      | 2 => σ
      | 3 => (SimplicialObject.σ S 1 f)
    have temp_s0 : s 0 = (SimplicialObject.σ S 0 f) := rfl
    have temp_s2 : s 2 = σ := rfl
    have temp_s3 : s 3 = (SimplicialObject.σ S 1 f) := rfl
    have temp_composition2 : S.map (SimplexCategory.σ 0).op (S.map (δ 1).op f) = ((S.map (SimplexCategory.σ 0).op) ∘ (S.map (SimplexCategory.δ 1).op)) f := rfl
    have temp_funcomp : (S.map (SimplexCategory.σ 1).op ≫ S.map (δ 2).op) f = S.map ((SimplexCategory.σ 1).op ≫ (δ 2).op) f := by {
      rw[composition_functoriality (SimplexCategory.σ 1).op (δ 2).op]
    }
    have temp_funcomp2 : (S.map (SimplexCategory.δ 1).op ≫ S.map (SimplexCategory.σ 0).op) f = S.map ((SimplexCategory.δ 1).op ≫ (SimplexCategory.σ 0).op) f := by {
      rw[composition_functoriality (SimplexCategory.δ 1).op (SimplexCategory.σ 0).op]
    }
    have compatible_s : S.map (δ 2).op (s 3) = S.map (δ 2).op (s 2) ∧  S.map (δ 0).op (s 3) = S.map (δ 2).op (s 0) ∧ S.map (δ 0).op (s 2) = S.map (δ 1).op (s 0) := by{
      constructor
      · rw[temp_s3, temp_s2, ← delta_is, hleft3, composition_applied (SimplicialObject.δ S 2) (SimplicialObject.σ S 1)]
        rw[delta_is, sigma_is]
        rw[← composition_gg_is_comp (SimplexCategory.σ 1).op (SimplexCategory.δ 2).op, composition_functoriality_applied S (SimplexCategory.σ 1).op (δ 2).op]
        rw[simpl_id_σ1_δ2, FunctorToTypes.map_id_apply S f]
        rw[delta_is]
        simp[SimplicialObject.δ, SimplicialObject.σ]
        rw[temp_composition2, ← composition_gg_is_comp (SimplexCategory.δ 1).op (SimplexCategory.σ 0).op, temp_funcomp2, simpl_id_δ1_σ0, FunctorToTypes.map_id_apply S f]
      · constructor
        · rw[temp_s3, temp_s0, ← delta_is, composition_applied (SimplicialObject.δ S 0) (SimplicialObject.σ S 1), delta_is, sigma_is, ← composition_gg_is_comp (SimplexCategory.σ 1).op (SimplexCategory.δ 0).op, composition_functoriality_applied S (SimplexCategory.σ 1).op (δ 0).op]
          rw[sigma_is]
          simp[SimplicialObject.δ, SimplicialObject.σ]
          rw[composition_applied (S.map (δ 0).op) (S.map (SimplexCategory.σ 1).op), ← composition_gg_is_comp (SimplexCategory.σ 1).op (SimplexCategory.δ 0).op, composition_functoriality_applied _ _, simpl_id_σ1_δ0, FunctorToTypes.map_id_apply S f]
--          rw[temp_a_simplicial_identity, FunctorToTypes.map_id_apply S f]
          sorry
        · rw[temp_s0, temp_s2, ← delta_is, hleft1, sigma_is]
        --, ← composition_functoriality_applied S (SimplexCategory.σ 1).op (δ 0).op]
          sorry
--          rw[temp_a_simplicial_identity, FunctorToTypes.map_id_apply S f]
--          rw[delta_is]
--          simp[SimplicialObject.δ, SimplicialObject.σ]
--          rw[temp_composition2, ← composition_hilfslemma (SimplexCategory.δ 1).op (SimplexCategory.σ 0).op, temp_funcomp2, temp_another_simplicial_identity, FunctorToTypes.map_id_apply S f]
    }
    let a : Λ[3,1] ⟶ S := by {
      use fun m ↦ ((hom_by_faces_1th_3horn (s : Fin 4 → S _[2]) compatible_s).app m)
      apply (hom_by_faces_1th_3horn (s : Fin 4 → S _[2]) compatible_s).naturality}
    have temp_a0 : a.app (op [2]) (horn.face 1 0 neq01) = SimplicialObject.σ S 0 f := by {
      apply hom_by_faces_13_works_fine_0
      exact compatible_s
    }
    have weirdrfl : @Fin.val (2 + 1) (Fin.castPred 1) = @Fin.val (2 + 2) 1 := by exact rfl -- I don't understand why this is necessary sometimes but apparently it is
    obtain ⟨b, hb⟩ := Quasicategory.hornFilling Fin.one_pos (Fin.lt_last_iff_coe_castPred.mpr weirdrfl) a
    let B := b.app (op [2]) (standardSimplex.triangle 0 2 3 (temp02) (temp23))
    use B
    have B_is : B = b.app (op [2]) (standardSimplex.triangle 0 2 3 temp02 (_ : OfNat.ofNat 2 ≤ 3)) := rfl --obsolete
    constructor
    · have d0_123_is_23 : SimplicialObject.δ Δ[3] 0 (standardSimplex.triangle 1 2 3 (temp12) (temp23)) = standardSimplex.edge 3 2 3 (temp23) := rfl
      have d0_023_is_23 : SimplicialObject.δ Δ[3] 0 (standardSimplex.triangle 0 2 3 (temp02) (temp23)) = standardSimplex.edge 3 2 3 (temp23) := rfl
      have dS0_B_is_b_23 : SimplicialObject.δ S 0 B = b.app (op [1]) (standardSimplex.edge 3 2 3 (temp23)) := by {
        rw[d0_023_is_23.symm]
        simp[B]
        rw[delta_is, delta_is]
        exact standard_simplex_naturality (δ 0).op b (standardSimplex.triangle 0 2 3 temp02 temp23)
      }
      rw[dS0_B_is_b_23]
      have hornincl_23 : (standardSimplex.edge 3 2 3 (temp23)) = (hornInclusion _ _).app (op [1]) (horn.edge 3 1 2 3 temp23 Finset.card_le_three) := by exact d0_123_is_23
      have temp_comp1 : (b.app (op [1])) ∘ ((hornInclusion 3 1).app (op [1])) = a.app (op [1]) := by exact congrFun (congrArg NatTrans.app (id hb.symm)) (op [1])
      have temp_comp : ∀ x, b.app (op [1]) ((hornInclusion 3 1).app (op [1]) x) = a.app (op [1]) x := by {
        intro x
        rw[← temp_comp1]
        exact rfl
      }
      have b_23_is_a_23 : b.app (op [1]) (standardSimplex.edge 3 2 3 (_ : OfNat.ofNat 2 ≤ 3)) = a.app (op [1]) (horn.edge 3 1 2 3 temp23 Finset.card_le_three) := by {
        rw[hornincl_23]
        exact temp_comp (horn.edge 3 1 2 3 temp23 Finset.card_le_three)
      }
      rw[b_23_is_a_23]
      let temp1 := (horn.edge 3 1 2 3 (temp23) (Finset.card_le_three)).val
      let temp2 := (SimplicialObject.δ Λ[3, 1] 0 (horn.face 1 0 (neq01))).val
      have temp3 : temp1 = temp2 := by sorry
      have hornedge23_is_d0_hornface_0 : horn.edge 3 1 2 3 (temp23) (Finset.card_le_three) = SimplicialObject.δ Λ[3,1] 0 (horn.face 1 0 neq01) := by {
--        rw?
        sorry
        --the problem here is that the definition of horn.edge is complicated
      }
      have a_23_is_dS0_a_face0 : a.app (op [1]) (horn.edge 3 1 2 3 (temp23) (Finset.card_le_three)) = SimplicialObject.δ S 0 (a.app (op [2]) (horn.face 1 0 neq01)) := by{
        rw[hornedge23_is_d0_hornface_0]
        apply (FunctorToTypes.naturality Λ[3,1] S a (δ 0).op (horn.face 1 0 neq01))
      }
      rw[a_23_is_dS0_a_face0]
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


def qc_homotopic {S : SSet} [Quasicategory S] (f g : S _[1]) : Prop := left_homotopic f g ∨ right_homotopic f g

#check (qc_homotopic f g)













/-
Note about the sorry's:
- In `HornMorphisms`, naturality in the definition of `hom_by_faces_1th_3horn` is missing.
- In `HornMorphisms`, the `tempij` lemmas should only be temporary, but there are places in which e.g. `i ≤ j : Prop` is needed and I can't find them
- The simplicial identities, I want to fix this and it should not be too hard, but maybe there was a mistake in my compatibility condition. Important TO DO

-/
