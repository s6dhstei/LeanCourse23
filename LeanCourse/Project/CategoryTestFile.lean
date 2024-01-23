import LeanCourse.Common

noncomputable section
set_option linter.unusedVariables false

namespace CategoryTheory
open Category
open Opposite

#check Opposite

-- a category of Sets
instance : Category Type where
  Hom X Y := X → Y
  id := fun X y ↦ y
  comp := fun f g ↦ (fun x ↦ g (f x))

-- a simplex category
instance : Category ℕ where
  Hom n m :=  Fin (n+1) →o Fin (m+1)
  id := by {
    intro n
    exact OrderHom.id
    }
-- usually fun n k ↦ k works fine to define identity map but it's only a map, here it must be order-pres.
  comp := by {
    intro l m n
    intro j
    intro i
    exact OrderHom.comp i j
  }

-- The following defines the simplicial k-simplex Δ[k] with (Δ[k])_n = Hom_Δ([n],[k]):
def Delta (k : ℕ) : Functor ℕᵒᵖ Type where
  obj := by{
    intro n
    exact Fin (n.unop + 1) → Fin (k+1)
  }
  map := by{
    intro n l f j
--    let f' := f.unop
--    let f₁ := f.unop.1
    exact (j ∘ f.unop.1)
  }
-- for an order-preserving map f, we can access the underlying map saying f.1
-- this is how in this case we coerce a morphism to be a map
#check (Delta 1).obj


-- Define the i-th face of Delta k:
def Face (k : ℕ) (i : Fin (k+1)) : Functor ℕᵒᵖ Type where
  obj := by{
    intro n
-- exact {x : Fin (n.unop + 1) → Fin (k+1) // i ∉ {a : Fin (k+1) | ∃ j, (a = x j)}}
-- but it is useful to define them as subsets of (Delta k)_n
    exact {x : (Delta k).obj n // i ∉ {a : Fin (k+1) | ∃ j, (a = x j)}}
  }
  map := by{
    intro n l f g
    use fun a ↦ g.1 (f.unop.1 a)
    intro h
    obtain ⟨b, hb⟩ := h
    have h2 : ∃ c, i = g.1 c := by{
      use f.unop.1 b
    }
    have h3 : i ∈ {a | ∃ j, a = g.1 j} := h2
    have h4 : i ∉ {a | ∃ j, a = g.1 j} := g.2
    exact h4 h2
  }

-- Define the natural inclusion of the i-face of Delta k into Delta k:
def face_incl (k : ℕ) (i : Fin (k+1)) : NatTrans (Face k i) (Delta k) where
  app := by{
    intro x a
    use a.1
  }

-- Define the i-th k-Horn
def Horn (k : ℕ) (i : Fin (k+1)) : Functor ℕᵒᵖ Type where
  obj := by{
    intro n
    exact {x : (Delta k).obj n // ∃ j, j ≠ i ∧ (i ∉ {a : Fin (k+1) | ∃ j, (a = x j)})}
--  in every level, Horn(k i) is defined to be the union of all j-faces for j≠i
  }
  map := by {
    intro n l f g
    use fun a ↦ g.1 (f.unop.1 a)
    obtain ⟨j, hj⟩ := g.2
    use j
    constructor
    · exact hj.1
    · intro h
      obtain ⟨j2, hj2⟩ := h
      have h1 : i ∈ {a | ∃ j, a = g.1 j} := by {
        use (f.unop.1 j2)
      }
      exact hj.2 h1
  }

-- Define the natural inclusion of the i-th k-horn into Delta k:
def horn_incl (k : ℕ) (i : Fin (k+1)) : NatTrans (Horn k i) (Delta k) where
  app := by{
    intro x a
    use a.1
  }
-- redundant, how to do this more elegantly? look up simplicial subsets


-- Define quasi-category and Kan complex as properties that a simplicial set can have
def Is_QuasiCategory (S : Functor ℕᵒᵖ Type) : Prop := by{
  exact ∀ k : ℕ, ∀ i : Fin (k+1), (i≠0 ∧ i≠k) → ∀ f : NatTrans (Horn k i) S, ∃ g : NatTrans (Delta k) S, (f = NatTrans.vcomp (horn_incl k i) g)
}

def Is_KanComplex (S : Functor ℕᵒᵖ Type) : Prop := by{
  exact ∀ k : ℕ, ∀ i : Fin (k+1), ∀ f : NatTrans (Horn k i) S, ∃ g : NatTrans (Delta k) S, (f = NatTrans.vcomp (horn_incl k i) g)
}

#check Is_QuasiCategory (Delta 1)
-- nice

-- What's next? Ideas:
-- Should I make a structure or class "QuasiCategory"?
-- Should I use the pre-defined definition of Simplicial sets instead of my own one?
-- --> pro: pre-defined face/ degeneracy maps

def left_homotpic {S : (Functor ℕᵒᵖ Type)} (f g : S.obj (op 1)) : Prop := by{
  sorry
-- exact d₀ f = d₀ g ∧ d₁ f = d₁ g ∧ ∃ σ : (S.obj 2), d₀ σ = f ∧ d₁ σ = g ∧ d₂ σ = s₀ (d₁ f)
-- for this, I would need the pre-defined d_i and s_i
}

-- Homotopy relation and -category
-- - Let S be a quasicategory and f, g : x → y two morphisms (i.e. elements of S.obj 1). Prove f and g are left homotopic if and only if they are right homotopic. Hence we can simply say f and g are homotopic and denote it f ∼ g.
-- - homotopy is an equivalence relation
-- -
-- Nerve of a category is always a quasi-category
--
