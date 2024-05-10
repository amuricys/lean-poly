/-
Copyright (c) 2023 David Spivak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Spivak, Shaowei Lin
-/
import Init.Prelude
import LeanPoly.Data
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Closed.Monoidal

namespace CategoryTheory

namespace Poly

def subst.leftUnitor (p : Poly) : (y ◁ p) ≅ p where
  hom := subst.leftUnitor.hom p
  inv := subst.leftUnitor.inv p

def subst.rightUnitor (p : Poly) : (p ◁ y) ≅ p where
  hom := subst.rightUnitor.hom p
  inv := subst.rightUnitor.inv p

def subst.associator (p q r : Poly) : (p ◁ q) ◁ r ≅ p ◁ (q ◁ r) where
  hom := subst.associator.hom p q r
  inv := subst.associator.inv p q r

instance Poly.subst.monoidalStruct : MonoidalCategoryStruct Poly where
  tensorObj    := subst
  whiskerLeft  := subst.whiskerLeft
  whiskerRight := subst.whiskerRight
  tensorUnit   := y
  leftUnitor   := subst.leftUnitor
  rightUnitor  := subst.rightUnitor
  associator   := subst.associator

/-- All hyptheses proven automatically so none provided. -/
instance Poly.subst.monoidal : MonoidalCategory Poly where

-- structure Comonad where
--   carrier : Poly
--   counit  : carrier ⟶ y
--   comult  : carrier ⟶ (carrier ◁ carrier)


def coproduct.leftUnitor.inv_hom_id : composemap (leftUnitor.inv p) (leftUnitor.hom p) = polyid p :=
  by
  unfold composemap
  unfold polyid
  simp
  exact (And.intro rfl rfl)

def coproduct.leftUnitor.hom_inv_id :
    composemap (leftUnitor.hom p) (leftUnitor.inv p) = polyid (𝟬 + p) := by
  ext d
  . cases d
    . contradiction
    . rfl
  . cases p
    simp only [hom, inv, composemap, polyid, Function.comp_apply, id_eq]
    congr!
    · split
      assumption
    · split
      assumption


def coproduct.leftUnitor (p : Poly) : (𝟬 + p) ≅ p where
  hom := coproduct.leftUnitor.hom p
  inv := coproduct.leftUnitor.inv p
  hom_inv_id := coproduct.leftUnitor.hom_inv_id
  inv_hom_id := coproduct.leftUnitor.inv_hom_id

-- TODO:
-- instance Poly.coproduct.monoidalStruct : MonoidalCategoryStruct Poly where
--   tensorObj    := coproduct
--   whiskerLeft  := coproduct.whiskerLeft
--   whiskerRight := coproduct.whiskerRight
--   tensorUnit   := 𝟬
--   leftUnitor   := _
--   rightUnitor  := _
--   associator   := _

/-!
## Cartesian product
-/

def product.leftUnitor.hom_inv_id : composemap (leftUnitor.hom p) (leftUnitor.inv p) = 𝟙 (𝟭 × p)
  := by
      unfold composemap
      ext
      . rfl
      . simp
        funext _ dir
        cases dir
        . contradiction
        . rfl

def product.leftUnitor (p : Poly) : (𝟭 × p) ≅ p :=
  { hom := product.leftUnitor.hom p
  , inv := product.leftUnitor.inv p
  , hom_inv_id := product.leftUnitor.hom_inv_id -- extracted so that we may unfold composemap
  , inv_hom_id := by
      unfold product.leftUnitor.hom
      simp
      rfl
  }

/-!
## Parallel product is monoidal structure
-/
def tensor.leftUnitor (p : Poly) : (y ⊗ p) ≅ p :=
  { hom := tensor.unit.l.fwd
  , inv := tensor.unit.l.bwd
  }

def tensor.rightUnitor (p : Poly) : (p ⊗ y) ≅ p :=
  { hom := tensor.unit.r.fwd
  , inv := tensor.unit.r.bwd
  }

def tensor.associator (p q r : Poly) : (p ⊗ q) ⊗ r ≅ p ⊗ (q ⊗ r) :=
  { hom := tensor.assoc.bwd
  , inv := tensor.assoc.fwd
  }

instance Poly.tensor.monoidalStruct : MonoidalCategoryStruct Poly where
  tensorObj    := tensor
  whiskerLeft  := tensor.whiskerLeft
  whiskerRight := tensor.whiskerRight
  tensorUnit   := y
  leftUnitor   := tensor.leftUnitor
  rightUnitor  := tensor.rightUnitor
  associator   := tensor.associator

/-- All hypotheses proven automatically so none provided. -/
instance Poly.tensor.monoidal : MonoidalCategory Poly where


-- /-!
-- ## Poly is ⊗-closed
-- -/

-- /--
-- The internal hom-object under ⊗.
-- I don't know enough about universes but I suppose
-- they should remain constant (the Us in {u, u} below).
-- -/

def homTensor.closed.adjunction.homEquiv.toFun {p : Poly} (φ : (p ⊗ X ⟶ Y)) : (X ⟶ ⟦p, Y⟧ ) :=
    let curriedOnPos (xPos : X.pos) : p ⟶ Y :=
        { onPos := λ pPos ↦ φ.onPos (pPos, xPos)
        -- We have to bee explicit about φ.onPos here; if we pattern match on φ
        -- to extract onPos, we get a type mismatch error.
        , onDir := λ (pPos : p.pos) (yDir : Poly.dir Y (φ.onPos (pPos, xPos)))  ↦
            let ⟨dirp, _⟩  := φ.onDir (pPos, xPos) yDir
            dirp }
    let curriedOnDir (xPos : X.pos) (homDir : (⟦p, Y⟧).dir (curriedOnPos xPos)) : X.dir xPos := match homDir with
        | ⟨pPos, ydir⟩ =>
            let ⟨_, dirx⟩  := φ.onDir (pPos, xPos) ydir
            dirx
      { onPos := curriedOnPos
        onDir := curriedOnDir }

def homTensor.closed.adjunction.homEquiv.invFun {p : Poly} (ψ : X ⟶ ⟦p, Y⟧ ) : (p ⊗ X ⟶ Y) :=
  let uncurriedOnPos (pxPos : (p ⊗ X).pos) : Y.pos :=
    let ⟨pPos, xPos⟩ := pxPos
    let intermediate := ψ.onPos xPos
    intermediate.onPos pPos
  let uncurriedOnDir (pxPos : (p ⊗ X).pos) (pyDir : Y.dir (uncurriedOnPos pxPos)) : (p ⊗ X).dir pxPos :=
    let ⟨pPos, xPos⟩ := pxPos
    let intermediate := ψ.onPos xPos
    ⟨intermediate.onDir pPos pyDir, ψ.onDir xPos ⟨pPos, pyDir⟩⟩
  { onPos := uncurriedOnPos,
    onDir := uncurriedOnDir }


def homTensor.closed.adjunction.homEquiv (p X Y : Poly) :
  (p ⊗ X ⟶ Y)  -- Hom(p ⊗ X, Y)  (same as X ⊗ p because ⊗ is symmetric)
  ≃
  (X ⟶ ⟦p, Y⟧ ) -- Hom (X, ⟦p, Y⟧)
  where
   toFun := homTensor.closed.adjunction.homEquiv.toFun
   invFun := homTensor.closed.adjunction.homEquiv.invFun
   left_inv := by
    intro ψ
    unfold homTensor.closed.adjunction.homEquiv.toFun
    unfold homTensor.closed.adjunction.homEquiv.invFun
    simp
    rfl
   right_inv := by
    intro ψ
    unfold homTensor.closed.adjunction.homEquiv.toFun
    unfold homTensor.closed.adjunction.homEquiv.invFun
    simp
    rfl

def homTensor.closed.adjunction (p : Poly) : MonoidalCategory.tensorLeft p ⊣ homTensor.closed.right p :=
  Adjunction.mkOfHomEquiv {homEquiv := homTensor.closed.adjunction.homEquiv p}

instance : Closed (p : Poly) where
  isAdj := {right := homTensor.closed.right p, adj := homTensor.closed.adjunction p}


def bofSides (f : p ⟶ r) (g : q ⟶ w) : p ◁ q ⟶ r ◁ w :=
  { onPos := λ ⟨ ppos, atqpos ⟩ ↦ ⟨ f.onPos ppos, λ atR ↦ g.onPos (atqpos (f.onDir ppos atR)) ⟩
  , onDir := λ ⟨ ppos, atqpos ⟩ ⟨ dr , dw ⟩ ↦ ⟨ f.onDir ppos dr , g.onDir (atqpos (f.onDir ppos dr)) dw ⟩ }

def unitizeLeft (p : Poly) : p ⟶ y ◁ p :=
  { onPos := λ ppos ↦ ⟨() , λ _ ↦ ppos ⟩
  , onDir := λ _ ↦ Sigma.snd
  }

def unitizeRight (p : Poly) : p ⟶ p ◁ y :=
  { onPos := λ ppos => ⟨ppos , λ _ ↦ () ⟩
  , onDir := λ _ => Sigma.fst
  }

structure Comonoid (carrier : Poly) : Type 1 where
  counit  : carrier ⟶ y
  comult  : carrier ⟶ carrier ◁ carrier
  leftCounit : unitizeLeft carrier = composemap comult (bofSides counit (polyid carrier))
  rightCounit : unitizeRight carrier = composemap comult (bofSides (polyid carrier) counit)
  -- 𝔰
  coassoc : HEq (comult ≫ bofSides (polyid carrier) comult) (comult ≫ bofSides comult (polyid carrier))


def comonoids_are_categories.hom  (c : Comonoid carrier) : Category carrier.pos :=
  let bookkeeping {anypos : carrier.pos} : (c.comult.onPos anypos).fst = anypos := sorry
  let 

  { Hom := λ p1 p2 ↦ { f : carrier.dir p1 // cod f = p2 }
  , id := λ p ↦ ⟨ c.counit.onDir p () ,
      by

        reduce
        have x := c.leftCounit
        unfold unitizeLeft at x
        unfold composemap at x
        unfold bofSides at x
        unfold polyid at x
        simp [Function.comp_apply] at x
        congr! at x


        exact x ⟩
  , comp := by
      intros a b c
      reduce
      exact
      λ ⟨dira , dirasib⟩ ⟨dirb , dirbisc⟩ ↦ by
        reduce
        exact ⟨ (by reduce ; whnf ; _ ) , _ ⟩

        sorry
  , id_comp := sorry
  , comp_id := sorry
  , assoc := sorry
  }
  where cod {x : carrier.pos} (f : carrier.dir x) : carrier.pos := let
          a := ((c.comult.onPos x).snd )

          sorry

theorem comonoids_are_categories : Comonoid carrier ≅ Category carrier.pos := {
    hom := comonoids_are_categories.hom
  , inv := sorry
  , hom_inv_id := sorry
  , inv_hom_id := sorry
}


/-!
## Or product is monoidal structure
-/

end Poly

end CategoryTheory
