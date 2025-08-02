/-
Copyright (c) 2023 David Spivak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Spivak, Shaowei Lin
-/
import Init.Prelude
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Closed.Monoidal

/-!
# Polynomial Functors

Defines the category of polynomial functors, as a type class parametrised by the type of objects.

## Notations

For polynomial functos, we use the same notation as that for categories.
* `𝟙 p` for the identity lens from `p` to itself (type as `\b1`)
* `p ⟶ q` for the space of lenses from `p` to `q` (type as `\-->`)
* `p ≫ q` for composition in the diagrammatic order (type as `\gg`)

We introduce some new notations in the `Poly` scope
* `A y^B` for monomials

Users may like to add `f ⊚ g` for composition in the classical order, using
```lean
local notation:80 f " ⊚ " g => composemap g f    -- type as \oo
```

Users preferring `;` to `≫` for composition in the diagrammatic order may add
```lean
local infixr:80 " ; " => composemap
```
-/

library_note "Poly universes"
/--
The category `Poly.{u, v}` of polynomial functors and lenses
between them contains polynomial functors
whose positions live in `Type u` and
whose directions have codomains in `Type v`.

These polynomial functors can be applied to types
in any `Type w` independent of `Type u` and `Type v`.
-/

universe u v u' v' w

namespace CategoryTheory
set_option pp.proofs true



/-!
## Category of polynommial functors
-/

/-- Poly as a type where the objects are pairs (pos, dir). -/
structure Poly where
  pos : Type u
  dir : pos -> Type v

/-- The type of lenses/maps from one polynomial functor to another. -/
@[ext]
structure polymap (p q : Poly.{u, v}) : Type max u v where
  onPos : p.pos -> q.pos
  onDir : (x : p.pos) -> q.dir (onPos x) -> p.dir x

/-- The identity lens/map from a polynomial functor to itself. -/
def polyid (p : Poly) : polymap p p where
  onPos := id
  onDir := λ _ ↦ id

/-- Composition of lenses/maps. -/
def composemap {p q r : Poly} (f : polymap p q) (g : polymap q r) :
    polymap p r where
  onPos := g.onPos ∘ f.onPos
  onDir := λ px rd ↦ f.onDir px (g.onDir (f.onPos px) rd)

/-- Poly as a type with some categorical structure. -/
instance Poly.categoryStruct : CategoryStruct Poly where
  Hom  := polymap
  id   := polyid
  comp := composemap

/-- Poly as a category. -/
instance Poly.category : Category Poly where
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc   := by intros; rfl

/-- Applying a polynomial functor to get a type. -/
def applyFun (p : Poly.{u, v}) (T : Type w) :
    Type max u v w :=
  Σ (x : p.pos), (p.dir x) -> T

/-- Applying a lens/map to get a function. -/
def applyMap {p q : Poly.{u, v}} (f : p ⟶ q) (T : Type) :
    (applyFun p T) -> (applyFun q T) :=
  λ x ↦ Sigma.mk (f.onPos x.fst) (x.snd ∘ (f.onDir x.fst))





/-!
## Special polynommial functors
-/

/-- A monomial functor. -/
def monomial (P : Type u) (D: Type v) : Poly.{u, v} where
  pos := P
  dir := (λ _ ↦ D)

/-- Notation for a monomial functor. -/
scoped notation:80 A:80 " y^" B:80 => monomial A B

/-- A representable functor. -/
def representable (D : Type v) : Poly.{u, v} := PUnit.{u+1} y^D

/-- Notation for a representable functor. -/
scoped notation:80 "y^" B:80 => representable B

/-- A constant polynomial functor. -/
def const (P : Type u) : Poly.{u, v} := P y^(PEmpty.{v+1})

/-- Notation for a constant polynomial functor. -/
scoped notation:80 A:80 " y^0" => const A

/-- A linear polynomial functor. -/
def linear (P : Type u) : Poly.{u, v} := P y^(PUnit.{v+1})

/-- Notation for a linear polynomial functor. -/
scoped notation:80 A:80 " y^1" => linear A

/-- The identity functor in Poly. -/
def y : Poly.{u, v} := linear PUnit.{u+1}

/-- Additional notation for a linear polynomial functor. -/
scoped notation "y^1" => y

/-- The initial object in Poly. -/
def poly0 : Poly.{u, v} := const PEmpty.{u+1}

/-- Notation for the initial object. -/
scoped notation "𝟬" => poly0  -- type as `\sb0`

/-- Notation for unique map from empty type. -/
scoped notation "!𝟬" => PEmpty.rec  -- type as `!\sb0`

/-- The terminal object in Poly. -/
def poly1 : Poly.{u, v} := const PUnit.{u+1}

/-- Notation for the terminal object. -/
scoped notation "𝟭" => poly1  -- type as `\sb1`

/-- Notation for unique map to unit type. -/
scoped notation "!𝟭" => Function.const _ PUnit.unit  -- type as `!\sb1`





/-!
## Special lenses/maps
-/

/-- A lens/map between constant polynomial functors. -/
def constantMap {T T' : Type u} (f : T -> T') : T y^0 ⟶ T' y^0 where
  onPos := f
  onDir := (λ _ ↦ !𝟬)

/-- A lens/map between linear polynomial functors. -/
def linearMap {T T' : Type u} (f : T -> T') : T y^1 ⟶ T' y^1 where
  onPos := f
  onDir := (λ _ ↦ !𝟭)

/-- A lens/map between representable functors. -/
def representableMap {T T' : Type u} (f : T -> T') : y^T' ⟶ y^T where
  onPos := !𝟭
  onDir := (λ _ ↦ f)

/-- The unique lens/map from the initial object in Poly. -/
def bang0poly {p : Poly.{u, v}} : 𝟬 ⟶ p where
  onPos := !𝟬
  onDir := !𝟬

/-- The unique lens/map to the terminal object in Poly. -/
def bang1poly {P : Poly.{u, v}} : P ⟶ 𝟭 where
  onPos := !𝟭
  onDir := (λ _ ↦ !𝟬)

/-- A second representation for the type of lenses/maps. -/
def polymap2 (p q : Poly.{u, v}) : Type max u v :=
  (px : p.pos) -> Σ (qx : q.pos), q.dir qx -> p.dir px

/-- Casting from the default representation for the type
    of lenses/maps to the second representation. -/
def cast12 {p q : Poly.{u, v}} (f : p ⟶ q) : polymap2 p q :=
  λ px ↦ (Sigma.mk (f.onPos px) (f.onDir px))

/-- Casting from the second representation for the type
    of lenses/maps to the default representation. -/
def cast21 {p q : Poly.{u, v}} (f : polymap2 p q) : p ⟶ q where
  onPos := (λ px ↦ (f px).fst)
  onDir := (λ px ↦ (f px).snd)





/-!
## Substitution product
-/

/--
Substitution product of polynomial functors.
Require polynomial functors from Poly.{u, u}
for the product to remain in Poly.{u, u}.
-/
def subst (p q : Poly.{u, u}) : Poly.{u, u} where
  pos := applyFun p q.pos
  dir := λ x ↦ Σ (d : p.dir x.fst), (q.dir (x.snd d))

/-- Notation for substitution product of polynomial functors. -/
scoped infixr:80 "◁" => subst -- type as `\lhd`

def subst.whiskerLeft {p : Poly} (f : q ⟶ q') : (p ◁ q) ⟶ (p ◁ q') where
  onPos := λ x ↦ Sigma.mk x.fst (f.onPos ∘ x.snd)
  onDir := λ x d ↦ Sigma.mk d.fst (f.onDir (x.snd d.fst) d.snd)

def subst.whiskerRight (f : p ⟶ p') : (p ◁ q) ⟶ (p' ◁ q) where
  onPos := applyMap f q.pos
  onDir := λ x d ↦ Sigma.mk (f.onDir x.fst d.fst) d.snd


def subst.leftUnitor.hom (p : Poly) : (y ◁ p) ⟶ p where
  onPos := λ x ↦ x.snd x.fst
  onDir := λ _ d ↦ Sigma.mk PUnit.unit d

def subst.leftUnitor.inv (p : Poly) : p ⟶ (y ◁ p) where
  onPos := λ x ↦ Sigma.mk PUnit.unit (λ _ ↦ x)
  onDir := λ _ d ↦ d.snd

def subst.leftUnitor (p : Poly) : (y ◁ p) ≅ p where
  hom := subst.leftUnitor.hom p
  inv := subst.leftUnitor.inv p

def subst.rightUnitor.hom (p : Poly) : (p ◁ y) ⟶ p where
  onPos := λ x ↦ x.fst
  onDir := λ _ d ↦ Sigma.mk d PUnit.unit

def subst.rightUnitor.inv (p : Poly) : p ⟶ (p ◁ y) where
  onPos := λ x ↦ Sigma.mk x (λ _ ↦ PUnit.unit)
  onDir := λ _ d ↦ d.fst

def subst.rightUnitor (p : Poly) : (p ◁ y) ≅ p where
  hom := subst.rightUnitor.hom p
  inv := subst.rightUnitor.inv p

def subst.associator.hom {p q r : Poly} : (p ◁ q) ◁ r ⟶ p ◁ q ◁ r where
  onPos := λ ⟨ ⟨pq_r11 , pq_r12⟩ , pq_r2 ⟩ ↦ ⟨ pq_r11, λ pd ↦ ⟨ pq_r12 pd , λ qd ↦ pq_r2 ⟨ pd , qd ⟩ ⟩ ⟩
  onDir := λ _ ⟨ p_qr1 , ⟨ p_qr21 , p_qr22 ⟩ ⟩ ↦ ⟨ ⟨ p_qr1 , p_qr21 ⟩ , p_qr22 ⟩

def subst.associator.inv (p q r : Poly) :
    p ◁ (q ◁ r) ⟶ (p ◁ q) ◁ r := by
  constructor
  case onPos =>
    intro p_qr
    let p_qr1 := p_qr.fst
    let p_qr2 := p_qr.snd
    constructor
    case fst =>
      constructor
      case fst =>
        exact p_qr1
      case snd =>
        intros pd
        exact (p_qr2 pd).fst
    case snd =>
      intro pqd
      exact (p_qr2 pqd.fst).snd pqd.snd
  case onDir =>
    intro p_qr1 pq_rd
    let pq_rd1 := pq_rd.fst
    let pq_rd2 := pq_rd.snd
    constructor
    case fst =>
      exact pq_rd1.fst
    case snd =>
      constructor
      case fst =>
        exact pq_rd1.snd
      case snd =>
        exact pq_rd2

def subst.associator (p q r : Poly) : (p ◁ q) ◁ r ≅ p ◁ (q ◁ r) where
  hom := subst.associator.hom
  inv := subst.associator.inv p q r

instance Poly.subst.monoidalStruct : MonoidalCategoryStruct Poly where
  tensorObj    := subst
  whiskerLeft  := λ p ↦ subst.whiskerLeft (p := p)
  whiskerRight := λ f q ↦ subst.whiskerRight f (q := q)
  tensorUnit   := y
  leftUnitor   := subst.leftUnitor
  rightUnitor  := subst.rightUnitor
  associator   := subst.associator

/-- All hyptheses proven automatically so none provided. -/
instance Poly.subst.monoidal : MonoidalCategory Poly where

/-!
## Co-Product
-/

def coproduct (p q : Poly.{u, u}) : Poly.{u, u} where
  pos := p.pos ⊕ q.pos
  dir := λ x ↦
    match x with
      | .inl ppos => p.dir ppos
      | .inr qpos => q.dir qpos

infixr:75 " + " => coproduct

def coproduct.map (p q r z : Poly.{u, u}) (f : p ⟶ q) (g : r ⟶ z) : (p + r) ⟶ (q + z) :=
    { onPos := λ pos ↦
      match pos with
        | .inl ppos => .inl (f.onPos ppos)
        | .inr qpos => .inr (g.onPos qpos)
    , onDir := λ pos ↦
      match pos with
        | .inl ppos => f.onDir ppos
        | .inr rpos => g.onDir rpos
    }

def coproduct.whiskerLeft {p q q' : Poly} (f : q ⟶ q') : p + q ⟶ p + q' :=
  (coproduct.map p p q q' ) (polyid p) f

def coproduct.whiskerRight {p p' q : Poly} (f : p ⟶ p') : p + q ⟶ p' + q :=
  (coproduct.map p p' q q) f (polyid q)

def coproduct.split.l {p : Poly.{u, u}} : p ⟶ p + p :=
  { onPos := λ ppos ↦ .inl ppos
  , onDir := λ _ppos ↦ id
  }

def coproduct.split.r {p : Poly.{u, u}} : p ⟶ p + p :=
  { onPos := λ ppos ↦ .inr ppos
  , onDir := λ _ppos pdir ↦ pdir
  }

def coproduct.leftUnitor.hom (p : Poly) : (𝟬 + p) ⟶ p where
  onPos := λ pos ↦
  match pos with
  | .inr ppos => ppos
  onDir := λ pos dir ↦
  match pos with
  | .inr _ppos => dir

def coproduct.leftUnitor.inv (p : Poly) : p ⟶ (𝟬 + p) where
  onPos := λ ppos ↦ .inr ppos
  onDir := λ _ppos pdir ↦ pdir


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

def product (p q : Poly.{u, u}) : Poly.{u, u} where
  pos := p.pos × q.pos
  dir := λ (ppos , qpos) =>  Sum (p.dir ppos) (q.dir qpos)

infixr:85 " × " => product

def product.map (p q r z : Poly.{u, u}) (f : p ⟶ q) (g : r ⟶ z) : (p × r) ⟶ (q × z) :=
    { onPos := λ (ppos , rpos) => (f.onPos ppos , g.onPos rpos)
    , onDir := λ (ppos , rpos) dir =>
      match dir with
        | .inl qdir => .inl (f.onDir ppos qdir)
        | .inr zdir => .inr (g.onDir rpos zdir)
    }

def product.whiskerLeft {p q q' : Poly} (f : q ⟶ q') : p × q ⟶ p × q' :=
  (product.map p p q q' ) (polyid p) f

def product.whiskerRight {p p' : Poly} (f : p ⟶ p') : p × q ⟶ p' × q :=
  (product.map p p' q q) f (polyid q)

def product.fst {p q : Poly} : (p × q) ⟶ p :=
  { onPos := λ (ppos , _qpos) => ppos
  , onDir := λ (_ppos , _qpos) pdir => .inl pdir
  }

def product.snd {p q : Poly} : (p × q) ⟶ q :=
  { onPos := λ (_ppos , qpos) => qpos
  , onDir := λ (_ppos , _qpos) qdir => .inr qdir
  }

def product.swap {p q : Poly} : (p × q) ⟶ (q × p) :=
  { onPos := λ (ppos , qpos) => (qpos , ppos)
  , onDir := λ (_ppos , _qpos) dir =>
        match dir with
          | .inl qdir => .inr qdir
          | .inr pdir => .inl pdir
  }

def product.dupe {p : Poly} : p ⟶ p × p :=
  { onPos := λ ppos => (ppos , ppos)
  , onDir := λ _pos dir =>
        match dir with
          | .inl pdir => pdir
          | .inr pdir => pdir
  }

def product.fanout {p q r : Poly} (f : r ⟶ p) (g : r ⟶ q) : r ⟶ p × q :=
  { onPos := λ rpos => (f.onPos rpos , g.onPos rpos)
  , onDir := λ rpos dir =>
        match dir with
          | .inl pdir => f.onDir rpos pdir
          | .inr qdir => g.onDir rpos qdir
  }

def product.leftUnitor.hom (p : Poly) : (𝟭 × p) ⟶ p where
  onPos := λ (() , ppos) ↦ ppos
  onDir := λ (() , _ppos) pdir ↦ .inr pdir

def product.leftUnitor.inv (p : Poly) : p ⟶ (𝟭 × p) where
  onPos := λ ppos ↦ (.unit , ppos)
  onDir := λ _ppos dir ↦
  match dir with
  | .inr pfib => pfib

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
## Parallel product
-/

def tensor (p q : Poly.{u, u}) : Poly.{u, u} where
  pos := p.pos × q.pos
  dir := λ (ppos , qpos) =>  (p.dir ppos) × (q.dir qpos)

infixr:90 " ⊗ " => tensor

def tensor.map (p q r z : Poly.{u, u}) (f : p ⟶ q) (g : r ⟶ z) : p ⊗ r ⟶ q ⊗ z :=
    { onPos := λ (ppos , rpos) => (f.onPos ppos , g.onPos rpos)
    , onDir := λ (ppos , rpos) (qdir , zdir) => (f.onDir ppos qdir , g.onDir rpos zdir)
    }

def tensor.whiskerLeft (p : Poly) {q q' : Poly} (f : q ⟶ q') : p ⊗ q ⟶ p ⊗ q' :=
  (tensor.map p p q q' ) (polyid p) f

def tensor.whiskerRight {p p' : Poly} (f : p ⟶ p') (q : Poly) : p ⊗ q ⟶ p' ⊗ q :=
  (tensor.map p p' q q) f (polyid q)

def tensor.first {p q r : Poly.{u, u}} (f : p ⟶ r) : p ⊗ q ⟶ r ⊗ q :=
  (tensor.map p r q q) f (polyid q)

def tensor.second {p q r : Poly.{u, u}} (g : q ⟶ r) : p ⊗ q ⟶ p ⊗ r :=
  (tensor.map p p q r) (polyid p) g

def tensor.swap {p q : Poly} : p ⊗ q ⟶ q ⊗ p :=
  { onPos := λ (ppos , qpos) => (qpos , ppos)
  , onDir := λ _ (qdir , pdir) => (pdir , qdir)
  }

def tensor.assoc.fwd {p q r : Poly} : p ⊗ (q ⊗ r) ⟶ (p ⊗ q) ⊗ r :=
  { onPos := λ (ppos , qpos , rpos) => ((ppos , qpos) , rpos)
  , onDir := λ _ ((pdir, qdir) , rdir) => (pdir , qdir , rdir)
  }

def tensor.assoc.bwd {p q r : Poly} : (p ⊗ q) ⊗ r ⟶ p ⊗ (q ⊗ r) :=
  { onPos := λ ((ppos , qpos) , rpos) => (ppos , qpos , rpos)
  , onDir := λ _ (pdir , qdir , rdir) => ((pdir , qdir) , rdir)
  }

def tensor.split.l {p : Poly} : p ⟶ p ⊗ p :=
  { onPos := λ ppos => (ppos , ppos)
  , onDir := λ _ (f , _) => f
  }

def tensor.split.r {p : Poly} : p ⟶ p ⊗ p :=
  { onPos := λ ppos => (ppos , ppos)
  , onDir := λ _ (_ , g) => g
  }

def tensor.unit.l.fwd {P : Poly} : y ⊗ P ⟶ P :=
  { onPos := λ (_ , ppos) => ppos
  , onDir := λ (Unit, _) pdir => (Unit , pdir)
  }

def tensor.unit.l.bwd {P : Poly} : P ⟶ y ⊗ P :=
  { onPos := λ ppos => (Unit.unit , ppos)
  , onDir := λ _ (_ , pdir) => pdir
  }

def tensor.unit.r.fwd {P : Poly} : P ⊗ y ⟶ P :=
  { onPos := λ (ppos , _) => ppos
  , onDir := λ (_ , Unit) pdir => (pdir , Unit)
  }

def tensor.unit.r.bwd {P : Poly} : P ⟶ P ⊗ y :=
  { onPos := λ ppos => (ppos , Unit.unit)
  , onDir := λ _ (pdir , _) => pdir
  }

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
-- ## ⊗-closure
-- -/

-- /--
-- The internal hom-object under ⊗.
-- I don't know enough about universes but I suppose
-- they should remain constant (the Us in {u, u} below).
-- -/

def homTensor (q r : Poly.{u, u}) : Poly.{u, u} where
  pos := q ⟶ r
  dir := λ φ ↦ Σ (j : q.pos), (r.dir (φ.onPos j))

scoped notation:95 "⟦" A:80 "," B:80 "⟧"  => homTensor A B

def homTensor.closed.right.fmap {p q r : Poly} (f : q ⟶ r) :
    (⟦p, q⟧ ⟶ ⟦p, r⟧) where
  onPos := (· ≫ f)
  onDir | _, (Sigma.mk pPos toDirR) => Sigma.mk pPos (f.onDir _ toDirR)

-- The functor ⟦r, -⟧
def homTensor.closed.right (r : Poly) : Poly ⥤ Poly where
  obj := λ x ↦ ⟦r, x⟧
  map := λ f ↦ homTensor.closed.right.fmap f

-- TODO: Shouldn't this be used somewhere to prove something about
-- the internal hom?
def homTensor.eval (p r : Poly) : ⟦ p, r ⟧ ⊗ p ⟶ r where
  onPos := λ (φ, pPos) ↦ φ.onPos pPos
  onDir := λ (φ, pPos) dirR ↦ (⟨pPos, dirR⟩, φ.onDir pPos dirR)

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
  rightAdj := homTensor.closed.right p
  adj := homTensor.closed.adjunction p

/-!
## Or product
-/

def or (p q : Poly.{u, u}) : Poly.{u, u} := p + (p × q) + q

infixr:75 " ∨ " => or

def or.map (p q r z : Poly.{u, u}) (f : p ⟶ q) (g : r ⟶ z) : (p ∨ r) ⟶ (q ∨ z) :=
    { onPos := λ pos =>
      match pos with
      | .inl ppos => .inl (f.onPos ppos)
      | .inr (.inl (ppos , rpos)) => .inr (.inl (f.onPos ppos , g.onPos rpos))
      | .inr (.inr rpos) => .inr (.inr (g.onPos rpos))
    , onDir := λ pos fib =>
      match pos with
      | .inl ppos => f.onDir ppos fib
      | .inr (.inl (ppos , rpos)) =>
        match fib with
        | .inl qfib => .inl (f.onDir ppos qfib)
        | .inr zfib => .inr (g.onDir rpos zfib)
      | .inr (.inr rpos) => g.onDir rpos fib
    }

def or.whiskerLeft (p : Poly) {q q' : Poly} (f : q ⟶ q') : p ∨ q ⟶ p ∨ q' :=
  (or.map p p q q' ) (polyid p) f

def or.whiskerRight {p p' : Poly} (f : p ⟶ p') (q : Poly) : p ∨ q ⟶ p' ∨ q :=
  (or.map p p' q q) f (polyid q)


-- | _∨_ This Inclusion
def This {p q : Poly} : p ⟶ p ∨ q :=
  { onPos := .inl
  , onDir := λ _ => id
  }

-- | _∨_ That Inclusion
def That {p q : Poly} : q ⟶ p ∨ q :=
  { onPos := .inr ∘ .inr
  , onDir := λ _ => id
  }

-- | _∨_ These Inclusion
def These {p q : Poly} : (p × q) ⟶ p ∨ q :=
  { onPos := .inr ∘ .inl
  , onDir := λ _ => id
  }

-- | _∨_ Eliminator
def these {p q r : Poly} (f : p ⟶ r) (g : q ⟶ r) (h : (p × q) ⟶ r) : ((p ∨ q) ⟶ r) :=
  { onPos := λ pos =>
    match pos with
    | .inl ppos => f.onPos ppos
    | .inr (.inl (ppos , qpos)) => h.onPos (ppos , qpos)
    | .inr (.inr qpos) => g.onPos qpos
  , onDir := λ pos fib =>
    match pos with
    | .inl ppos => f.onDir ppos fib
    | .inr (.inl (ppos , qpos)) => h.onDir (ppos , qpos) fib
    | .inr (.inr qpos) => g.onDir qpos fib
  }

end CategoryTheory
