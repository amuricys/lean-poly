import Init.Prelude
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Closed.Monoidal
import «LeanPoly».Poly
import «LeanPoly».Lemmas
import LeanCopilot

/-!
## Custom substitution product
-/

namespace CategoryTheory

/--
Substitution product of polynomial functors. Uses
its own custom inductive type for representing both positions and directions.
Require polynomial functors from Poly.{u, u}
for the product to remain in Poly.{u, u}.
-/

structure SubstPos (p q : Poly) : Type where
  b : p.pos
  next : p.dir b → q.pos

structure SubstDir {p q : Poly} (pos : SubstPos p q) : Type where
  t : p.dir pos.b -- t for position on top
  two : q.dir (pos.next t) -- two for the one-two step that directions represent

def subst2 (p q : Poly) : Poly where
  pos := SubstPos p q
  dir := λ x ↦ SubstDir x

/-- Notation for substitution product of polynomial functors. -/
scoped infixr:80 "⋉" => subst2 -- type as `\ltimes`

def subst2.whiskerLeft {p : Poly} (f : q ⟶ q') : (p ⋉ q) ⟶ (p ⋉ q') where
  onPos := λ x ↦ SubstPos.mk x.b (f.onPos ∘ x.next)
  onDir := λ x d ↦ SubstDir.mk d.t (f.onDir (x.next d.t) d.two)

def subst2.whiskerRight (f : p ⟶ p') : (p ⋉ q) ⟶ (p' ⋉ q) where
  onPos := λ x ↦ SubstPos.mk (f.onPos x.b) (x.next ∘ f.onDir x.b)  -- applyMap f q.pos
  onDir := λ x d ↦ SubstDir.mk (f.onDir x.b d.t) d.two


def subst2.leftUnitor.hom (p : Poly) : (y ⋉ p) ⟶ p where
  onPos := λ x ↦ x.next x.b
  onDir := λ _ d ↦ SubstDir.mk PUnit.unit d

def subst2.leftUnitor.inv (p : Poly) : p ⟶ (y ⋉ p) where
  onPos := λ x ↦ SubstPos.mk PUnit.unit (λ _ ↦ x)
  onDir := λ _ d ↦ d.two

def subst2.leftUnitor (p : Poly) : (y ⋉ p) ≅ p where
  hom := subst2.leftUnitor.hom p
  inv := subst2.leftUnitor.inv p

def subst2.rightUnitor.hom (p : Poly) : (p ⋉ y) ⟶ p where
  onPos := λ x ↦ x.b
  onDir := λ _ d ↦ SubstDir.mk d PUnit.unit

def subst2.rightUnitor.inv (p : Poly) : p ⟶ (p ⋉ y) where
  onPos := λ x ↦ SubstPos.mk x (λ _ ↦ PUnit.unit)
  onDir := λ _ d ↦ d.t

def subst2.rightUnitor (p : Poly) : (p ⋉ y) ≅ p where
  hom := subst2.rightUnitor.hom p
  inv := subst2.rightUnitor.inv p

def subst2.associator.hom {p q r : Poly} : (p ⋉ q) ⋉ r ⟶ p ⋉ q ⋉ r where
  onPos := λ ⟨ ⟨pq_r11 , pq_r12⟩ , pq_r2 ⟩ ↦ ⟨ pq_r11, λ pd ↦ ⟨ pq_r12 pd , λ qd ↦ pq_r2 ⟨ pd , qd ⟩ ⟩ ⟩
  onDir := λ _ ⟨ p_qr1 , ⟨ p_qr21 , p_qr22 ⟩ ⟩ ↦ ⟨ ⟨ p_qr1 , p_qr21 ⟩ , p_qr22 ⟩

def subst2.associator.inv {p q r : Poly} :
    p ⋉ (q ⋉ r) ⟶ (p ⋉ q) ⋉ r := by
  constructor
  case onPos =>
    intro p_qr
    let p_qr1 := p_qr.b
    let p_qr2 := p_qr.next
    constructor
    case b =>
      constructor
      case b =>
        exact p_qr1
      case next =>
        intros pd
        exact (p_qr2 pd).b
    case next =>
      intro pqd
      exact (p_qr2 pqd.t).next pqd.two
  case onDir =>
    intro p_qr1 pq_rd
    let pq_rd1 := pq_rd.t
    let pq_rd2 := pq_rd.two
    constructor
    case t =>
      exact pq_rd1.t
    case two =>
      constructor
      case t =>
        exact pq_rd1.two
      case two =>
        exact pq_rd2

def subst2.associator (p q r : Poly) : (p ⋉ q) ⋉ r ≅ p ⋉ (q ⋉ r) where
  hom := subst2.associator.hom
  inv := subst2.associator.inv

instance Poly.subst2.monoidalStruct : MonoidalCategoryStruct Poly where
  tensorObj    := subst2
  whiskerLeft  := λ p ↦ subst2.whiskerLeft (p := p)
  whiskerRight := λ f q ↦ subst2.whiskerRight f (q := q)
  tensorUnit   := y
  leftUnitor   := subst2.leftUnitor
  rightUnitor  := subst2.rightUnitor
  associator   := subst2.associator

/-- All hyptheses proven automatically so none provided. -/
instance Poly.subst2.monoidal : MonoidalCategory Poly where


/-- A comonoid in Poly (with respect to the substitution product ⋉ and unit y). -/
structure Comonoid2 where
  carrier     : Poly
  counit      : carrier ⟶ y
  comult      : carrier ⟶ carrier ⋉ carrier
  leftCounit  : composemap comult (subst2.whiskerRight counit)
                =
                subst2.leftUnitor.inv carrier
  rightCounit : composemap comult (subst2.whiskerLeft counit)
                = subst2.rightUnitor.inv carrier
  coassoc     : (composemap comult (subst2.whiskerLeft comult)) -- : c ⟶ c ⋉ (c ⋉ c)
                =
                composemap (composemap comult (subst2.whiskerRight comult)) -- : c ⟶ (c ⋉ c) ⋉ c
                           subst2.associator.hom -- therefore the associator is needed

lemma fst_eq_new {H X : SubstPos p q} (e : H = X) : H.b = X.b := by
  cases e
  rfl

def snd_heq_new {H X : SubstPos p q} (h : H = X) : H.next = (fst_eq_new h) ▸ X.next := by
  cases h
  rfl

lemma bookkeeping_new {C : Comonoid2} (i : C.carrier.pos) : (C.comult.onPos i).b = i :=
  by
  have H : (composemap C.comult (subst2.whiskerLeft C.counit)).onPos i
           =
           (subst2.rightUnitor.inv C.carrier).onPos i := by
           rewrite [C.rightCounit]
           simp only
  apply fst_eq_new H

lemma dir_eq_new {C : Comonoid2} {i : C.carrier.pos} : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).b := by
  rewrite [bookkeeping_new i]
  rfl

def cod_new {C : Comonoid2} {i : C.carrier.pos} (f : C.carrier.dir i) : C.carrier.pos :=
    (C.comult.onPos i).next (dir_eq_new ▸ f)

def posAtDir_new {C : Comonoid2} (i : C.carrier.pos) : C.carrier.pos :=
  (C.comult.onPos i).b

def cod_2_new {C : Comonoid2} {i : C.carrier.pos} (f : C.carrier.dir (posAtDir_new i)) : C.carrier.pos :=
    (C.comult.onPos i).next f

def comp_new {C : Comonoid2} {i : C.carrier.pos} (f : C.carrier.dir i) (g : C.carrier.dir (cod_new f)) : C.carrier.dir i :=
  C.comult.onDir i ⟨ dir_eq_new ▸ f , g ⟩

def comp_2_new {C : Comonoid2}
         {i : C.carrier.pos}
         (f : C.carrier.dir (posAtDir_new i))
         (g : C.carrier.dir (cod_2_new f)) :
         C.carrier.dir i :=
         C.comult.onDir i ⟨ f , g ⟩

lemma coassoc_pos_statement_new {C : Comonoid2}
                            {i : C.carrier.pos}
                            (f : C.carrier.dir i)
                            (g : C.carrier.dir (cod_new f)) :
                            cod_new g = cod_new (comp_new f g) := by
    have coassoc_onPos := congrArg (λ x => x.onPos) C.coassoc
    simp [composemap, subst2.whiskerRight, subst2.whiskerLeft, applyMap, subst2.associator.hom, Function.comp, subst2] at coassoc_onPos

    let at_i := congrFun coassoc_onPos i

    have wait : (fun x => C.comult.onPos ((C.comult.onPos i).next x) : C.carrier.dir (C.comult.onPos i).b → (C.carrier⋉C.carrier).pos)
                =
                (bookkeeping_new (C.comult.onPos i).b) ▸
                 (fun pd =>
                   { b := (C.comult.onPos (C.comult.onPos i).b).next pd,
                     next := fun qd => (C.comult.onPos i).next (C.comult.onDir (C.comult.onPos i).b ⟨ pd , qd ⟩)
                     } : C.carrier.dir (C.comult.onPos (C.comult.onPos i).b).b → (C.carrier⋉C.carrier).pos )
                := snd_heq_new (h := at_i)

    have hard_rhs : Eq.rec (motive := fun x _ => C.carrier.dir x → (C.carrier ⋉ C.carrier).pos)
                           (fun pd : C.carrier.dir (C.comult.onPos (C.comult.onPos i).b).b =>
                             { b := (C.comult.onPos (C.comult.onPos i).b).next pd,
                               next := fun qd =>
                                 (C.comult.onPos i).next
                                   (C.comult.onDir (C.comult.onPos i).b { t := pd, two := qd }) } )
                           (bookkeeping_new ((C.comult.onPos i).b) : (C.comult.onPos (C.comult.onPos i).b).b = (C.comult.onPos i).b)
                    =
                    (fun pd =>
                      { b := (C.comult.onPos (C.comult.onPos i).b).next (dir_eq_new ▸ pd),
                        next := fun qd => (C.comult.onPos i).next (C.comult.onDir (C.comult.onPos i).b ⟨ dir_eq_new ▸ pd , qd ⟩)
                        } : C.carrier.dir (C.comult.onPos i).b → (C.carrier⋉C.carrier).pos )
                    := push_cast_in_lambda (χ := (C.carrier ⋉ C.carrier).pos)
                                           (bookkeeping_new ((C.comult.onPos i).b))
                                           (fun (pd : C.carrier.dir (C.comult.onPos (C.comult.onPos i).b).b) =>
                                             { b := (C.comult.onPos (C.comult.onPos i).b).next pd,
                                               next := fun qd =>
                                                 (C.comult.onPos i).next (C.comult.onDir (C.comult.onPos i).b { t := pd, two := qd }) })

    have now_we'd_be_talking :
                (fun x => C.comult.onPos ((C.comult.onPos i).next x) : C.carrier.dir (C.comult.onPos i).b → (C.carrier⋉C.carrier).pos)
                =
                (fun pd =>
                      { b := (C.comult.onPos (C.comult.onPos i).b).next (dir_eq_new ▸ pd),
                        next := fun qd => (C.comult.onPos i).next (C.comult.onDir (C.comult.onPos i).b ⟨ dir_eq_new ▸ pd , qd ⟩)
                        } : C.carrier.dir (C.comult.onPos i).b → (C.carrier⋉C.carrier).pos )
                := by
                conv =>
                  rhs
                  rw [← hard_rhs]
                exact wait

    have obvious : (C.carrier.dir i → (C.carrier⋉C.carrier).pos)
                   =
                   (C.carrier.dir (C.comult.onPos i).b → (C.carrier⋉C.carrier).pos)
                   := by
                   rewrite [bookkeeping_new i]
                   rfl

    have now_lhs : (fun x => C.comult.onPos ((C.comult.onPos i).next x) : C.carrier.dir (C.comult.onPos i).b → (C.carrier⋉C.carrier).pos)
                   =
                   obvious ▸
                   (fun x => C.comult.onPos ((C.comult.onPos i).next (dir_eq_new ▸ x)) : C.carrier.dir i → (C.carrier⋉C.carrier).pos)
                   := lhs_lemma (arg1 := C.carrier.dir (C.comult.onPos i).b)
                                (arg2 := C.carrier.dir i)
                                (out := (C.carrier⋉C.carrier).pos)
                                obvious.symm
                                (by rewrite [← dir_eq_new]; simp)


    let dir_eq_specialized {C : Comonoid2} {i : C.carrier.pos}: C.carrier.dir (C.comult.onPos i).b = C.carrier.dir (C.comult.onPos (C.comult.onPos i).b).b  := by
      simp only [bookkeeping_new i]

    have fst_do_i_have {x : C.carrier.dir (C.comult.onPos i).b} :
                        (C.comult.onPos (C.comult.onPos i).b).next
                          ((dir_eq_new :
                              C.carrier.dir (C.comult.onPos i).b =
                                C.carrier.dir (C.comult.onPos (C.comult.onPos i).b).b) ▸
                            x) =
                        (C.comult.onPos i).next
                          ((dir_eq_new : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).b) ▸
                            (dir_eq_new.symm : C.carrier.dir (C.comult.onPos i).b = C.carrier.dir i) ▸ x)
                        := by
                            conv =>
                              rhs
                              rewrite [← cast_id (a := i) (c := x) (β := C.carrier.dir) (bookkeeping_new i).symm dir_eq_new]
                            exact fst_do_i_actual (i := i)
                                                  (i' := (C.comult.onPos i).b)
                                                  (β := λ x ↦ C.carrier.dir (C.comult.onPos x).b)
                                                  (x_general := fun x y => (C.comult.onPos x).next y)
                                                  (bookkeeping_new i).symm
                                                  x
                                                  dir_eq_new
    sorry


    -- let very_small {x : C.carrier.dir (C.comult.onPos i).fst}
    --                {qd : C.carrier.dir ((C.comult.onPos (C.comult.onPos i).fst).snd (dir_eq ▸ x)) }
    --                :
    --                (⟨ (dir_eq : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).fst) ▸
    --                     (dir_eq.symm : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir i) ▸ x, dir_different_casts_eq ▸ qd ⟩ : @Sigma (C.carrier.dir (C.comult.onPos i).fst)
    --                                                                                    (fun d => C.carrier.dir ((C.comult.onPos i).snd d)))
    --                =
    --                (dir_composed_eq ▸
    --                (⟨ dir_eq ▸ x , qd ⟩ : @Sigma (C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst)
    --                                              (fun d => C.carrier.dir (Sigma.snd (C.comult.onPos (C.comult.onPos i).fst) d)))
    --                 : (C.carrier◁C.carrier).dir (C.comult.onPos i))
    --                := sigmas_eq (β₁ := (λ {i} d ↦ C.carrier.dir ((C.comult.onPos i).snd d)))
    --                             dir_eq
    --                             dir_eq
    --                             qd
    --                             dir_different_casts_eq
    --                             dir_composed_eq
    --                             (bookkeeping i)

    -- let dirs_equal_lemma {α : Type}
    --                      {β : α → Type} -- λ i ↦ (C.carrier◁C.carrier).dir (C.comult.onPos i)
    --                      {out : α → Type} -- C.carrier.dir
    --                      {i i' : α}  -- i, (C.comult.onPos i).fst
    --                      {dir_i : β i} -- ⟨ dir_eq ▸ dir_eq.symm ▸ x, dir_different_casts_eq ▸ qd ⟩
    --                      {dir_i' : β i'} -- ⟨ dir_eq ▸ x, qd ⟩
    --                      (f : (x : α) → β x → out x) -- C.comult.onDir
    --                      (h : out i = out i') -- dir_eq
    --                      (k : i = i') -- (bookkeeping i).symm
    --                      (t : β i = β i')
    --                      (l : dir_i = t ▸ dir_i')
    --                      : h ▸ f i dir_i
    --                      = f i' dir_i'
    --                      := by
    --                      cases k
    --                      simp only [l]

    -- let dirs_equal {x : C.carrier.dir (C.comult.onPos i).fst}
    --                {qd : C.carrier.dir ((C.comult.onPos (C.comult.onPos i).fst).snd (dir_eq ▸ x)) }
    --               :
    --                let tgt_dir_1 : (C.carrier◁C.carrier).dir (C.comult.onPos i) := ⟨ dir_eq ▸ dir_eq.symm ▸ x, dir_different_casts_eq ▸ qd ⟩
    --                let tgt_dir_2 : (C.carrier◁C.carrier).dir (C.comult.onPos (C.comult.onPos i).fst) := ⟨ dir_eq ▸ x, qd ⟩

    --                (dir_eq ▸
    --                (C.comult.onDir i tgt_dir_1 : C.carrier.dir i))
    --                =
    --                ((C.comult.onDir (C.comult.onPos i).fst tgt_dir_2) : C.carrier.dir (C.comult.onPos i).fst)
    --               := dirs_equal_lemma (α := C.carrier.pos)
    --                                   (β := λ i ↦ (C.carrier◁C.carrier).dir (C.comult.onPos i))
    --                                   (out := C.carrier.dir)
    --                                   C.comult.onDir
    --                                   dir_eq
    --                                   (bookkeeping i).symm
    --                                   dir_composed_eq
    --                                   very_small

    -- let pushed_cast {x : C.carrier.dir (C.comult.onPos i).fst}
    --           : (fst_do_i_have ▸
    --               (fun qd =>
    --                 (C.comult.onPos i).snd
    --                   (dir_eq ▸ C.comult.onDir i ⟨ dir_eq ▸ dir_eq.symm ▸ x, qd ⟩) : C.carrier.dir ((C.comult.onPos i).snd ((dir_eq : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).fst) ▸ (dir_eq.symm: C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir i) ▸ x)) → C.carrier.pos ))
    --             =
    --             (fun qd =>
    --               (C.comult.onPos i).snd
    --                 (dir_eq ▸ C.comult.onDir i ⟨ dir_eq ▸ dir_eq.symm ▸ x, dir_different_casts_eq ▸ qd ⟩) : C.carrier.dir ((C.comult.onPos (C.comult.onPos i).fst).snd ((_ : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst) ▸ x)) → C.carrier.pos)
    --             :=
    --             push_cast_in_lambda dir_different_casts
    --                                 (fun qd =>
    --                                  (C.comult.onPos i).snd
    --                                    (dir_eq ▸ C.comult.onDir i ⟨ dir_eq ▸ dir_eq.symm ▸ x, qd ⟩))

    -- let same_type {x : C.carrier.dir (C.comult.onPos i).fst}
    --           : (fun qd =>
    --               (C.comult.onPos i).snd
    --                 (C.comult.onDir (C.comult.onPos i).fst ⟨ dir_eq ▸ x, qd ⟩))
    --               =
    --             (fun qd =>
    --               (C.comult.onPos i).snd
    --                 (dir_eq ▸ C.comult.onDir i ⟨ dir_eq ▸ dir_eq.symm ▸ x, dir_different_casts_eq ▸ qd ⟩))
    --           := by
    --           funext qd
    --           rewrite [← dirs_equal (x := x) (qd := qd)]
    --           rfl

    -- let innit {x : C.carrier.dir (C.comult.onPos i).fst}
    --           : (fun qd =>
    --               (C.comult.onPos i).snd
    --                 (C.comult.onDir (C.comult.onPos i).fst ⟨ dir_eq ▸ x, qd ⟩) : C.carrier.dir ((C.comult.onPos (C.comult.onPos i).fst).snd ((_ : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst) ▸ x)) → C.carrier.pos)
    --               =
    --               (fst_do_i_have ▸
    --               (fun qd =>
    --                 (C.comult.onPos i).snd
    --                   (dir_eq ▸ C.comult.onDir i ⟨ dir_eq ▸ dir_eq.symm ▸ x, qd ⟩) : C.carrier.dir ((C.comult.onPos i).snd ((dir_eq : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).fst) ▸ (dir_eq.symm: C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir i) ▸ x)) → C.carrier.pos ))
    --             := by
    --             funext y
    --             conv =>
    --               rhs
    --               rewrite [pushed_cast]
    --             rewrite [← same_type (x := x)]
    --             rfl

    -- have do_i_have_this :
    --                 -- original lhs
    --                 (fun pd =>
    --                   { fst := (C.comult.onPos (C.comult.onPos i).fst).snd (dir_eq_specialized ▸ pd),
    --                     snd := fun qd => (C.comult.onPos i).snd (C.comult.onDir (C.comult.onPos i).fst ⟨ dir_eq_specialized ▸ pd , qd ⟩ )
    --                     } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
    --                 =
    --                 -- new lhs
    --                 (fun pd =>
    --                   { fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
    --                     snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ pd , qd ⟩))
    --                     } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
    --                 := by
    --                 funext x
    --                 exact sigma_eq fst_do_i_have innit

    -- let cast_on_arg {α β out : Type}
    --                  { f : β → out }
    --                  (obvious : (β → out) = (α → out))
    --                  (dir_eq : α = β)
    --                 : (obvious ▸ f)
    --                   =
    --                   (fun x => f (dir_eq ▸ x)) := by
    --                   cases dir_eq
    --                   rfl

    -- let cast_on_arg_incredible_stupidity
    --                 {α β χ out : Type}
    --                 { f : β → out }
    --                 (dir_eq : α = β)
    --                 (dir_eq' : β = χ)
    --                  :
    --                  (fun x => f (dir_eq ▸ dir_eq ▸ x))
    --                  =
    --                  (fun x => f (dir_eq'.symm ▸ dir_eq' ▸ x)) := by
    --                  cases dir_eq
    --                  cases dir_eq'
    --                  rfl

    -- have yes_you_may : (fun pd =>
    --                   { fst := (C.comult.onPos i).snd (dir_eq ▸ dir_eq ▸ pd),
    --                     snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ dir_eq ▸ pd , qd ⟩))
    --                     } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
    --                   =
    --                   (fun pd =>
    --                     { fst := (C.comult.onPos i).snd (dir_eq.symm ▸ dir_eq ▸ pd),
    --                       snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq.symm ▸ dir_eq ▸ pd , qd ⟩))
    --                       } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
    --                   := cast_on_arg_incredible_stupidity
    --                                 (out := (C.carrier◁C.carrier).pos )
    --                                 (f := fun pd =>
    --                                   { fst := (C.comult.onPos i).snd pd,
    --                                     snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ pd , qd ⟩))
    --                                     })
    --                                 dir_eq
    --                                 dir_eq

    -- have may_i : Eq.rec
    --                  (fun pd =>
    --                    {
    --                      fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
    --                      snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ C.comult.onDir i { fst := dir_eq ▸ pd, snd := qd }) })
    --                  obvious
    --              =
    --              (fun pd =>
    --                { fst := (C.comult.onPos i).snd (dir_eq ▸ dir_eq ▸ pd),
    --                  snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ dir_eq ▸ pd , qd ⟩))
    --                  } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
    --              := cast_on_arg obvious dir_eq.symm

    -- have pre_now_the_other : Eq.rec
    --                             (fun pd =>
    --                               {
    --                                 fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
    --                                 snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ C.comult.onDir i { fst := dir_eq ▸ pd, snd := qd }) })
    --                             obvious
    --                         =
    --                         (fun pd =>
    --                           { fst := (C.comult.onPos i).snd (dir_eq.symm ▸ dir_eq ▸ pd),
    --                             snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq.symm ▸ dir_eq ▸ pd , qd ⟩))
    --                             } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
    --                         := by
    --                         funext pd
    --                         conv =>
    --                           lhs
    --                           rewrite [may_i]
    --                           rewrite [yes_you_may]

    -- have pre_even : (fun pd =>
    --                 { fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
    --                   snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ pd , qd ⟩))
    --                   } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
    --                 =
    --                 (fun pd =>
    --                   { fst := (C.comult.onPos i).snd (dir_eq.symm ▸ dir_eq ▸ pd),
    --                     snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq.symm ▸ dir_eq ▸ pd , qd ⟩))
    --                     } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
    --                 := cast_on_arg_incredible_stupidity
    --                                 (out := (C.carrier◁C.carrier).pos )
    --                                 (f := fun pd =>
    --                                   { fst := (C.comult.onPos i).snd pd,
    --                                     snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ pd , qd ⟩))
    --                                     })
    --                                 dir_eq
    --                                 dir_eq

    -- have now_the_other_one : (fun pd =>
    --                           { fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
    --                             snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ pd , qd ⟩))
    --                             } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
    --                           =
    --                           obvious ▸
    --                           (fun pd =>
    --                            { fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
    --                              snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ pd , qd ⟩))
    --                              } : C.carrier.dir i → (C.carrier◁C.carrier).pos )
    --                           := by
    --                           rewrite [pre_now_the_other]
    --                           exact pre_even


    -- have now_rhs : (fun pd =>
    --                   { fst := (C.comult.onPos (C.comult.onPos i).fst).snd (dir_eq_specialized ▸ pd),
    --                     snd := fun qd => (C.comult.onPos i).snd (C.comult.onDir (C.comult.onPos i).fst ⟨ dir_eq_specialized ▸ pd , qd ⟩)
    --                     } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
    --                =
    --                obvious ▸
    --                (fun pd =>
    --                   { fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
    --                     snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ pd , qd ⟩))
    --                     } : C.carrier.dir i → (C.carrier◁C.carrier).pos )
    --                := by
    --                conv =>
    --                  lhs
    --                  rewrite [do_i_have_this]
    --                rewrite [now_the_other_one]
    --                rfl

    -- have pre_now_we'd_talk_even_more :
    --             obvious ▸
    --             (fun x => C.comult.onPos (cod x) : C.carrier.dir i → (C.carrier◁C.carrier).pos)
    --             =
    --             obvious ▸
    --             (fun pd =>
    --                   { fst := cod pd,
    --                     snd := fun qd => cod (comp pd qd)
    --                     } : C.carrier.dir i → (C.carrier◁C.carrier).pos )
    --             := by
    --             simp only [now_lhs, now_rhs] at now_we'd_be_talking
    --             exact now_we'd_be_talking

    -- have now_we'd_talk_even_more :
    --             (fun x => C.comult.onPos (cod x) : C.carrier.dir i → (C.carrier◁C.carrier).pos)
    --             =
    --             (fun pd =>
    --                   { fst := cod pd,
    --                     snd := fun qd => cod (comp pd qd)
    --                     } : C.carrier.dir i → (C.carrier◁C.carrier).pos ) := by
    --                     apply remove_casts
    --                     exact pre_now_we'd_talk_even_more

    -- have e_isso :
    --       C.comult.onPos (cod f)
    --       =
    --       { fst := cod f,
    --         snd := (fun qd => cod (comp f qd) : C.carrier.dir (cod f) → C.carrier.pos ) : (C.carrier◁C.carrier).pos }
    --       := congrFun now_we'd_talk_even_more f

    -- have e_isso_mesmo :
    --       (C.comult.onPos (cod f)).snd
    --       =
    --       Eq.rec (motive := fun x h => C.carrier.dir x → C.carrier.pos)
    --       (fun qd => cod (comp f qd))
    --       (_ : cod f = (C.comult.onPos (cod f)).fst)
    --       := snd_heq e_isso

    -- have agora_imagine : Eq.rec (motive := fun x h => C.carrier.dir x → C.carrier.pos)
    --                              (fun qd => cod (comp f qd))
    --                              (_ : cod f = (C.comult.onPos (cod f)).fst)
    --                      =
    --                      (fun qd => cod (comp f (dir_eq ▸ qd)))
    --   := push_cast_in_lambda
    --             (x := cod f)
    --             (y := (C.comult.onPos (cod f)).fst)
    --             (by rewrite [bookkeeping (cod f)]; simp)
    --             (fun qd => cod (comp f qd))

    -- have que_e_possivel : (C.comult.onPos (cod f)).snd
    --                       =
    --                       (fun qd => cod (comp f (dir_eq ▸ qd))) := by
    --   simp only [e_isso_mesmo, agora_imagine]


    -- have e_isso_demais : cod g =
    --                      cod (comp f (dir_eq ▸ g))
    --   := congrFun que_e_possivel (dir_eq ▸ g)

    -- have hihi : cod (comp f (dir_eq.symm ▸ dir_eq ▸ g))
    --             =
    --             cod (comp f g)
    --             := by
    --             rewrite [← cast_id' dir_eq]
    --             rfl
    -- rewrite [hihi] at e_isso_demais
    -- exact e_isso_demais
def on_pos_eq_new {f g : polymap p (p ⋉ p ⋉ p)}
              {i : p.pos}
              (x : f = g)
              : (f.onPos i) = (g.onPos i) := congrFun (congrArg (λ x ↦ x.onPos) x) i

def on_dir_eq_new {f : polymap p (p ⋉ p ⋉ p)} {g : polymap p ((p ⋉ p) ⋉ p)}
  {i : p.pos}
  (x : f = composemap g subst2.associator.hom)
  (pos_eq : f.onPos i = subst2.associator.hom.onPos (g.onPos i))
  :
  (fun (d : (p ⋉ p ⋉ p).dir (f.onPos i))  => f.onDir i d)
  =
  (fun (d : (p ⋉ p ⋉ p).dir (f.onPos i)) => g.onDir i ⟨ ⟨ (pos_eq ▸ d).t, (pos_eq ▸ d).two.t ⟩ , (pos_eq ▸ d).two.two  ⟩  )
  := by
  cases x
  rfl

def on_dir_eq_no_cast_new {f : polymap p (p ⋉ p ⋉ p)} {g : polymap p ((p ⋉ p) ⋉ p)}
  {i : p.pos}
  (x : f = composemap g subst2.associator.hom)
  :
  (fun (df : (p ⋉ p ⋉ p).dir (f.onPos i)) =>
  (f.onDir i df : p.dir i))
  =
  (fun (df : (p ⋉ p ⋉ p).dir (f.onPos i)) =>
  let dg : (p ⋉ p ⋉ p).dir (subst2.associator.hom.onPos $ g.onPos i) := by
    rewrite [x] at df
    exact df
  (g.onDir i (subst2.associator.hom.onDir _ dg) : p.dir i))
  := by
  subst x
  simp_all only [eq_mp_eq_cast, cast_eq]
  rfl

def coassoc_dir_statement_new {C : Comonoid2}
                          {i j k l : C.carrier.pos}
                          (f : C.carrier.dir i)
                          (g : C.carrier.dir (cod_new f))
                          (h : C.carrier.dir (cod_new g))
                          :
                          comp_new f (comp_new g h)
                          =
                          comp_new (comp_new f g) (coassoc_pos_statement_new f g ▸ h) :=
  by

    have sacred_pos_left : (C.carrier⋉C.carrier⋉C.carrier).pos := ⟨(C.comult.onPos i).b, λ pd ↦ C.comult.onPos ((C.comult.onPos i).next pd)⟩
    have sacred_pos_right : (C.carrier⋉C.carrier⋉C.carrier).pos := ⟨ (C.comult.onPos (C.comult.onPos i).b).b , λ pd ↦ ⟨ (C.comult.onPos (C.comult.onPos i).b).next pd , λ qd ↦ (C.comult.onPos i).next ((comp_2_new pd qd)) ⟩ ⟩
    have pos_eq :
        (⟨posAtDir_new i, λ pd ↦ C.comult.onPos (cod_new pd)⟩ : (C.carrier⋉C.carrier⋉C.carrier).pos)  =
        (⟨posAtDir_new (posAtDir_new i) , λ pd ↦ ⟨ cod_new pd , λ qd ↦ cod_new (comp_new pd qd) ⟩ ⟩ : (C.carrier⋉C.carrier⋉C.carrier).pos)
      := on_pos_eq_new (i := i) C.coassoc

    have coassoc_onDir := on_dir_eq_new (i := i) C.coassoc pos_eq

    simp [composemap, subst2.whiskerLeft, subst2.whiskerRight, subst2.associator.hom] at coassoc_onDir

    -- simp [composemap, subst.whiskerLeft, subst.whiskerRight, subst.associator.hom, applyMap, Function.comp_apply, cast] at coassoc_onDir_2


    let f' : C.carrier.dir (posAtDir_new i) := dir_eq_new ▸ f
    let g' : C.carrier.dir (posAtDir_new (cod_new f)) := dir_eq_new ▸ g


    let composed := pos_eq ▸ { t := f', two := { t := g', two := h } : (C.carrier⋉C.carrier⋉C.carrier).dir ⟨posAtDir_new i, λ pd ↦ C.comult.onPos (cod_new pd)⟩ }
    let some_kind_of_f := composed.t

    let hmm : C.carrier.dir ⟨posAtDir_new (posAtDir_new i), fun pd => ⟨cod_new pd, fun qd => cod_new (comp_new pd qd)⟩⟩.fst = posAtDir_new (posAtDir_new i) := by sorry

    let some_kind_of_g := composed.snd.fst
    let some_kind_of_h := composed.snd.snd

    have at_fgh_2 :
      comp f (comp g h)
      =
      let dg := (congrArg (fun _a => (C.carrier◁C.carrier◁C.carrier).dir (_a.onPos i)) C.coassoc).mp ⟨f', ⟨g', h⟩⟩;
      (composemap C.comult (subst.whiskerRight C.comult)).onDir i
        (subst.associator.hom.onDir ((composemap C.comult (subst.whiskerRight C.comult)).onPos i) dg)
     := by
     exact congrFun coassoc_onDir_2 ⟨ f' , g' , h ⟩

    have at_fgh
    : comp f (comp g h)
      =
      comp_2
        (comp_2
          some_kind_of_f
          some_kind_of_g)
        some_kind_of_h
     := by
     exact congrFun coassoc_onDir ⟨ f' , g' , h ⟩

    -- have x : cod f = cod_2 f'' := by
    --   simp [across_cods, bookkeeping i]
    --   congr!
    --   . simp [bookkeeping]
    --   . simp_all only [heq_eqRec_iff_heq, heq_eq_eq, f', g', f'']

    -- have coassoc_pos_stmt_2 : (cod g) = (cod_2 (comp_2 f'' (x ▸ g))) := by
    --   simp_all only [eq_mp_eq_cast, f', f'', some_kind_of_f, composed, g', some_kind_of_g, some_kind_of_h]
    --   obtain ⟨fst, snd⟩ := composed
    --   sorry
    -- let hmm : comp_2 (comp_2 f'' (x ▸ g)) (coassoc_pos_stmt_2 ▸ h)
    --          =
    --          comp (comp f g) (coassoc_pos_statement f g ▸ h) :=
    --          by
    --          sorry

    -- have rewritten
    -- : comp_2
    --     (comp_2
    --           ((pos_eq ▸ { fst := f', snd := { fst := g', snd := h }} : (C.carrier◁C.carrier◁C.carrier).dir ⟨ (C.comult.onPos (C.comult.onPos i).fst).fst , λ pd ↦ ⟨ cod_2 pd , λ qd ↦ cod_2 (comp_2 pd qd) ⟩ ⟩ ).fst)
    --           ((pos_eq ▸ { fst := f', snd := { fst := g', snd := h } : (C.carrier◁C.carrier◁C.carrier).dir ⟨(C.comult.onPos i).fst, λ pd ↦ C.comult.onPos (cod_2 pd)⟩ }).snd.fst))
    --     ((pos_eq ▸ { fst := f', snd := { fst := g', snd := h } : (C.carrier◁C.carrier◁C.carrier).dir ⟨(C.comult.onPos i).fst, λ pd ↦ C.comult.onPos (cod_2 pd)⟩  }).snd.snd )
    --  =
    --   comp_2 (comp_2 f'' (x ▸ g)) (coassoc_pos_stmt_2 ▸ h) := by
    --   congr!
    --   .
    --     suggest_tactics

    --     sorry
    --   . sorry
    --   . sorry
    sorry

end CategoryTheory
