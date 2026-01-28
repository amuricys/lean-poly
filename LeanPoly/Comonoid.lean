import Init.Prelude
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Comon_
import «LeanPoly».Poly
import «LeanPoly».Lemmas
import LeanCopilot

namespace CategoryTheory
set_option pp.proofs true
set_option pp.showLetValues true

open Comon_Class
open MonoidalCategory

-- We work with Poly using the substitution monoidal structure (◁, y)
-- A comonoid in Poly is now represented by Comon_Class p for p : Poly
-- The Mathlib notation gives us:
--   ε[p] : p ⟶ 𝟙_ Poly  (which is y)
--   Δ[p] : p ⟶ p ⊗ p    (which is p ◁ p under the subst monoidal structure)

-- The axioms from Comon_Class are:
-- counit_comul : Δ ≫ ε ▷ p = (λ_ p).inv
-- comul_counit : Δ ≫ p ◁ ε = (ρ_ p).inv
-- comul_assoc  : Δ ≫ p ◁ Δ = Δ ≫ (Δ ▷ p) ≫ (α_ p p p).hom

instance : Category Poly := Poly.category
instance : MonoidalCategoryStruct Poly := Poly.subst.monoidalStruct
instance : MonoidalCategory Poly := Poly.subst.monoidal
variable {p : Poly} [Comon_Class p]

def posAtDir (i : p.pos) : p.pos :=
  (Δ[p].onPos i).fst

lemma bookkeeping (i : p.pos) : posAtDir i = i :=
  fst_eq (congrArg (λ x ↦ x.onPos i) (comul_counit p))

lemma dir_eq {i : p.pos} : p.dir i = p.dir (posAtDir i) := by
  rewrite [bookkeeping i]
  rfl

def cod {i : p.pos} (f : p.dir i) : p.pos := by
    exact (Δ[p].onPos i).snd (dir_eq (p := p) ▸ f)

def comp {i : p.pos}
         (f : p.dir i)
         (g : p.dir (cod f)) :
         p.dir i :=
          Δ[p].onDir i ⟨ dir_eq (p := p) ▸ f , g ⟩

lemma dir_cast_id {i : p.pos} {x : p.dir (Δ[p].onPos i).fst} :
                    (Δ[p].onPos i).snd
                          ((dir_eq : p.dir i = p.dir (Δ[p].onPos i).fst) ▸
                            (dir_eq.symm : p.dir (Δ[p].onPos i).fst = p.dir i) ▸ x)
                    =
                    (Δ[p].onPos i).snd x
                    := by
                    rewrite [← cast_id (a := i) (c := x) (β := p.dir) (bookkeeping i).symm dir_eq]
                    rfl


lemma need_this {i : p.pos} {x : p.dir (Δ[p].onPos i).fst} :
                (Δ[p].onPos (Δ[p].onPos i).fst).snd
                  ((dir_eq :
                      p.dir (Δ[p].onPos i).fst =
                        p.dir (Δ[p].onPos (Δ[p].onPos i).fst).fst) ▸
                    x) =
                (Δ[p].onPos i).snd x
                := fst_do_i_actual (i := i)
                                   (i' := (Δ[p].onPos i).fst)
                                   (β := λ x ↦ p.dir (Δ[p].onPos x).fst)
                                   (x_general := fun x y => (Δ[p].onPos x).snd y)
                                   (bookkeeping i).symm
                                   x
                                   dir_eq

lemma dir_different_casts {i : p.pos} {x : p.dir (Δ[p].onPos i).fst} :
                    (Δ[p].onPos i).snd
                      ((dir_eq : p.dir i = p.dir (Δ[p].onPos i).fst) ▸
                        (dir_eq.symm : p.dir (Δ[p].onPos i).fst = p.dir i) ▸ x)
                    =
                    (Δ[p].onPos (Δ[p].onPos i).fst).snd
                      ((dir_eq : p.dir (Δ[p].onPos i).fst = p.dir (Δ[p].onPos (Δ[p].onPos i).fst).fst) ▸ x)
                    := by
                    rewrite [← cast_id (a := i) (c := x) (β := p.dir) (bookkeeping i).symm dir_eq]
                    rewrite [need_this]
                    simp

lemma dir_different_casts_eq {i : p.pos} {x : p.dir (Δ[p].onPos i).fst} :
                    p.dir ((Δ[p].onPos i).snd
                          ((dir_eq : p.dir i = p.dir (Δ[p].onPos i).fst) ▸
                            (dir_eq.symm : p.dir (Δ[p].onPos i).fst = p.dir i) ▸ x))
                    =
                    p.dir ((Δ[p].onPos (Δ[p].onPos i).fst).snd
                      ((dir_eq : p.dir (Δ[p].onPos i).fst = p.dir (Δ[p].onPos (Δ[p].onPos i).fst).fst) ▸
                      x))
                    := by
                    rewrite [← cast_id (a := i) (c := x) (β := p.dir) (bookkeeping i).symm dir_eq]
                    rewrite [need_this]
                    simp


lemma dir_composed_eq {i : p.pos} :
                      (p◁p).dir (Δ[p].onPos i) =
                      (p◁p).dir (Δ[p].onPos (posAtDir i))
                      := by
                      rewrite [bookkeeping i]
                      rfl


def on_pos_eq {f g : polymap p (p ◁ p ◁ p)}
              {i : p.pos}
              (x : f = g)
              : (f.onPos i) = (g.onPos i) := congrFun (congrArg (λ x ↦ x.onPos) x) i

def on_dir_eq {f : polymap p (p ◁ p ◁ p)} {g : polymap p ((p ◁ p) ◁ p)}
  {i : p.pos}
  (x : f = composemap g subst.associator.hom)
  (pos_eq : f.onPos i = subst.associator.hom.onPos (g.onPos i))
  :
  (fun (d : (p ◁ p ◁ p).dir (f.onPos i))  => f.onDir i d)
  =
  (fun (d : (p ◁ p ◁ p).dir (f.onPos i)) => g.onDir i ⟨ ⟨ (pos_eq ▸ d).fst, (pos_eq ▸ d).snd.fst ⟩ , (pos_eq ▸ d).snd.snd  ⟩  )
  := by
  cases x
  rfl

def on_pos_eq_id {f g : polymap p (y ◁ p)}
                 {i : p.pos}
                 (x : f = g)
                 : (f.onPos i).snd () = (g.onPos i).snd () := by
                 have H := congrFun (congrArg (λ x ↦ x.onPos) x) i
                 subst x
                 simp_all only

def on_dir_eq_id {f : polymap p (y ◁ p)} {g : polymap p (y ◁ p)}
  {i : p.pos}
  (x : f = g)

  (pos_eq : (f.onPos i).snd () = (g.onPos i).snd ())
  :
  (fun (d : (y ◁ p).dir (f.onPos i))  => f.onDir i d)
  =
  (fun (d : (y ◁ p).dir (f.onPos i)) => g.onDir i ⟨ () , pos_eq ▸ d.snd  ⟩  )
  := by
  cases x
  rfl

def on_pos_eq_id_ {f g : polymap p (p ◁ y)}
                 {i : p.pos}
                 (x : f = g)
                 : (f.onPos i).fst = (g.onPos i).fst := by
                 have H := congrFun (congrArg (λ x ↦ x.onPos) x) i
                 subst x
                 simp_all only

def on_dir_eq_id_ {f : polymap p (p ◁ y)} {g : polymap p (p ◁ y)}
  {i : p.pos}
  (x : f = g)
  (pos_eq : (f.onPos i).fst = (g.onPos i).fst )
  :
  (fun (d : (p ◁ y).dir (f.onPos i))  => f.onDir i d)
  =
  (fun (d : (p ◁ y).dir (f.onPos i)) => g.onDir i ⟨ pos_eq ▸ d.fst  , ()  ⟩  )
  := by
  cases x
  rfl


lemma coassoc_pos_statement {i : p.pos}
                            (f : p.dir i)
                            (g : p.dir (cod f)) :
                            cod (comp f g) = cod g := by
    have coassoc_onPos := congrArg (λ x => x.onPos) (comul_assoc p)

    -- simp [composemap, subst.whiskerRight, subst.whiskerLeft, applyMap, subst.associator.hom, Function.comp, subst] at coassoc_onPos

    let at_i := congrFun coassoc_onPos i

    have wait : (fun x => Δ[p].onPos ((Δ[p].onPos i).snd x) : p.dir (Δ[p].onPos i).fst → (p◁p).pos)
                =
                (bookkeeping (Δ[p].onPos i).fst) ▸
                 (fun pd =>
                   { fst := (Δ[p].onPos (Δ[p].onPos i).fst).snd pd,
                     snd := fun qd => (Δ[p].onPos i).snd (Δ[p].onDir (Δ[p].onPos i).fst ⟨ pd , qd ⟩)
                     } : p.dir (Δ[p].onPos (Δ[p].onPos i).fst).fst → (p◁p).pos )
                := snd_heq (h := at_i)

    have hard_rhs : Eq.rec (motive := fun x _ => p.dir x → (p ◁ p).pos)
                           (fun pd : p.dir (Δ[p].onPos (Δ[p].onPos i).fst).fst =>
                             { fst := (Δ[p].onPos (Δ[p].onPos i).fst).snd pd,
                               snd := fun qd =>
                                 (Δ[p].onPos i).snd
                                   (Δ[p].onDir (Δ[p].onPos i).fst { fst := pd, snd := qd }) } )
                           (bookkeeping ((Δ[p].onPos i).fst) : (Δ[p].onPos (Δ[p].onPos i).fst).fst = (Δ[p].onPos i).fst)
                    =
                    (fun pd =>
                      { fst := (Δ[p].onPos (Δ[p].onPos i).fst).snd (dir_eq (p := p) ▸ pd),
                        snd := fun qd => (Δ[p].onPos i).snd (Δ[p].onDir (Δ[p].onPos i).fst ⟨ dir_eq (p := p) ▸ pd , qd ⟩)
                        } : p.dir (Δ[p].onPos i).fst → (p◁p).pos )
                    := push_cast_in_lambda (χ := (p ◁ p).pos)
                                           (bookkeeping ((Δ[p].onPos i).fst))
                                           (fun (pd : p.dir (Δ[p].onPos (Δ[p].onPos i).fst).fst) =>
                                             { fst := (Δ[p].onPos (Δ[p].onPos i).fst).snd pd,
                                               snd := fun qd =>
                                                 (Δ[p].onPos i).snd (Δ[p].onDir (Δ[p].onPos i).fst { fst := pd, snd := qd }) })

    have now_we'd_be_talking :
                (fun x => Δ[p].onPos ((Δ[p].onPos i).snd x) : p.dir (Δ[p].onPos i).fst → (p◁p).pos)
                =
                (fun pd =>
                      { fst := (Δ[p].onPos (Δ[p].onPos i).fst).snd (dir_eq (p := p) ▸ pd),
                        snd := fun qd => (Δ[p].onPos i).snd (Δ[p].onDir (Δ[p].onPos i).fst ⟨ dir_eq (p := p) ▸ pd , qd ⟩)
                        } : p.dir (Δ[p].onPos i).fst → (p◁p).pos )
                := by
                conv =>
                  rhs
                  rw [← hard_rhs]
                exact wait

    have obvious : (p.dir i → (p◁p).pos)
                   =
                   (p.dir (posAtDir i) → (p◁p).pos)
                   := by
                   rewrite [bookkeeping i]
                   rfl

    have now_lhs : (fun x => Δ[p].onPos ((Δ[p].onPos i).snd x) : p.dir (Δ[p].onPos i).fst → (p◁p).pos)
                   =
                   obvious ▸
                   (fun x => Δ[p].onPos ((Δ[p].onPos i).snd (dir_eq (p := p) ▸ x)) : p.dir i → (p◁p).pos)
                   := lhs_lemma (arg1 := p.dir (posAtDir i))
                                (arg2 := p.dir i)
                                (out := (p◁p).pos)
                                obvious.symm
                                (by rewrite [← dir_eq]; simp)

    let dir_eq_specialized {i : p.pos}: p.dir (posAtDir i) = p.dir (posAtDir (posAtDir i))  := by
      simp only [bookkeeping i]

    have fst_do_i_have {x : p.dir (Δ[p].onPos i).fst} :
                        (Δ[p].onPos (Δ[p].onPos i).fst).snd
                          ((dir_eq :
                              p.dir (Δ[p].onPos i).fst =
                                p.dir (Δ[p].onPos (Δ[p].onPos i).fst).fst) ▸
                            x) =
                        (Δ[p].onPos i).snd
                          ((dir_eq : p.dir i = p.dir (Δ[p].onPos i).fst) ▸
                            (dir_eq.symm : p.dir (Δ[p].onPos i).fst = p.dir i) ▸ x)
                        := by
                            conv =>
                              rhs
                              rewrite [← cast_id (a := i) (c := x) (β := p.dir) (bookkeeping i).symm dir_eq]
                            exact need_this

    let sigmas_eq {α : Type}
                  {χ₁ : α → Type} -- λ i → (p.dir (Δ[p].onPos i).fst)
                  {χ₂ : α → Type} -- λ i → (p.dir i)
                  {β₁ : {a : α} → (χ₁ a) → Type} -- (λ {i} d ↦ p.dir ((Δ[p].onPos i).snd d))
                  {i i' : α} -- i, (Δ[p].onPos i).fst
                  {x : χ₁ i} -- p.dir (Δ[p].onPos i).fst
                  (h : χ₁ i = χ₁ i') -- dir_eq : p.dir (Δ[p].onPos i).fst = p.dir (Δ[p].onPos (Δ[p].onPos i).fst).fst
                  (h' : χ₂ i = χ₁ i) -- dir_eq : p.dir i = p.dir (Δ[p].onPos i).fst
                  (qd : β₁ (a := i') (h ▸ x)) -- p.dir ((Δ[p].onPos (Δ[p].onPos i).fst).snd (dir_eq ▸ x))
                  (t : β₁ (a := i) (h'.symm ▸ h' ▸ x) = β₁ (a := i') (h ▸ x))
                  (u : Sigma (β₁ (a := i)) = Sigma (β₁ (a := i')))
                  (k : i' = i)
                  :
                    (⟨ h' ▸ (h'.symm ▸ x), t ▸ qd ⟩ : Sigma (β₁ (a := i)))
                    =
                    u ▸ (⟨ h ▸ x , qd ⟩ : Sigma (β₁ (a := i'))) := by
                    cases k
                    simp
                    apply cast_id''
                    exact h'.symm
    let very_small {x : p.dir (Δ[p].onPos i).fst}
                   {qd : p.dir ((Δ[p].onPos (Δ[p].onPos i).fst).snd (dir_eq (p := p) ▸ x)) }
                   :
                   (⟨ (dir_eq : p.dir i = p.dir (Δ[p].onPos i).fst) ▸
                        (dir_eq.symm : p.dir (Δ[p].onPos i).fst = p.dir i) ▸ x, dir_different_casts_eq (p := p) ▸ qd ⟩ : @Sigma (p.dir (Δ[p].onPos i).fst)
                                                                                       (fun d => p.dir ((Δ[p].onPos i).snd d)))
                   =
                   (dir_composed_eq (p := p) ▸
                   (⟨ dir_eq (p := p) ▸ x , qd ⟩ : @Sigma (p.dir (Δ[p].onPos (Δ[p].onPos i).fst).fst)
                                                 (fun d => p.dir (Sigma.snd (Δ[p].onPos (Δ[p].onPos i).fst) d)))
                    : (p◁p).dir (Δ[p].onPos i))
                   := sigmas_eq (β₁ := (λ {i} d ↦ p.dir ((Δ[p].onPos i).snd d)))
                                dir_eq
                                dir_eq
                                qd
                                dir_different_casts_eq
                                dir_composed_eq
                                (bookkeeping i)

    let dirs_equal_lemma {α : Type}
                         {β : α → Type} -- λ i ↦ (p◁p).dir (Δ[p].onPos i)
                         {out : α → Type} -- p.dir
                         {i i' : α}  -- i, (Δ[p].onPos i).fst
                         {dir_i : β i} -- ⟨ dir_eq ▸ dir_eq.symm ▸ x, dir_different_casts_eq ▸ qd ⟩
                         {dir_i' : β i'} -- ⟨ dir_eq ▸ x, qd ⟩
                         (f : (x : α) → β x → out x) -- Δ[p].onDir
                         (h : out i = out i') -- dir_eq
                         (k : i = i') -- (bookkeeping i).symm
                         (t : β i = β i')
                         (l : dir_i = t ▸ dir_i')
                         : h ▸ f i dir_i
                         = f i' dir_i'
                         := by
                         cases k
                         simp only [l]

    let dirs_equal {x : p.dir (Δ[p].onPos i).fst}
                   {qd : p.dir ((Δ[p].onPos (Δ[p].onPos i).fst).snd (dir_eq (p := p) ▸ x)) }
                  :
                   let tgt_dir_1 : (p◁p).dir (Δ[p].onPos i) := ⟨ dir_eq (p := p) ▸ (dir_eq (p := p)).symm ▸ x, dir_different_casts_eq (p := p) ▸ qd ⟩
                   let tgt_dir_2 : (p◁p).dir (Δ[p].onPos (Δ[p].onPos i).fst) := ⟨ dir_eq (p := p) ▸ x, qd ⟩

                   (dir_eq (p := p) ▸
                   (Δ[p].onDir i tgt_dir_1 : p.dir i))
                   =
                   ((Δ[p].onDir (Δ[p].onPos i).fst tgt_dir_2) : p.dir (Δ[p].onPos i).fst)
                  := dirs_equal_lemma (α := p.pos)
                                      (β := λ i ↦ (p◁p).dir (Δ[p].onPos i))
                                      (out := p.dir)
                                      Δ[p].onDir
                                      dir_eq
                                      (bookkeeping i).symm
                                      dir_composed_eq
                                      very_small

    let pushed_cast {x : p.dir (Δ[p].onPos i).fst}
              : (fst_do_i_have ▸
                  (fun qd =>
                    (Δ[p].onPos i).snd
                      (dir_eq (p := p) ▸ Δ[p].onDir i ⟨ dir_eq (p := p) ▸ (dir_eq (p := p)).symm ▸ x, qd ⟩) : p.dir ((Δ[p].onPos i).snd ((dir_eq : p.dir i = p.dir (Δ[p].onPos i).fst) ▸ (dir_eq.symm: p.dir (Δ[p].onPos i).fst = p.dir i) ▸ x)) → p.pos ))
                =
                (fun qd =>
                  (Δ[p].onPos i).snd
                    (dir_eq (p := p) ▸ Δ[p].onDir i ⟨ dir_eq (p := p) ▸ (dir_eq (p := p)).symm ▸ x, dir_different_casts_eq (p := p) ▸ qd ⟩) : p.dir ((Δ[p].onPos (Δ[p].onPos i).fst).snd ((_ : p.dir (Δ[p].onPos i).fst = p.dir (Δ[p].onPos (Δ[p].onPos i).fst).fst) ▸ x)) → p.pos)
                :=
                push_cast_in_lambda dir_different_casts
                                    (fun qd =>
                                     (Δ[p].onPos i).snd
                                       (dir_eq (p := p) ▸ Δ[p].onDir i ⟨ dir_eq (p := p) ▸ (dir_eq (p := p)).symm ▸ x, qd ⟩))

    let same_type {x : p.dir (Δ[p].onPos i).fst}
              : (fun qd =>
                  (Δ[p].onPos i).snd
                    (Δ[p].onDir (Δ[p].onPos i).fst ⟨ dir_eq (p := p) ▸ x, qd ⟩))
                  =
                (fun qd =>
                  (Δ[p].onPos i).snd
                    (dir_eq (p := p) ▸ Δ[p].onDir i ⟨ dir_eq (p := p) ▸ (dir_eq (p := p)).symm ▸ x, dir_different_casts_eq (p := p) ▸ qd ⟩))
              := by
              funext qd
              rewrite [← dirs_equal (x := x) (qd := qd)]
              rfl

    let innit {x : p.dir (Δ[p].onPos i).fst}
              : (fun qd =>
                  (Δ[p].onPos i).snd
                    (Δ[p].onDir (Δ[p].onPos i).fst ⟨ dir_eq (p := p) ▸ x, qd ⟩) : p.dir ((Δ[p].onPos (Δ[p].onPos i).fst).snd ((_ : p.dir (Δ[p].onPos i).fst = p.dir (Δ[p].onPos (Δ[p].onPos i).fst).fst) ▸ x)) → p.pos)
                  =
                  (fst_do_i_have ▸
                  (fun qd =>
                    (Δ[p].onPos i).snd
                      (dir_eq (p := p) ▸ Δ[p].onDir i ⟨ dir_eq (p := p) ▸ (dir_eq (p := p)).symm ▸ x, qd ⟩) : p.dir ((Δ[p].onPos i).snd ((dir_eq : p.dir i = p.dir (Δ[p].onPos i).fst) ▸ (dir_eq.symm: p.dir (Δ[p].onPos i).fst = p.dir i) ▸ x)) → p.pos ))
                := by
                funext y
                conv =>
                  rhs
                  rewrite [pushed_cast]
                rewrite [← same_type (x := x)]
                rfl

    have do_i_have_this :
                    -- original lhs
                    (fun pd =>
                      { fst := (Δ[p].onPos (Δ[p].onPos i).fst).snd (dir_eq_specialized ▸ pd),
                        snd := fun qd => (Δ[p].onPos i).snd (Δ[p].onDir (Δ[p].onPos i).fst ⟨ dir_eq_specialized ▸ pd , qd ⟩ )
                        } : p.dir (Δ[p].onPos i).fst → (p◁p).pos )
                    =
                    -- new lhs
                    (fun pd =>
                      { fst := (Δ[p].onPos i).snd (dir_eq (p := p) ▸ pd),
                        snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ (Δ[p].onDir i ⟨ dir_eq (p := p) ▸ pd , qd ⟩))
                        } : p.dir (Δ[p].onPos i).fst → (p◁p).pos )
                    := by
                    funext x
                    exact sigma_eq fst_do_i_have innit

    let cast_on_arg {α β out : Type}
                     { f : β → out }
                     (obvious : (β → out) = (α → out))
                     (dir_eq : α = β)
                    : (obvious ▸ f)
                      =
                      (fun x => f (dir_eq ▸ x)) := by
                      cases dir_eq
                      rfl

    let cast_on_arg_incredible_stupidity
                    {α β χ out : Type}
                    { f : β → out }
                    (dir_eq : α = β)
                    (dir_eq' : β = χ)
                     :
                     (fun x => f (dir_eq ▸ dir_eq ▸ x))
                     =
                     (fun x => f (dir_eq'.symm ▸ dir_eq' ▸ x)) := by
                     cases dir_eq
                     cases dir_eq'
                     rfl

    have yes_you_may : (fun pd =>
                      { fst := (Δ[p].onPos i).snd (dir_eq (p := p) ▸ dir_eq (p := p) ▸ pd),
                        snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ (Δ[p].onDir i ⟨ dir_eq (p := p) ▸ dir_eq (p := p) ▸ pd , qd ⟩))
                        } : p.dir (Δ[p].onPos i).fst → (p◁p).pos )
                      =
                      (fun pd =>
                        { fst := (Δ[p].onPos i).snd ((dir_eq (p := p)).symm ▸ dir_eq (p := p) ▸ pd),
                          snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ (Δ[p].onDir i ⟨ (dir_eq (p := p)).symm ▸ dir_eq (p := p) ▸ pd , qd ⟩))
                          } : p.dir (Δ[p].onPos i).fst → (p◁p).pos )
                      := cast_on_arg_incredible_stupidity
                                    (out := (p◁p).pos )
                                    (f := fun pd =>
                                      { fst := (Δ[p].onPos i).snd pd,
                                        snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ (Δ[p].onDir i ⟨ pd , qd ⟩))
                                        })
                                    dir_eq
                                    dir_eq

    have may_i : Eq.rec
                     (fun pd =>
                       {
                         fst := (Δ[p].onPos i).snd (dir_eq (p := p) ▸ pd),
                         snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ Δ[p].onDir i { fst := dir_eq (p := p) ▸ pd, snd := qd }) })
                     obvious
                 =
                 (fun pd =>
                   { fst := (Δ[p].onPos i).snd (dir_eq (p := p) ▸ dir_eq (p := p) ▸ pd),
                     snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ (Δ[p].onDir i ⟨ dir_eq (p := p) ▸ dir_eq (p := p) ▸ pd , qd ⟩))
                     } : p.dir (Δ[p].onPos i).fst → (p◁p).pos )
                 := cast_on_arg obvious dir_eq.symm

    have pre_now_the_other : Eq.rec
                                (fun pd =>
                                  {
                                    fst := (Δ[p].onPos i).snd (dir_eq (p := p) ▸ pd),
                                    snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ Δ[p].onDir i { fst := dir_eq (p := p) ▸ pd, snd := qd }) })
                                obvious
                            =
                            (fun pd =>
                              { fst := (Δ[p].onPos i).snd ((dir_eq (p := p)).symm ▸ dir_eq (p := p) ▸ pd),
                                snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ (Δ[p].onDir i ⟨ (dir_eq (p := p)).symm ▸ dir_eq (p := p) ▸ pd , qd ⟩))
                                } : p.dir (Δ[p].onPos i).fst → (p◁p).pos )
                            := by
                            funext pd
                            conv =>
                              lhs
                              rewrite [may_i]
                              rewrite [yes_you_may]

    have pre_even : (fun pd =>
                    { fst := (Δ[p].onPos i).snd (dir_eq (p := p) ▸ pd),
                      snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ (Δ[p].onDir i ⟨ dir_eq (p := p) ▸ pd , qd ⟩))
                      } : p.dir (Δ[p].onPos i).fst → (p◁p).pos )
                    =
                    (fun pd =>
                      { fst := (Δ[p].onPos i).snd ((dir_eq (p := p)).symm ▸ dir_eq (p := p) ▸ pd),
                        snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ (Δ[p].onDir i ⟨ (dir_eq (p := p)).symm ▸ dir_eq (p := p) ▸ pd , qd ⟩))
                        } : p.dir (Δ[p].onPos i).fst → (p◁p).pos )
                    := cast_on_arg_incredible_stupidity
                                    (out := (p◁p).pos )
                                    (f := fun pd =>
                                      { fst := (Δ[p].onPos i).snd pd,
                                        snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ (Δ[p].onDir i ⟨ pd , qd ⟩))
                                        })
                                    dir_eq
                                    dir_eq

    have now_the_other_one : (fun pd =>
                              { fst := (Δ[p].onPos i).snd (dir_eq (p := p) ▸ pd),
                                snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ (Δ[p].onDir i ⟨ dir_eq (p := p) ▸ pd , qd ⟩))
                                } : p.dir (Δ[p].onPos i).fst → (p◁p).pos )
                              =
                              obvious ▸
                              (fun pd =>
                               { fst := (Δ[p].onPos i).snd (dir_eq (p := p) ▸ pd),
                                 snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ (Δ[p].onDir i ⟨ dir_eq (p := p) ▸ pd , qd ⟩))
                                 } : p.dir i → (p◁p).pos )
                              := by
                              rewrite [pre_now_the_other]
                              exact pre_even


    have now_rhs : (fun pd =>
                      { fst := (Δ[p].onPos (Δ[p].onPos i).fst).snd (dir_eq_specialized ▸ pd),
                        snd := fun qd => (Δ[p].onPos i).snd (Δ[p].onDir (Δ[p].onPos i).fst ⟨ dir_eq_specialized ▸ pd , qd ⟩)
                        } : p.dir (Δ[p].onPos i).fst → (p◁p).pos )
                   =
                   obvious ▸
                   (fun pd =>
                      { fst := (Δ[p].onPos i).snd (dir_eq (p := p) ▸ pd),
                        snd := fun qd => (Δ[p].onPos i).snd (dir_eq (p := p) ▸ (Δ[p].onDir i ⟨ dir_eq (p := p) ▸ pd , qd ⟩))
                        } : p.dir i → (p◁p).pos )
                   := by
                   conv =>
                     lhs
                     rewrite [do_i_have_this]
                   rewrite [now_the_other_one]
                   rfl

    have pre_now_we'd_talk_even_more :
                obvious ▸
                (fun x => Δ[p].onPos (cod x) : p.dir i → (p◁p).pos)
                =
                obvious ▸
                (fun pd =>
                      { fst := cod pd,
                        snd := fun qd => cod (comp pd qd)
                        } : p.dir i → (p◁p).pos )
                := by
                simp only [now_lhs, now_rhs] at now_we'd_be_talking
                exact now_we'd_be_talking

    have now_we'd_talk_even_more :
                (fun x => Δ[p].onPos (cod x) : p.dir i → (p◁p).pos)
                =
                (fun pd =>
                      { fst := cod pd,
                        snd := fun qd => cod (comp pd qd)
                        } : p.dir i → (p◁p).pos ) := by
                        apply remove_casts
                        exact pre_now_we'd_talk_even_more

    have e_isso :
          Δ[p].onPos (cod f)
          =
          { fst := cod f,
            snd := (fun qd => cod (comp f qd) : p.dir (cod f) → p.pos ) : (p◁p).pos }
          := congrFun now_we'd_talk_even_more f

    have e_isso_mesmo :
          (Δ[p].onPos (cod f)).snd
          =
          Eq.rec (motive := fun x h => p.dir x → p.pos)
          (fun qd => cod (comp f qd))
          (_ : cod f = (Δ[p].onPos (cod f)).fst)
          := snd_heq e_isso

    have agora_imagine : Eq.rec (motive := fun x h => p.dir x → p.pos)
                                 (fun qd => cod (comp f qd))
                                 (_ : cod f = (Δ[p].onPos (cod f)).fst)
                         =
                         (fun qd => cod (comp f (dir_eq (p := p) ▸ qd)))
      := push_cast_in_lambda
                (x := cod f)
                (y := (posAtDir (cod f)))
                (by rewrite [bookkeeping (cod f)]; simp)
                (fun qd => cod (comp f qd))

    have que_e_possivel : (Δ[p].onPos (cod f)).snd
                          =
                          (fun qd => cod (comp f (dir_eq (p := p) ▸ qd))) := by
      simp only [e_isso_mesmo, agora_imagine]


    have e_isso_demais : cod g =
                         cod (comp f (dir_eq (p := p) ▸ g))
      := congrFun que_e_possivel (dir_eq (p := p) ▸ g)

    have hihi : cod (comp f ((dir_eq (p := p)).symm ▸ dir_eq (p := p) ▸ g))
                =
                cod (comp f g)
                := by
                rewrite [← cast_id' dir_eq]
                rfl
    rewrite [hihi] at e_isso_demais
    exact e_isso_demais.symm

def cod_2 {i : p.pos} (f : p.dir (posAtDir i)) : p.pos :=
    (Δ[p].onPos i).snd f

def comp_2 {i : p.pos}
         (f : p.dir (posAtDir i))
         (g : p.dir (cod_2 f)) :
         p.dir i :=
         Δ[p].onDir i ⟨ f , g ⟩

def id (i : p.pos) : p.dir i :=
    ε[p].onDir i ()

lemma cod_id {i : p.pos} : cod (id (i := i)) = i :=
  by
    unfold cod
    have H : (Δ[p] ≫ (ε[p] ▷ p)).onPos i
              =
             ((λ_ p).inv).onPos i := by
             rw [counit_comul]
    have M : (Δ[p].onPos i).snd (ε[p].onDir (Δ[p].onPos i).fst ())
              =
              i := congrFun (snd_eq H) ()
    have K : ε[p].onDir (Δ[p].onPos i).fst ()
             =
             dir_eq (p := p) ▸
             ε[p].onDir i () := npodese (Δ[p].onPos i).fst i (bookkeeping i) dir_eq.symm (fun x => ε[p].onDir x ())
    conv at M =>
      lhs
      rewrite [K]
    exact M

lemma across_cods {i : p.pos}
                  {f : p.dir i}
                  : cod f = cod_2 (dir_eq (p := p) ▸ f) := by
                  rfl

lemma cod_eq {α : Sort _}
             {i i' : α}
             {β : α → Sort _}
             (f : β i)
             (h : i = i')
             (x : β i = β i')
             (abstract_cod : {i : α} → (f : β i) → α)
              : abstract_cod (i := i') (f := x ▸ f) = abstract_cod (i := i) (f := f) := by
              cases h
              rfl

lemma dir_lemma {p q r : Poly}
                {i j : (p ◁ q ◁ r).pos}
                {i' : p.pos}
                (x : i = j)
                (f : p.dir i.fst)
                (g : q.dir (i.snd f).fst)
                (h : r.dir ((i.snd f).snd g))
                (y : i.fst = i')
                (y' : j.fst = i')
                :
                let d : (p ◁ q ◁ r).dir i := ⟨ f , ⟨ g , h ⟩⟩
                let f'' : p.dir i' := y ▸ f
                (x ▸ d).fst = y' ▸ f'' := by
                cases x
                cases y
                rfl

@[simp] lemma fst_cast  {β β' : α → Sort _} (h : β = β') (x : Σ a, β a) :
  (h ▸ x).fst = x.fst := by cases h; rfl


@[simp] lemma Sigma.snd_cast {α : Sort _} {β β' : α → Sort _}
    (h : β = β') (x : Σ a, β a) :
  HEq (h ▸ x).snd x.snd := by
  cases h; rfl

lemma abstracted {α : Sort _} -- C.carrier.os
                 {β : α → Sort _} -- C.carrier.dir
                 {i i' i'' : α} -- i, posAtDir i, posAtDir (posAtDir i)
                 {cod : {i : α} → (β i) → α} -- cod
                 (fn : (i : α) → (i' : α) → (f : β i) → (fPos : β i') → (g : β (cod f)) → (β i)) -- λ i {f} fpos g ↦ C.comult.onDir i ⟨ fpos , g ⟩
                 (h : i = i') -- bookeeping i
                 (h' : i' = i'') -- bookeeping i
                 (x : β i = β i') -- dir_eq
                 (x' : β i' = β i'') -- dir_eq
                 (f : β i) -- f
                 (g : β (cod f)) -- g
                 (more_info : cod f = cod (i := i') (x ▸ f)) -- what_
           :
           x ▸ fn i i' (f := f) (x ▸ f) g = fn i' i'' (f := (x ▸ f)) (x' ▸ x ▸ f) (more_info ▸ g)
           := by
           cases h
           cases h'
           cases x
           rfl


-- LMAOOOOO
lemma abstracted2 {α : Sort _} -- C.carrier.os
                  {β : α → Sort _} -- C.carrier.dir
                  {i : α} -- i
                  {posAt : α → α} -- posAtDir
                  {cod : {i : α} → (β i) → α} -- cod
                  (h : i = posAt i) -- bookeeping i
                  (x : {i : α} → β i = β (posAt i)) -- dir_eq
                  (f : β i) -- f
                  (g : β (cod f)) -- g
                  (fn : (i : α) → (f : β i) → (g : β (cod f)) → (β i)) -- λ i {f} fpos g ↦ C.comult.onDir i ⟨ fpos , g ⟩
                  (more_info : (cod f) = (cod (i := posAt i) (x ▸ f))) -- what_g
           :
           x ▸ fn i (f := f) g = fn (posAt i) (f := (x ▸ f)) (more_info ▸ g)
           := by
           exact abstracted (α := α)
                                (β := β)
                                (i := i)
                                (i' := posAt i)
                                (i'' := posAt (posAt i))
                                (cod := cod)
                                (fn := λ i _ f _ g ↦ fn i f g)
                                (h := h)
                                (h' := h ▸ h)
                                (x := x)
                                (x' := x)
                                (f := f)
                                (g := g)
                                (more_info := more_info)

lemma casted_sigma_fst_eq_s -- p.pos
                            (p1 p2 : Sigma fun x => (p.dir x → (x : p.pos) × (p.dir x → p.pos))) -- ⟨posAtDir i, λ pd ↦ Δ[p].onPos (cod_2 pd)⟩ and ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (Δ[p].onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩
                            (pos_eq : p1 = p2)
                            (f : p.dir p1.fst) -- So the type of f is constructed *out of* a position
                            {g : (p◁p).dir (p1.snd f)}
                            (x : p.dir p1.fst = p.dir p2.fst) :
                            let elem_of_the_type : (p◁p◁p).dir p1 := ⟨ f , g ⟩
                            (pos_eq ▸ elem_of_the_type).fst = x ▸ f
                            := by
                            cases pos_eq
                            rfl

lemma casted_sigma_snd_eq_s -- p.pos
                            (p1 p2 : Sigma fun x => (p.dir x → (x : p.pos) × (p.dir x → p.pos))) -- ⟨posAtDir i, λ pd ↦ Δ[p].onPos (cod_2 pd)⟩ and ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (Δ[p].onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩
                            (pos_eq : p1 = p2)
                            (f : p.dir p1.fst) -- So the type of f is constructed *out of* a position
                            {g : p.dir (p1.snd f).fst}
                            {h : p.dir ((p1.snd f).snd g)}
                            :
                            let elem_of_the_type : (p◁p◁p).dir p1 := ⟨ f , ⟨ g , h ⟩  ⟩
                            HEq (pos_eq ▸ elem_of_the_type).snd.fst g
                            := by
                            cases pos_eq
                            rfl

lemma casted_sigma_3rd_eq_s -- p.pos
                            (p1 p2 : Sigma fun x => (p.dir x → (x : p.pos) × (p.dir x → p.pos))) -- ⟨posAtDir i, λ pd ↦ Δ[p].onPos (cod_2 pd)⟩ and ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (Δ[p].onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩
                            (pos_eq : p1 = p2)
                            (f : p.dir p1.fst) -- So the type of f is constructed *out of* a position
                            {g : p.dir (p1.snd f).fst}
                            {h : p.dir ((p1.snd f).snd g)}
                            {capstmt : α}
                            (more : HEq capstmt h )
                            :
                            let elem_of_the_type : (p◁p◁p).dir p1 := ⟨ f , ⟨ g , h ⟩  ⟩
                            HEq (pos_eq ▸ elem_of_the_type).snd.snd capstmt
                            := by
                            cases pos_eq
                            cases more
                            rfl

lemma cast_heq {α : Type}
               {β : α → Type}
               {a b : α}
               (h : a = b)
               (A : β a)
               : HEq (h ▸ A) A   := by
  cases h
  rfl



def coassoc_dir_statement {i : p.pos}
                          (f : p.dir i)
                          (g : p.dir (cod f))
                          (h : p.dir (cod g))
                          :
                          comp (comp f g) (coassoc_pos_statement f g ▸ h)
                          =
                          comp f (comp g h) :=
  by

    have sacred_pos_left : (p◁p◁p).pos
      := ⟨posAtDir i, λ pd ↦ Δ[p].onPos (cod_2 pd)⟩
    have sacred_pos_right : (p◁p◁p).pos
      := ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (Δ[p].onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩
    let reduced_pos_type := Sigma (fun x => (p.dir x → (x : p.pos) × (p.dir x → p.pos)))
    have pos_eq : (Δ ≫ p ◁ Δ).onPos i = (Δ ≫ Δ ▷ p ≫ (α_ p p p).hom).onPos i := on_pos_eq (i := i) (comul_assoc p)
    reduce at pos_eq
    have coassoc_onDir := on_dir_eq (p := p) (f := (Δ ≫ p ◁ Δ)) (g := Δ ≫ Δ ▷ p) (i := i) (comul_assoc p) pos_eq

    let f' : p.dir (posAtDir i) := dir_eq (p := p) ▸ f
    let g' : p.dir (posAtDir (cod f)) := dir_eq (p := p) ▸ g

    let composed :
      (p◁p◁p).dir ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (Δ[p].onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩
      := pos_eq ▸ (⟨f', ⟨g', h⟩⟩ )
    let composed_snd := composed.snd
    let composed_fst := composed.fst

    let wm_eq_wm' : pos_eq.symm ▸ composed = ⟨f', ⟨g', h⟩⟩ :=
      cast_id'''' (α := (p◁p◁p).pos) (β := (p◁p◁p).dir) pos_eq


    let some_kind_of_f : p.dir (posAtDir (posAtDir i)) := composed.fst
    let some_kind_of_g : p.dir (cod_2 some_kind_of_f) := composed.snd.fst
    let some_kind_of_h : p.dir (cod_2 (comp_2 some_kind_of_f some_kind_of_g)) := composed.snd.snd

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


    let capstmt : p.dir (cod (comp f g)) := (coassoc_pos_statement f g).symm ▸ h

    have ultimate :
      (⟨Δ[p].onDir (posAtDir i) ⟨some_kind_of_f, some_kind_of_g⟩, some_kind_of_h⟩ : (p ◁ p).dir (Δ[p].onPos i))
      =
      (⟨dir_eq (p := p) ▸ Δ[p].onDir i ⟨dir_eq (p := p) ▸ f, g⟩, capstmt⟩ : (p ◁ p).dir (Δ[p].onPos i))
      := by

      have cod_eq : cod (i := i) f = cod (i := posAtDir i) (dir_eq (i := i) ▸ f)
        := (cod_eq (i := i) (i' := posAtDir i) (h := (bookkeeping i).symm) (x := dir_eq) f cod).symm

      have H0 : dir_eq (p := p) ▸ Δ[p].onDir i ⟨dir_eq (p := p) ▸ f, g⟩ = Δ[p].onDir (posAtDir i) ⟨ dir_eq (p := p) ▸ dir_eq (p := p) ▸ f , ((cod_eq ▸ g) :  p.dir (cod (i := posAtDir i) (dir_eq (p := p) ▸ f)))  ⟩ :=
        abstracted2 (α := p.pos)
                    (β := p.dir)
                    (i := i)
                    (posAt := λ i ↦ posAtDir i)
                    (cod := λ {i} b ↦ cod (i := i) b)
                    (fn := λ i f gw ↦ Δ[p].onDir i ⟨ (dir_eq (p := p) ▸ f) , gw ⟩)
                    (h := (bookkeeping i).symm)
                    (x := dir_eq)
                    (f := f)
                    (g := g)
                    cod_eq


      have cap_eq : HEq capstmt h := by
        let w := cast_heq ((coassoc_pos_statement f g).symm) h
        exact w

      have H : Δ[p].onDir (posAtDir i) ⟨some_kind_of_f, some_kind_of_g⟩ = dir_eq (p := p) ▸ Δ[p].onDir i ⟨dir_eq (p := p) ▸ f, g⟩ := by
        rw [H0]
        congr!
        . exact casted_sigma_fst_eq_s (p1 := ⟨posAtDir i, λ pd ↦ Δ[p].onPos (cod_2 pd)⟩)
                                      (p2 := ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (Δ[p].onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩)
                                      (pos_eq := pos_eq)
                                      (f := dir_eq (p := p) ▸ f)
                                      (x := dir_eq)
        . unfold some_kind_of_g composed g'
          have x := casted_sigma_snd_eq_s (p1 := ⟨posAtDir i, λ pd ↦ Δ[p].onPos (cod_2 pd)⟩)
                                          (p2 := ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (Δ[p].onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩)
                                          (pos_eq := pos_eq)
                                          (f := dir_eq (p := p) ▸ f)
                                          (g := dir_eq (p := p) ▸ g)
                                          (h := h)
          simp_all only [heq_eqRec_iff_heq, f']
      congr!
      . unfold some_kind_of_f some_kind_of_g composed
        simp_all only [some_kind_of_f, composed, f', g', some_kind_of_g, some_kind_of_h]
        have x := casted_sigma_3rd_eq_s (p1 := ⟨posAtDir i, λ pd ↦ Δ[p].onPos (cod_2 pd)⟩)
                                          (p2 := ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (Δ[p].onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩)
                                          (pos_eq := pos_eq)
                                          (f := dir_eq (p := p) ▸ f)
                                          (g := dir_eq (p := p) ▸ g)
                                          (h := h)
                                          (capstmt := capstmt)
                                          (more := cap_eq)
        simp_all only [some_kind_of_f, f', some_kind_of_g, g', composed, some_kind_of_h, x]

    have intermediate :
      comp_2
        (comp_2
          some_kind_of_f
          some_kind_of_g)
        some_kind_of_h
      =
      comp (comp f g) (coassoc_pos_statement f g ▸ h) := by
      unfold comp_2
      simp [ultimate]
      congr!
    rw [at_fgh, ← intermediate]


def Hom_cat (i j : p.pos) : Type :=
  { f : p.dir i // cod f = j }

def id_cat (i : p.pos) : { f : p.dir i // cod f = i } :=
  ⟨ id i, cod_id ⟩

def comp_cat {i j k : p.pos}
               (fg : { codlessf : p.dir i // cod codlessf = j })
               (gh : { codlessg : p.dir j // cod codlessg = k }) :
               { f : p.dir i // cod f = k } :=
  let ⟨f, codf⟩ := fg
  let ⟨g, codg⟩ := gh
  ⟨ comp f (codf ▸ g) , by
    subst codf codg
    rw [coassoc_pos_statement f g]
  ⟩

def dependentCongrArg {α out : Type}
                      {β : α → Type}
                      {x y : α}
                      (a : β x)

                      (h : y = x)
                      (g : {x : α} → β x → out)
                      : g (x := x) a = g (x := y) (h ▸ a) := by
                      cases h
                      rfl

def assoc_cat {i j k l : p.pos}
                (f : { codlessf : p.dir i // cod codlessf = j })
                (g : { codlessg : p.dir j // cod codlessg = k })
                (h : { codlessh : p.dir k // cod codlessh = l }) :
                comp_cat (comp_cat f g) h = comp_cat f (comp_cat g h) :=
    let ⟨f, codf⟩ := f
    let ⟨g, codg⟩ := g
    let ⟨h, codh⟩ := h
    by
    have codg_eq_codg' : cod g = cod (codf ▸ g) := by
      exact dependentCongrArg g codf cod
    have dir_statement := coassoc_dir_statement (i := i) f (codf ▸ g) (codg_eq_codg' ▸ codg ▸ h)
    subst codh codg codf
    simp_all only [comp_cat]

def counit_onPos_unit {i : p.pos} : ε[p].onPos i = () :=
  by
  rfl

-- C.counit.onDir (C.comult.onPos i).fst () = dir_eq ▸ C.counit.onDir i ()
lemma abstracted_lol {α : Sort _}
                     {β : α → Sort _}
                     {i i' : α}
                     (h : i' = i )
                     (x : β i = β i')
                     (f : (i : α) → β i)
                     :
                     f i' = x ▸ f i := by
                     cases h
                     rfl



def id_comp_cat_dir_statement {i : p.pos}
                              (f : p.dir i)
                              :
                              comp (id i) (cod_id (p := p) ▸ f) = f :=
  by
  unfold comp cod
  have H : (Δ[p] ≫ (ε[p] ▷ p) : p ⟶ (y ◁ p))
            =
           ((λ_ p).inv : p ⟶ (y ◁ p)) := by
           rw [counit_comul]

  have pos_eq
    : (cod_2 (ε[p].onDir (posAtDir i) ()))
      =
      (i : p.pos)
    := on_pos_eq_id (i := i) (x := H)


  have id_comp_onDir := on_dir_eq_id (i := i)
                                     (counit_comul p)
                                     pos_eq

  have well :
   Δ[p].onDir i ⟨id (posAtDir i), (pos_eq.symm ▸ f : p.dir (cod_2 (ε[p].onDir (posAtDir i) ())))⟩
   =
   (pos_eq ▸ pos_eq.symm ▸ f : p.dir i)
  := congrFun id_comp_onDir ⟨ () , (pos_eq.symm ▸ f : p.dir (cod_2 (ε[p].onDir (posAtDir i) ())))  ⟩

  have rhs_rw : (pos_eq ▸ pos_eq.symm ▸ f : p.dir i) = f := cast_id'''''' pos_eq.symm

  have lhs_rw_1 : id (posAtDir i) = dir_eq (p := p) ▸ id i := abstracted_lol (bookkeeping i)
                                                                    dir_eq
                                                                    (λ i ↦ ε[p].onDir i ())


  rw [rhs_rw] at well

  rw [← well]
  congr!
  . exact lhs_rw_1.symm


def comp_id_cat_dir_statement {i : p.pos}
                          (f : p.dir i)
                          :
                          comp f (id (cod f)) = f :=
  by
  unfold comp cod
  have H : (Δ[p] ≫ (p ◁ ε[p]))
            =
           ((ρ_ p).inv) := by
           rw [comul_counit]



  simp_all [composemap, subst.whiskerRight]

  have id_comp_onDir := on_dir_eq_id_ (i := i)
                                      (comul_counit p)
                                      (bookkeeping i)

  reduce at id_comp_onDir

  have well
    : comp f (id (cod_2 (dir_eq (p := p) ▸ f)))
      =
      (bookkeeping i ▸ dir_eq (p := p) ▸ f : p.dir i)
   := congrFun id_comp_onDir ⟨ dir_eq (p := p) ▸ f , () ⟩

  have x : (bookkeeping i ▸ dir_eq (p := p) ▸ f : p.dir i) = f := cast_id''''' (h := (bookkeeping i).symm) (x := dir_eq)

  rw [x] at well
  conv =>
    rhs
    rw [← well]
  congr!


def id_comp_cat :
                {i j : p.pos} →
                (f : { codlessf : p.dir i // cod codlessf = j }) →
                comp_cat (id_cat i) f = f :=
    λ {i j} ⟨f, codf⟩ ↦ by
      have stmt := id_comp_cat_dir_statement (i := i) f
      subst codf
      ext : 1
      simp_all only
      exact stmt


def comp_id_cat :
                {i j : p.pos} →
                (f : { codlessf : p.dir i // cod codlessf = j }) →
                comp_cat f (id_cat j) = f :=
    λ {i j} ⟨f, codf⟩ ↦ by
      have stmt := comp_id_cat_dir_statement (i := i) f
      subst codf
      ext : 1
      simp_all only
      exact stmt

/-- The theorem: every comonoid in Poly induces a (small) category. -/
instance comonoid_to_category : Category p.pos where
  Hom := Hom_cat
  id := id_cat
  comp := comp_cat
  id_comp := id_comp_cat
  comp_id := comp_id_cat
  assoc   := assoc_cat


end CategoryTheory
