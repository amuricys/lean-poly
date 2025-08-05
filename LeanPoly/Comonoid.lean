import Init.Prelude
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Closed.Monoidal
import «LeanPoly».Poly
import «LeanPoly».Lemmas
import LeanCopilot

namespace CategoryTheory
set_option pp.proofs true
set_option pp.showLetValues true

/-- A comonoid in Poly (with respect to the substitution product ◁ and unit y). -/
structure Comonoid where
  carrier     : Poly
  counit      : carrier ⟶ y
  comult      : carrier ⟶ carrier ◁ carrier
  leftCounit  : composemap comult (subst.whiskerRight counit)
                =
                subst.leftUnitor.inv carrier
  rightCounit : composemap comult (subst.whiskerLeft counit)
                = subst.rightUnitor.inv carrier
  coassoc     : (composemap comult (subst.whiskerLeft comult)) -- : c ⟶ c ◁ (c ◁ c)
                =
                composemap (composemap comult (subst.whiskerRight comult)) -- : c ⟶ (c ◁ c) ◁ c
                           subst.associator.hom -- therefore the associator is needed


def posAtDir {C : Comonoid} (i : C.carrier.pos) : C.carrier.pos :=
  (C.comult.onPos i).fst

lemma bookkeeping {C : Comonoid} (i : C.carrier.pos) : posAtDir i = i :=
  by
  have H : (composemap C.comult (subst.whiskerLeft C.counit)).onPos i
           =
           (subst.rightUnitor.inv C.carrier).onPos i := by
           rewrite [C.rightCounit]
           simp only
  apply fst_eq H

lemma dir_eq {C : Comonoid} {i : C.carrier.pos} : C.carrier.dir i = C.carrier.dir (posAtDir i) := by
  rewrite [bookkeeping i]
  rfl

def cod {C : Comonoid} {i : C.carrier.pos} (f : C.carrier.dir i) : C.carrier.pos :=
    (C.comult.onPos i).snd (dir_eq ▸ f)

def comp {C : Comonoid}
         {i : C.carrier.pos}
         (f : C.carrier.dir i)
         (g : C.carrier.dir (cod f)) :
         C.carrier.dir i :=
         C.comult.onDir i ⟨ dir_eq ▸ f , g ⟩

lemma dir_cast_id {C : Comonoid} {i : C.carrier.pos} {x : C.carrier.dir (C.comult.onPos i).fst} :
                    (C.comult.onPos i).snd
                          ((dir_eq : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).fst) ▸
                            (dir_eq.symm : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir i) ▸ x)
                    =
                    (C.comult.onPos i).snd x
                    := by
                    rewrite [← cast_id (a := i) (c := x) (β := C.carrier.dir) (bookkeeping i).symm dir_eq]
                    rfl


lemma need_this {C : Comonoid} {i : C.carrier.pos} {x : C.carrier.dir (C.comult.onPos i).fst} :
                (C.comult.onPos (C.comult.onPos i).fst).snd
                  ((dir_eq :
                      C.carrier.dir (C.comult.onPos i).fst =
                        C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst) ▸
                    x) =
                (C.comult.onPos i).snd x
                := fst_do_i_actual (i := i)
                                   (i' := (C.comult.onPos i).fst)
                                   (β := λ x ↦ C.carrier.dir (C.comult.onPos x).fst)
                                   (x_general := fun x y => (C.comult.onPos x).snd y)
                                   (bookkeeping i).symm
                                   x
                                   dir_eq

lemma dir_different_casts {C : Comonoid} {i : C.carrier.pos} {x : C.carrier.dir (C.comult.onPos i).fst} :
                    (C.comult.onPos i).snd
                      ((dir_eq : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).fst) ▸
                        (dir_eq.symm : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir i) ▸ x)
                    =
                    (C.comult.onPos (C.comult.onPos i).fst).snd
                      ((dir_eq : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir (C.comult.onPos  (C.comult.onPos i).fst).fst) ▸ x)
                    := by
                    rewrite [← cast_id (a := i) (c := x) (β := C.carrier.dir) (bookkeeping i).symm dir_eq]
                    rewrite [need_this]
                    simp

lemma dir_different_casts_eq {C : Comonoid} {i : C.carrier.pos} {x : C.carrier.dir (C.comult.onPos i).fst} :
                    C.carrier.dir ((C.comult.onPos i).snd
                          ((dir_eq : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).fst) ▸
                            (dir_eq.symm : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir i) ▸ x))
                    =
                    C.carrier.dir ((C.comult.onPos (C.comult.onPos i).fst).snd
                      ((dir_eq : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst) ▸
                      x))
                    := by
                    rewrite [← cast_id (a := i) (c := x) (β := C.carrier.dir) (bookkeeping i).symm dir_eq]
                    rewrite [need_this]
                    simp


lemma dir_composed_eq {C : Comonoid} {i : C.carrier.pos} :
                      (C.carrier◁C.carrier).dir (C.comult.onPos i) =
                      (C.carrier◁C.carrier).dir (C.comult.onPos (posAtDir i))
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

def on_dir_eq_no_cast {f : polymap p (p ◁ p ◁ p)} {g : polymap p ((p ◁ p) ◁ p)}
  {i : p.pos}
  (x : f = composemap g subst.associator.hom)
  :
  (fun (df : (p ◁ p ◁ p).dir (f.onPos i)) =>
  (f.onDir i df : p.dir i))
  =
  (fun (df : (p ◁ p ◁ p).dir (f.onPos i)) =>
  let dg : (p ◁ p ◁ p).dir (subst.associator.hom.onPos $ g.onPos i) := by
    rewrite [x] at df
    exact df
  (g.onDir i (subst.associator.hom.onDir _ dg) : p.dir i))
  := by
  subst x
  simp_all only [eq_mp_eq_cast, cast_eq]
  rfl


lemma coassoc_pos_statement {C : Comonoid}
                            {i : C.carrier.pos}
                            (f : C.carrier.dir i)
                            (g : C.carrier.dir (cod f)) :
                            cod (comp f g) = cod g := by
    have coassoc_onPos := congrArg (λ x => x.onPos) C.coassoc
    simp [composemap, subst.whiskerRight, subst.whiskerLeft, applyMap, subst.associator.hom, Function.comp, subst] at coassoc_onPos

    let at_i := congrFun coassoc_onPos i

    have wait : (fun x => C.comult.onPos ((C.comult.onPos i).snd x) : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos)
                =
                (bookkeeping (C.comult.onPos i).fst) ▸
                 (fun pd =>
                   { fst := (C.comult.onPos (C.comult.onPos i).fst).snd pd,
                     snd := fun qd => (C.comult.onPos i).snd (C.comult.onDir (C.comult.onPos i).fst ⟨ pd , qd ⟩)
                     } : C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst → (C.carrier◁C.carrier).pos )
                := snd_heq (h := at_i)

    have hard_rhs : Eq.rec (motive := fun x _ => C.carrier.dir x → (C.carrier ◁ C.carrier).pos)
                           (fun pd : C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst =>
                             { fst := (C.comult.onPos (C.comult.onPos i).fst).snd pd,
                               snd := fun qd =>
                                 (C.comult.onPos i).snd
                                   (C.comult.onDir (C.comult.onPos i).fst { fst := pd, snd := qd }) } )
                           (bookkeeping ((C.comult.onPos i).fst) : (C.comult.onPos (C.comult.onPos i).fst).fst = (C.comult.onPos i).fst)
                    =
                    (fun pd =>
                      { fst := (C.comult.onPos (C.comult.onPos i).fst).snd (dir_eq ▸ pd),
                        snd := fun qd => (C.comult.onPos i).snd (C.comult.onDir (C.comult.onPos i).fst ⟨ dir_eq ▸ pd , qd ⟩)
                        } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
                    := push_cast_in_lambda (χ := (C.carrier ◁ C.carrier).pos)
                                           (bookkeeping ((C.comult.onPos i).fst))
                                           (fun (pd : C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst) =>
                                             { fst := (C.comult.onPos (C.comult.onPos i).fst).snd pd,
                                               snd := fun qd =>
                                                 (C.comult.onPos i).snd (C.comult.onDir (C.comult.onPos i).fst { fst := pd, snd := qd }) })

    have now_we'd_be_talking :
                (fun x => C.comult.onPos ((C.comult.onPos i).snd x) : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos)
                =
                (fun pd =>
                      { fst := (C.comult.onPos (C.comult.onPos i).fst).snd (dir_eq ▸ pd),
                        snd := fun qd => (C.comult.onPos i).snd (C.comult.onDir (C.comult.onPos i).fst ⟨ dir_eq ▸ pd , qd ⟩)
                        } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
                := by
                conv =>
                  rhs
                  rw [← hard_rhs]
                exact wait

    have obvious : (C.carrier.dir i → (C.carrier◁C.carrier).pos)
                   =
                   (C.carrier.dir (posAtDir i) → (C.carrier◁C.carrier).pos)
                   := by
                   rewrite [bookkeeping i]
                   rfl

    have now_lhs : (fun x => C.comult.onPos ((C.comult.onPos i).snd x) : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos)
                   =
                   obvious ▸
                   (fun x => C.comult.onPos ((C.comult.onPos i).snd (dir_eq ▸ x)) : C.carrier.dir i → (C.carrier◁C.carrier).pos)
                   := lhs_lemma (arg1 := C.carrier.dir (posAtDir i))
                                (arg2 := C.carrier.dir i)
                                (out := (C.carrier◁C.carrier).pos)
                                obvious.symm
                                (by rewrite [← dir_eq]; simp)

    let dir_eq_specialized {C : Comonoid} {i : C.carrier.pos}: C.carrier.dir (posAtDir i) = C.carrier.dir (posAtDir (posAtDir i))  := by
      simp only [bookkeeping i]

    have fst_do_i_have {x : C.carrier.dir (C.comult.onPos i).fst} :
                        (C.comult.onPos (C.comult.onPos i).fst).snd
                          ((dir_eq :
                              C.carrier.dir (C.comult.onPos i).fst =
                                C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst) ▸
                            x) =
                        (C.comult.onPos i).snd
                          ((dir_eq : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).fst) ▸
                            (dir_eq.symm : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir i) ▸ x)
                        := by
                            conv =>
                              rhs
                              rewrite [← cast_id (a := i) (c := x) (β := C.carrier.dir) (bookkeeping i).symm dir_eq]
                            exact need_this

    let sigmas_eq {α : Type}
                  {χ₁ : α → Type} -- λ i → (C.carrier.dir (C.comult.onPos i).fst)
                  {χ₂ : α → Type} -- λ i → (C.carrier.dir i)
                  {β₁ : {a : α} → (χ₁ a) → Type} -- (λ {i} d ↦ C.carrier.dir ((C.comult.onPos i).snd d))
                  {i i' : α} -- i, (C.comult.onPos i).fst
                  {x : χ₁ i} -- C.carrier.dir (C.comult.onPos i).fst
                  (h : χ₁ i = χ₁ i') -- dir_eq : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst
                  (h' : χ₂ i = χ₁ i) -- dir_eq : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).fst
                  (qd : β₁ (a := i') (h ▸ x)) -- C.carrier.dir ((C.comult.onPos (C.comult.onPos i).fst).snd (dir_eq ▸ x))
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
    let very_small {x : C.carrier.dir (C.comult.onPos i).fst}
                   {qd : C.carrier.dir ((C.comult.onPos (C.comult.onPos i).fst).snd (dir_eq ▸ x)) }
                   :
                   (⟨ (dir_eq : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).fst) ▸
                        (dir_eq.symm : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir i) ▸ x, dir_different_casts_eq ▸ qd ⟩ : @Sigma (C.carrier.dir (C.comult.onPos i).fst)
                                                                                       (fun d => C.carrier.dir ((C.comult.onPos i).snd d)))
                   =
                   (dir_composed_eq ▸
                   (⟨ dir_eq ▸ x , qd ⟩ : @Sigma (C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst)
                                                 (fun d => C.carrier.dir (Sigma.snd (C.comult.onPos (C.comult.onPos i).fst) d)))
                    : (C.carrier◁C.carrier).dir (C.comult.onPos i))
                   := sigmas_eq (β₁ := (λ {i} d ↦ C.carrier.dir ((C.comult.onPos i).snd d)))
                                dir_eq
                                dir_eq
                                qd
                                dir_different_casts_eq
                                dir_composed_eq
                                (bookkeeping i)

    let dirs_equal_lemma {α : Type}
                         {β : α → Type} -- λ i ↦ (C.carrier◁C.carrier).dir (C.comult.onPos i)
                         {out : α → Type} -- C.carrier.dir
                         {i i' : α}  -- i, (C.comult.onPos i).fst
                         {dir_i : β i} -- ⟨ dir_eq ▸ dir_eq.symm ▸ x, dir_different_casts_eq ▸ qd ⟩
                         {dir_i' : β i'} -- ⟨ dir_eq ▸ x, qd ⟩
                         (f : (x : α) → β x → out x) -- C.comult.onDir
                         (h : out i = out i') -- dir_eq
                         (k : i = i') -- (bookkeeping i).symm
                         (t : β i = β i')
                         (l : dir_i = t ▸ dir_i')
                         : h ▸ f i dir_i
                         = f i' dir_i'
                         := by
                         cases k
                         simp only [l]

    let dirs_equal {x : C.carrier.dir (C.comult.onPos i).fst}
                   {qd : C.carrier.dir ((C.comult.onPos (C.comult.onPos i).fst).snd (dir_eq ▸ x)) }
                  :
                   let tgt_dir_1 : (C.carrier◁C.carrier).dir (C.comult.onPos i) := ⟨ dir_eq ▸ dir_eq.symm ▸ x, dir_different_casts_eq ▸ qd ⟩
                   let tgt_dir_2 : (C.carrier◁C.carrier).dir (C.comult.onPos (C.comult.onPos i).fst) := ⟨ dir_eq ▸ x, qd ⟩

                   (dir_eq ▸
                   (C.comult.onDir i tgt_dir_1 : C.carrier.dir i))
                   =
                   ((C.comult.onDir (C.comult.onPos i).fst tgt_dir_2) : C.carrier.dir (C.comult.onPos i).fst)
                  := dirs_equal_lemma (α := C.carrier.pos)
                                      (β := λ i ↦ (C.carrier◁C.carrier).dir (C.comult.onPos i))
                                      (out := C.carrier.dir)
                                      C.comult.onDir
                                      dir_eq
                                      (bookkeeping i).symm
                                      dir_composed_eq
                                      very_small

    let pushed_cast {x : C.carrier.dir (C.comult.onPos i).fst}
              : (fst_do_i_have ▸
                  (fun qd =>
                    (C.comult.onPos i).snd
                      (dir_eq ▸ C.comult.onDir i ⟨ dir_eq ▸ dir_eq.symm ▸ x, qd ⟩) : C.carrier.dir ((C.comult.onPos i).snd ((dir_eq : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).fst) ▸ (dir_eq.symm: C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir i) ▸ x)) → C.carrier.pos ))
                =
                (fun qd =>
                  (C.comult.onPos i).snd
                    (dir_eq ▸ C.comult.onDir i ⟨ dir_eq ▸ dir_eq.symm ▸ x, dir_different_casts_eq ▸ qd ⟩) : C.carrier.dir ((C.comult.onPos (C.comult.onPos i).fst).snd ((_ : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst) ▸ x)) → C.carrier.pos)
                :=
                push_cast_in_lambda dir_different_casts
                                    (fun qd =>
                                     (C.comult.onPos i).snd
                                       (dir_eq ▸ C.comult.onDir i ⟨ dir_eq ▸ dir_eq.symm ▸ x, qd ⟩))

    let same_type {x : C.carrier.dir (C.comult.onPos i).fst}
              : (fun qd =>
                  (C.comult.onPos i).snd
                    (C.comult.onDir (C.comult.onPos i).fst ⟨ dir_eq ▸ x, qd ⟩))
                  =
                (fun qd =>
                  (C.comult.onPos i).snd
                    (dir_eq ▸ C.comult.onDir i ⟨ dir_eq ▸ dir_eq.symm ▸ x, dir_different_casts_eq ▸ qd ⟩))
              := by
              funext qd
              rewrite [← dirs_equal (x := x) (qd := qd)]
              rfl

    let innit {x : C.carrier.dir (C.comult.onPos i).fst}
              : (fun qd =>
                  (C.comult.onPos i).snd
                    (C.comult.onDir (C.comult.onPos i).fst ⟨ dir_eq ▸ x, qd ⟩) : C.carrier.dir ((C.comult.onPos (C.comult.onPos i).fst).snd ((_ : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst) ▸ x)) → C.carrier.pos)
                  =
                  (fst_do_i_have ▸
                  (fun qd =>
                    (C.comult.onPos i).snd
                      (dir_eq ▸ C.comult.onDir i ⟨ dir_eq ▸ dir_eq.symm ▸ x, qd ⟩) : C.carrier.dir ((C.comult.onPos i).snd ((dir_eq : C.carrier.dir i = C.carrier.dir (C.comult.onPos i).fst) ▸ (dir_eq.symm: C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir i) ▸ x)) → C.carrier.pos ))
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
                      { fst := (C.comult.onPos (C.comult.onPos i).fst).snd (dir_eq_specialized ▸ pd),
                        snd := fun qd => (C.comult.onPos i).snd (C.comult.onDir (C.comult.onPos i).fst ⟨ dir_eq_specialized ▸ pd , qd ⟩ )
                        } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
                    =
                    -- new lhs
                    (fun pd =>
                      { fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
                        snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ pd , qd ⟩))
                        } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
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
                      { fst := (C.comult.onPos i).snd (dir_eq ▸ dir_eq ▸ pd),
                        snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ dir_eq ▸ pd , qd ⟩))
                        } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
                      =
                      (fun pd =>
                        { fst := (C.comult.onPos i).snd (dir_eq.symm ▸ dir_eq ▸ pd),
                          snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq.symm ▸ dir_eq ▸ pd , qd ⟩))
                          } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
                      := cast_on_arg_incredible_stupidity
                                    (out := (C.carrier◁C.carrier).pos )
                                    (f := fun pd =>
                                      { fst := (C.comult.onPos i).snd pd,
                                        snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ pd , qd ⟩))
                                        })
                                    dir_eq
                                    dir_eq

    have may_i : Eq.rec
                     (fun pd =>
                       {
                         fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
                         snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ C.comult.onDir i { fst := dir_eq ▸ pd, snd := qd }) })
                     obvious
                 =
                 (fun pd =>
                   { fst := (C.comult.onPos i).snd (dir_eq ▸ dir_eq ▸ pd),
                     snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ dir_eq ▸ pd , qd ⟩))
                     } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
                 := cast_on_arg obvious dir_eq.symm

    have pre_now_the_other : Eq.rec
                                (fun pd =>
                                  {
                                    fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
                                    snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ C.comult.onDir i { fst := dir_eq ▸ pd, snd := qd }) })
                                obvious
                            =
                            (fun pd =>
                              { fst := (C.comult.onPos i).snd (dir_eq.symm ▸ dir_eq ▸ pd),
                                snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq.symm ▸ dir_eq ▸ pd , qd ⟩))
                                } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
                            := by
                            funext pd
                            conv =>
                              lhs
                              rewrite [may_i]
                              rewrite [yes_you_may]

    have pre_even : (fun pd =>
                    { fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
                      snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ pd , qd ⟩))
                      } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
                    =
                    (fun pd =>
                      { fst := (C.comult.onPos i).snd (dir_eq.symm ▸ dir_eq ▸ pd),
                        snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq.symm ▸ dir_eq ▸ pd , qd ⟩))
                        } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
                    := cast_on_arg_incredible_stupidity
                                    (out := (C.carrier◁C.carrier).pos )
                                    (f := fun pd =>
                                      { fst := (C.comult.onPos i).snd pd,
                                        snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ pd , qd ⟩))
                                        })
                                    dir_eq
                                    dir_eq

    have now_the_other_one : (fun pd =>
                              { fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
                                snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ pd , qd ⟩))
                                } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
                              =
                              obvious ▸
                              (fun pd =>
                               { fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
                                 snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ pd , qd ⟩))
                                 } : C.carrier.dir i → (C.carrier◁C.carrier).pos )
                              := by
                              rewrite [pre_now_the_other]
                              exact pre_even


    have now_rhs : (fun pd =>
                      { fst := (C.comult.onPos (C.comult.onPos i).fst).snd (dir_eq_specialized ▸ pd),
                        snd := fun qd => (C.comult.onPos i).snd (C.comult.onDir (C.comult.onPos i).fst ⟨ dir_eq_specialized ▸ pd , qd ⟩)
                        } : C.carrier.dir (C.comult.onPos i).fst → (C.carrier◁C.carrier).pos )
                   =
                   obvious ▸
                   (fun pd =>
                      { fst := (C.comult.onPos i).snd (dir_eq ▸ pd),
                        snd := fun qd => (C.comult.onPos i).snd (dir_eq ▸ (C.comult.onDir i ⟨ dir_eq ▸ pd , qd ⟩))
                        } : C.carrier.dir i → (C.carrier◁C.carrier).pos )
                   := by
                   conv =>
                     lhs
                     rewrite [do_i_have_this]
                   rewrite [now_the_other_one]
                   rfl

    have pre_now_we'd_talk_even_more :
                obvious ▸
                (fun x => C.comult.onPos (cod x) : C.carrier.dir i → (C.carrier◁C.carrier).pos)
                =
                obvious ▸
                (fun pd =>
                      { fst := cod pd,
                        snd := fun qd => cod (comp pd qd)
                        } : C.carrier.dir i → (C.carrier◁C.carrier).pos )
                := by
                simp only [now_lhs, now_rhs] at now_we'd_be_talking
                exact now_we'd_be_talking

    have now_we'd_talk_even_more :
                (fun x => C.comult.onPos (cod x) : C.carrier.dir i → (C.carrier◁C.carrier).pos)
                =
                (fun pd =>
                      { fst := cod pd,
                        snd := fun qd => cod (comp pd qd)
                        } : C.carrier.dir i → (C.carrier◁C.carrier).pos ) := by
                        apply remove_casts
                        exact pre_now_we'd_talk_even_more

    have e_isso :
          C.comult.onPos (cod f)
          =
          { fst := cod f,
            snd := (fun qd => cod (comp f qd) : C.carrier.dir (cod f) → C.carrier.pos ) : (C.carrier◁C.carrier).pos }
          := congrFun now_we'd_talk_even_more f

    have e_isso_mesmo :
          (C.comult.onPos (cod f)).snd
          =
          Eq.rec (motive := fun x h => C.carrier.dir x → C.carrier.pos)
          (fun qd => cod (comp f qd))
          (_ : cod f = (C.comult.onPos (cod f)).fst)
          := snd_heq e_isso

    have agora_imagine : Eq.rec (motive := fun x h => C.carrier.dir x → C.carrier.pos)
                                 (fun qd => cod (comp f qd))
                                 (_ : cod f = (C.comult.onPos (cod f)).fst)
                         =
                         (fun qd => cod (comp f (dir_eq ▸ qd)))
      := push_cast_in_lambda
                (x := cod f)
                (y := (posAtDir (cod f)))
                (by rewrite [bookkeeping (cod f)]; simp)
                (fun qd => cod (comp f qd))

    have que_e_possivel : (C.comult.onPos (cod f)).snd
                          =
                          (fun qd => cod (comp f (dir_eq ▸ qd))) := by
      simp only [e_isso_mesmo, agora_imagine]


    have e_isso_demais : cod g =
                         cod (comp f (dir_eq ▸ g))
      := congrFun que_e_possivel (dir_eq ▸ g)

    have hihi : cod (comp f (dir_eq.symm ▸ dir_eq ▸ g))
                =
                cod (comp f g)
                := by
                rewrite [← cast_id' dir_eq]
                rfl
    rewrite [hihi] at e_isso_demais
    exact e_isso_demais.symm

def cod_2 {C : Comonoid} {i : C.carrier.pos} (f : C.carrier.dir (posAtDir i)) : C.carrier.pos :=
    (C.comult.onPos i).snd f

def comp_2 {C : Comonoid}
         {i : C.carrier.pos}
         (f : C.carrier.dir (posAtDir i))
         (g : C.carrier.dir (cod_2 f)) :
         C.carrier.dir i :=
         C.comult.onDir i ⟨ f , g ⟩

lemma across_cods {C : Comonoid}
                  {i : C.carrier.pos}
                  {f : C.carrier.dir i}
                  : cod f = cod_2 (dir_eq ▸ f) := by
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

lemma casted_sigma_fst_eq_s {C : Comonoid} -- C.carrier.pos
                            (p1 p2 : Sigma fun x => (C.carrier.dir x → (x : C.carrier.pos) × (C.carrier.dir x → C.carrier.pos))) -- ⟨posAtDir i, λ pd ↦ C.comult.onPos (cod_2 pd)⟩ and ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (C.comult.onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩
                            (pos_eq : p1 = p2)
                            (f : C.carrier.dir p1.fst) -- So the type of f is constructed *out of* a position
                            {g : (C.carrier◁C.carrier).dir (p1.snd f)}
                            (x : C.carrier.dir p1.fst = C.carrier.dir p2.fst) :
                            let elem_of_the_type : (C.carrier◁C.carrier◁C.carrier).dir p1 := ⟨ f , g ⟩
                            (pos_eq ▸ elem_of_the_type).fst = x ▸ f
                            := by
                            cases pos_eq
                            rfl

lemma casted_sigma_snd_eq_s {C : Comonoid} -- C.carrier.pos
                            (p1 p2 : Sigma fun x => (C.carrier.dir x → (x : C.carrier.pos) × (C.carrier.dir x → C.carrier.pos))) -- ⟨posAtDir i, λ pd ↦ C.comult.onPos (cod_2 pd)⟩ and ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (C.comult.onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩
                            (pos_eq : p1 = p2)
                            (f : C.carrier.dir p1.fst) -- So the type of f is constructed *out of* a position
                            {g : C.carrier.dir (p1.snd f).fst}
                            {h : C.carrier.dir ((p1.snd f).snd g)}
                            :
                            let elem_of_the_type : (C.carrier◁C.carrier◁C.carrier).dir p1 := ⟨ f , ⟨ g , h ⟩  ⟩
                            HEq (pos_eq ▸ elem_of_the_type).snd.fst g
                            := by
                            cases pos_eq
                            rfl

lemma casted_sigma_3rd_eq_s {C : Comonoid} -- C.carrier.pos
                            (p1 p2 : Sigma fun x => (C.carrier.dir x → (x : C.carrier.pos) × (C.carrier.dir x → C.carrier.pos))) -- ⟨posAtDir i, λ pd ↦ C.comult.onPos (cod_2 pd)⟩ and ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (C.comult.onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩
                            (pos_eq : p1 = p2)
                            (f : C.carrier.dir p1.fst) -- So the type of f is constructed *out of* a position
                            {g : C.carrier.dir (p1.snd f).fst}
                            {h : C.carrier.dir ((p1.snd f).snd g)}
                            {capstmt : α}
                            (more : HEq capstmt h )
                            :
                            let elem_of_the_type : (C.carrier◁C.carrier◁C.carrier).dir p1 := ⟨ f , ⟨ g , h ⟩  ⟩
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



def coassoc_dir_statement {C : Comonoid}
                          {i : C.carrier.pos}
                          (f : C.carrier.dir i)
                          (g : C.carrier.dir (cod f))
                          (h : C.carrier.dir (cod g))
                          :
                          comp (comp f g) (coassoc_pos_statement f g ▸ h)
                          =
                          comp f (comp g h) :=
  by

    have sacred_pos_left : (C.carrier◁C.carrier◁C.carrier).pos
      := ⟨posAtDir i, λ pd ↦ C.comult.onPos (cod_2 pd)⟩
    have sacred_pos_right : (C.carrier◁C.carrier◁C.carrier).pos
      := ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (C.comult.onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩
    let reduced_pos_type := Sigma (fun x => (C.carrier.dir x → (x : C.carrier.pos) × (C.carrier.dir x → C.carrier.pos)))
    have pos_eq :
        (⟨posAtDir i, λ pd ↦ C.comult.onPos (cod_2 pd)⟩ : reduced_pos_type)  =
        (⟨posAtDir (posAtDir i) , λ pd ↦ ⟨ cod_2 pd , λ qd ↦ cod_2 (comp_2 pd qd) ⟩ ⟩ : reduced_pos_type)
        := on_pos_eq (i := i) C.coassoc

    have coassoc_onDir := on_dir_eq (i := i) C.coassoc pos_eq

    let f' : C.carrier.dir (posAtDir i) := dir_eq ▸ f
    let g' : C.carrier.dir (posAtDir (cod f)) := dir_eq ▸ g

    let composed :
      (C.carrier◁C.carrier◁C.carrier).dir ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (C.comult.onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩
      := pos_eq ▸ (⟨f', ⟨g', h⟩⟩ )
    let composed_snd := composed.snd
    let composed_fst := composed.fst

    let wm_eq_wm' : pos_eq.symm ▸ composed = ⟨f', ⟨g', h⟩⟩ :=
      cast_id'''' (α := (C.carrier◁C.carrier◁C.carrier).pos) (β := (C.carrier◁C.carrier◁C.carrier).dir) pos_eq


    let some_kind_of_f : C.carrier.dir (posAtDir (posAtDir i)) := composed.fst
    let some_kind_of_g : C.carrier.dir (cod_2 some_kind_of_f) := composed.snd.fst
    let some_kind_of_h : C.carrier.dir (cod_2 (comp_2 some_kind_of_f some_kind_of_g)) := composed.snd.snd


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


    let capstmt : C.carrier.dir (cod (comp f g)) := (coassoc_pos_statement f g).symm ▸ h

    have ultimate :
      (⟨C.comult.onDir (posAtDir i) ⟨some_kind_of_f, some_kind_of_g⟩, some_kind_of_h⟩ : (C.carrier ◁ C.carrier).dir (C.comult.onPos i))
      =
      (⟨dir_eq ▸ C.comult.onDir i ⟨dir_eq ▸ f, g⟩, capstmt⟩ : (C.carrier ◁ C.carrier).dir (C.comult.onPos i))
      := by

      have cod_eq : cod (i := i) f = cod (i := posAtDir i) (dir_eq (i := i) ▸ f)
        := (cod_eq (i := i) (i' := posAtDir i) (h := (bookkeeping i).symm) (x := dir_eq) f cod).symm

      have H0 : dir_eq ▸ C.comult.onDir i ⟨dir_eq ▸ f, g⟩ = C.comult.onDir (posAtDir i) ⟨ dir_eq ▸ dir_eq ▸ f , ((cod_eq ▸ g) :  C.carrier.dir (cod (i := posAtDir i) (dir_eq ▸ f)))  ⟩ :=
        abstracted2 (α := C.carrier.pos)
                    (β := C.carrier.dir)
                    (i := i)
                    (posAt := λ i ↦ posAtDir (C := C) i)
                    (cod := λ {i} b ↦ cod (C := C) (i := i) b)
                    (fn := λ i f gw ↦ C.comult.onDir i ⟨ (dir_eq ▸ f) , gw ⟩)
                    (h := (bookkeeping i).symm)
                    (x := dir_eq)
                    (f := f)
                    (g := g)
                    cod_eq


      have cap_eq : HEq capstmt h := by
        let w := cast_heq ((coassoc_pos_statement f g).symm) h
        exact w

      have H : C.comult.onDir (posAtDir i) ⟨some_kind_of_f, some_kind_of_g⟩ = dir_eq ▸ C.comult.onDir i ⟨dir_eq ▸ f, g⟩ := by
        rw [H0]
        congr!
        . exact casted_sigma_fst_eq_s (p1 := ⟨posAtDir i, λ pd ↦ C.comult.onPos (cod_2 pd)⟩)
                                      (p2 := ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (C.comult.onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩)
                                      (pos_eq := pos_eq)
                                      (f := dir_eq ▸ f)
                                      (x := dir_eq)
        . unfold some_kind_of_g composed g'
          have x := casted_sigma_snd_eq_s (p1 := ⟨posAtDir i, λ pd ↦ C.comult.onPos (cod_2 pd)⟩)
                                          (p2 := ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (C.comult.onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩)
                                          (pos_eq := pos_eq)
                                          (f := dir_eq ▸ f)
                                          (g := dir_eq ▸ g)
                                          (h := h)
          simp_all only [heq_eqRec_iff_heq, f']
      congr!
      . unfold some_kind_of_f some_kind_of_g composed
        simp_all only [some_kind_of_f, composed, f', g', some_kind_of_g, some_kind_of_h]
        have x := casted_sigma_3rd_eq_s (p1 := ⟨posAtDir i, λ pd ↦ C.comult.onPos (cod_2 pd)⟩)
                                          (p2 := ⟨posAtDir (posAtDir i), λ pd ↦ ⟨ (C.comult.onPos (posAtDir i)).snd pd , λ qd ↦ cod_2 ((comp_2 pd qd)) ⟩⟩)
                                          (pos_eq := pos_eq)
                                          (f := dir_eq ▸ f)
                                          (g := dir_eq ▸ g)
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


def Hom_cat : {C : Comonoid} → (i j : C.carrier.pos) → Type :=
  λ {C} i j ↦ { f : C.carrier.dir i // cod f = j }

def id_cat : {C : Comonoid} → (i : C.carrier.pos) → { f : C.carrier.dir i // cod f = i } :=
  λ {C} i ↦
  ⟨ C.counit.onDir i () ,
  by

    unfold cod


    have H : (composemap C.comult (subst.whiskerRight C.counit)).onPos i
              =
             (subst.leftUnitor.inv C.carrier).onPos i := by
             rw [C.leftCounit]
    have M : (C.comult.onPos i).snd (C.counit.onDir (C.comult.onPos i).fst ())
              =
              i := congrFun (snd_eq H) ()
    have K : C.counit.onDir (C.comult.onPos i).fst ()
             =
             dir_eq ▸
             C.counit.onDir i () := npodese (C.comult.onPos i).fst i (bookkeeping i) dir_eq.symm (fun x => C.counit.onDir x ())
    conv at M =>
      lhs
      rewrite [K]
    exact M
    ⟩

def comp_cat : {C : Comonoid} →
               {i j k : C.carrier.pos} →
               { codlessf : C.carrier.dir i // cod codlessf = j } →
               { codlessg : C.carrier.dir j // cod codlessg = k } →
               { f : C.carrier.dir i // cod f = k } :=
  λ ⟨f, codf⟩ ⟨g, codg⟩ ↦ ⟨ comp f (codf ▸ g) , by
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

def assoc_cat : {C : Comonoid} →
                {i j k l : C.carrier.pos} →
                (f : { codlessf : C.carrier.dir i // cod codlessf = j }) →
                (g : { codlessg : C.carrier.dir j // cod codlessg = k }) →
                (h : { codlessh : C.carrier.dir k // cod codlessh = l }) →
                comp_cat (comp_cat f g) h = comp_cat f (comp_cat g h) :=
    λ {C} {i j k l} ⟨f, codf⟩ ⟨g, codg⟩ ⟨h, codh⟩ ↦ by
    have codg_eq_codg' : cod g = cod (codf ▸ g) := by
      exact dependentCongrArg g codf cod
    have dir_statement := coassoc_dir_statement (i := i) f (codf ▸ g) (codg_eq_codg' ▸ codg ▸ h)
    subst codh codg codf
    simp_all only [comp_cat]

  /-- The theorem: every comonoid in Poly induces a (small) category. -/
instance comonoid_to_category (C : Comonoid) : Category C.carrier.pos where
  Hom := Hom_cat
  id := id_cat
  comp := comp_cat
  id_comp := by sorry
  comp_id := by sorry
  assoc   := assoc_cat


end CategoryTheory
