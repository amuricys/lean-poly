import Init.Prelude
import Mathlib.CategoryTheory.Category.Basic


lemma fst_eq {H X : Sigma B} (e : H = X) : H.1 = X.1 := by
  cases e
  rfl

lemma snd_eq {H X : Σ _ : α, β} (e : H = X) : H.snd = X.snd := by
  cases e
  rfl

def snd_heq {α : Type} {β : α → Type} {H X : Sigma β} (h : H = X) : H.snd = (fst_eq h) ▸ X.snd := by
  cases h
  rfl

lemma fst_do_i_actual
              {α : Type}      -- C.carrier.pos
              {i i' : α}      -- i := i, i' := (C.comult.onPos i).fst
              {β : α → Type}  -- λ x ↦ C.carrier.dir (C.comult.onPos x).fst
              {x_general : (x : α) → β x → α} -- fun x y => (C.comult.onPos x).snd y : (x : C.carrier.pos) → C.carrier.dir (C.comult.onPos x).fst → C.carrier.pos
              (h : i = i')    -- bookkeeping i : i = (C.comult.onPos i).fst
              (pd : β i)      -- pd : C.carrier.dir (C.comult.onPos i).fst
              (dir_eq : β i = β i') -- dir_eq : C.carrier.dir (C.comult.onPos i).fst = C.carrier.dir (C.comult.onPos (C.comult.onPos i).fst).fst
              : (x_general i' (dir_eq ▸ pd)) = (x_general i pd) -- cod_2 pd
              := by
              cases h
              simp


lemma sigma_eq {α : Type}
               {β : α → Type}
               {a1 a2 : α}
               {b1 : β a1}
               {b2 : β a2}
               (fst_eq : a1 = a2)
               (snd_eq : b1 = fst_eq ▸ b2) :
               ({ fst := a1 , snd := b1 : Sigma β} = { fst := a2, snd := b2}) := by
               cases fst_eq
               cases snd_eq
               rfl

lemma eq_to_heq {α : Type} {β : Type} {a : α} {b : β} (h : α = β) (r : a = h ▸ b) : (@HEq α a β b) :=
  by
  cases r
  cases h
  rfl

lemma eq_type_fam {α : Type} {β : α → Type} {i i' : α} (h : i = i'): β i = β i' := by
  cases h
  rfl

lemma npodese {α : Type}          -- C.carrier.pos
              {β : α → Type}      -- fun x => C.carrier.dir x
              (a : α)             -- (C.comult.onPos i).fst
              (b : α)             -- i
              (k : a = b)         -- bookkeeping i
              (h : β a = β b)     -- dir_eq
              (f : (x : α) → β x) -- fun x => C.counit.onDir x ()
              : f a = h ▸ f b
              := by
              cases k
              rfl

lemma remove_casts {α β : Type} {a b : α} (h : α = β) (lolproof : h ▸ a = h ▸ b) : a = b := by
  cases h
  exact lolproof

lemma cast_id {α : Type} {β : α → Type} {a b : α} {c : β b} (x : a = b) (h : β a = β b) : c = (h ▸ (h.symm ▸ c)):= by
  cases x
  simp

lemma cast_id' {α : Type} {β : Type} {a : α} (h : α = β) : a = (h ▸ (h.symm ▸ a)):= by
  cases h
  rfl

lemma cast_id'' {α β : Type} (x : α) (h : α = β) : h ▸ h.symm ▸ x = x := by
  cases h
  rfl


lemma cast_sigma_fst {α : Type} {β : α → Type} {a1 a2 : α}
                        {b1 : β a1} {b2 : β a2} (h : a1 = a2)
                        (e : Sigma.mk a1 b1 = Sigma.mk a2 b2) :
                        b1 = h ▸ b2 := by
      cases h
      cases e
      rfl


lemma push_cast_in_lambda {α : Sort u}
                          {γ : α → Sort v}
                          {χ : Sort u}
                          {x y : α}
                          (h : x = y)
                          (f : (x' : γ x) → χ) :
                          Eq.rec (motive := fun (x : α) _ => γ x → χ)
                                 (fun i => f i)
                                 h
                          =
                          fun x' => f (((by simp [h]) : γ y = γ x) ▸ x')
                    := by
                    cases h
                    rfl


lemma lhs_lemma {arg1 arg2 out : Type u}
                {f : arg1 → out}
                (d : (arg1 → out) = (arg2 → out))
                (t : arg1 = arg2)
                :
                (fun x => f x)
                =
                (d ▸ (fun x => f (t ▸ x))) := by
                cases t
                rfl

lemma sigmas_eq {α : Type}
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
              (k : i' = i) :
              (⟨ h' ▸ (h'.symm ▸ x), t ▸ qd ⟩ : Sigma (β₁ (a := i)))
              =
              u ▸ (⟨ h ▸ x , qd ⟩ : Sigma (β₁ (a := i'))) := by
              cases k
              simp
              apply cast_id''
              exact h'.symm
