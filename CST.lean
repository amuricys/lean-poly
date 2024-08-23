import Init.Prelude

def η [Monad m] {A : Type} (a : A) : m A := pure a
def μ [Monad m] {A : Type} (a : m (m A)) : m A := a >>= id
notation "⟨" f:80 "×" g:80 "⟩" => Prod.map f g

def myswap : a × b × c → (a × b) × c := λ ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩
def myunswap : (a × b) × c → a × b × c := λ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩

class CommutativeMonad (m : Type → Type) extends Monad m where
  σ : m a × m b → m (a × b)
  comm_l : let arr : m a × Unit → m a := Functor.map Prod.fst ∘ σ ∘ ⟨id × η⟩ ; arr = Prod.fst
  comm_r : let arr : Unit × m a → m a := Functor.map (f := m) Prod.snd ∘ σ ∘ ⟨η (m := m) × id⟩ ; arr = Prod.snd
  assoc : let arrleft : m a × m b × m c → m (a × b × c) := σ ∘ ⟨id × σ⟩
          let arrright : m a × m b × m c → m (a × b × c) := Functor.map myunswap ∘ σ ∘ ⟨σ × id⟩ ∘ myswap
          arrleft = arrright
  relift : let arr : a × b → m (a × b) := σ ∘ ⟨η × η⟩
          arr = η
  rejoin : let arrleft : m (m a) × m (m b) → m (a × b) := μ ∘ Functor.map σ ∘ σ
           let arrright : m (m a) × m (m b) → m (a × b) := σ ∘ ⟨μ × μ⟩
           arrleft = arrright

def f : [CommutativeMonad m] → m a → m b → m (a × b) :=
  λ ma mb ↦ do
    let a ← ma
    let b ← mb
    return (a, b)

def g : [CommutativeMonad m] → m a → m b → m (a × b) :=
  λ ma mb ↦ do
    let b ← mb
    let a ← ma
    return (a, b)

theorem f_eq_g : [CommutativeMonad m] → f (m := m) ma mb = g (m := m) ma mb := by
  sorry
