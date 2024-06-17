import Mathlib.data.setoid.basic -- per a emprar el quocient

-- Anem a estudiar i comprovar que tenim el colímit pushout en la categoria de Tipus

namespace pushout

-- Definim la mínima relació d'equivalència que conté una relació donada
inductive Eqvgen {X : Type} (R : X → X → Prop) : X → X → Prop where
  | base : ∀ {x y: X}, R x y → Eqvgen R x y
  | rfl : ∀(x:X), Eqvgen R x x
  | sim : ∀{x y:X}, Eqvgen R x y → Eqvgen R y x
  | trans : ∀{x y z: X}, Eqvgen R x y →  Eqvgen R y z → Eqvgen R x z

-- Definim θ de forma que ens relaciona ι1(f(x)) i ι2(g(x)) per a tot x en el tipus X,
-- siguent ι1 i ι2 les inclusions canòniques de X i Y al coproducte de X i Y, respectivament.
-- Notem que hem denotat al coproducte de X i Y com Sum X Y
def θ {X Y Z: Type} (f: Z → X) (g: Z → Y) : Sum X Y → Sum X Y → Prop := by
  intro w1 w2
  exact ∃ (z : Z), (w1 = Sum.inl (f z)  ∧ w2 = Sum.inr (g z))

-- Ara, definim la relació d'equivalència Θ. És la mínima relació d'equivalència generada per θ
def Θ {X Y Z: Type} (f: Z → X) (g: Z → Y) : Sum X Y → Sum X Y → Prop := Eqvgen (θ f g)

-- Comprovem que, efectivament, és una relació d'equivalència
theorem iseqv {X Y Z: Type} (f: Z → X) (g: Z → Y): Equivalence (Θ f g) := by
  refine { refl := ?refl, symm := ?symm, trans := ?trans }
  -- cas reflexiu
  exact Eqvgen.rfl
  -- cas simètric
  exact Eqvgen.sim
  -- cas transitiu
  exact Eqvgen.trans

-- Un setoid és un parell (Ω,R) on Ω és un tipus i R una relació d'equivalència sobre Ω.
-- Definim el setoide com el coproducte de X i Y el nostre tipus i Θ la relació sobre aquest
def Setoide {X Y Z: Type} (f: Z → X) (g: Z → Y): Setoid (Sum X Y) := by
  apply Setoid.mk (Θ f g) (iseqv f g)

-- Definim el pushout o suma amalgamada com el quocient del coproducte de X i Y, Sum X Y,
-- per la relació d'equivalència Θ
def SumAm {X Y Z: Type} (f: Z → X) (g: Z → Y) : Type :=
  Quotient (Setoide f g)

-- Donat un element de Sum X Y, podem considerar la projecció canònica al pushout
def proj {X Y Z: Type} (f: Z → X) (g: Z → Y): Sum X Y → SumAm f g := by
  intro w
  exact Quotient.mk (Setoide f g) w

-- Definim les inclusions de X i Y al pushout, que seran les aplicacions que formen
-- part del colímit, junt amb el pushout
def ι1 {X Y Z: Type} (f: Z → X) (g: Z → Y): X → SumAm f g := (proj f g) ∘ Sum.inl

def ι2 {X Y Z: Type} (f: Z → X) (g: Z → Y): Y → SumAm f g := (proj f g) ∘ Sum.inr

-- Demostrem que el diagrama commuta, és a dir, el cocon està ben definit
theorem TCocon {X Y Z: Type}  {f: Z → X} {g: Z → Y}: (ι1 f g) ∘ f = (ι2 f g) ∘  g := by
  apply funext
  intro z
  apply Quotient.sound
  apply Eqvgen.base
  use z

-- En la categoria de Tipus, el pushout verifica la Propietat Universal, definim l'aplicació
-- que ho demostra. Definim aquesta aplicació definint primer una aplicació l de Sum X Y al tipus W,
-- el tipus on volíem arribar, de forma que donat un l en el coproducte, si l pertany al tipus X,
-- l és de la forma l = f(z), aleshores se li assigna el valor h1(f(z)), i d'igual manera si l peryany
-- al tipus Y, que és de la forma l = g(z) se li assigna el valor h2(g(z)). Una vegada tenim aquesta
-- aplicació l definida, la PUniv que busquem és aquella que verifica l = PUniv ∘ proj
def PUniv {X Y Z W: Type} (f: Z → X) (g: Z → Y) (h1: X → W) (h2: Y → W) (h3: h1 ∘ f = h2 ∘ g): (SumAm f g) → W := by
  let l : (Sum X Y) → W := by
    intro t
    cases t with
    | inl x => exact (h1 x)
    | inr y => exact (h2 y)
  have h: ∀ (p q : Sum X Y), (Setoide f g).r p q → (l p = l q) := by
    intro h4
    intro h5
    intro h6
    induction h6
    -- Cas base
    rename_i j k h8
    apply Exists.elim h8
    intro z
    intro ⟨ h9, h10 ⟩
    calc
      l j = l (Sum.inl (f z)) := by exact congrArg l h9
      _ = h1 (f z) := by exact rfl
      _ = (h1 ∘ f) z := by exact rfl
      _ = (h2 ∘ g) z := by exact congrFun h3 z
      _ = h2 (g z) := by exact rfl
      _ = l (Sum.inr (g z)) := by exact rfl
      _ = l k := by exact congrArg l (id h10.symm)
    -- Cas rfl
    rename_i j
    exact rfl
    -- Cas sim
    rename_i j k h6 h7
    exact id h7.symm
    -- Cas trans
    rename_i x y z j k h6 h7
    exact h6.trans h7
  apply Quotient.lift l h

-- Comprovem que les aplicacions inclusions estan ben definides i, efectivament, fan que el diagrama commute
theorem TComm1 {X Y Z W: Type} (f: Z → X) (g: Z → Y) (h1: X → W) (h2: Y → W) (h3: h1 ∘ f = h2 ∘ g):  PUniv f g h1 h2 h3 ∘ ι1 f g = h1 := by
  apply funext
  intro x
  exact rfl

theorem TComm2 {X Y Z W: Type} (f: Z → X) (g: Z → Y) (h1: X → W) (h2: Y → W) (h3: h1 ∘ f = h2 ∘ g):  PUniv f g h1 h2 h3 ∘ ι2 f g = h2 := by
  apply funext
  intro y
  exact rfl

-- Vegem que PUniv és la única aplicació que satisfà les anteriors condicions
theorem TUniv {X Y Z W: Type} (f: Z → X) (g: Z → Y) (h1: X → W) (h2: Y → W) (h3: h1 ∘ f = h2 ∘ g) (l: SumAm f g → W) (l1: l ∘ ι1 f g  = h1) (l2: l ∘ ι2 f g  = h2) : l = PUniv f g h1 h2 h3 := by
  apply funext
  intro ct
  have h4 : ∃ (t : Sum X Y), Quotient.mk (Setoide f g) t = ct := by
    exact Quot.exists_rep ct
  apply Exists.elim h4
  intro t
  cases t
  -- cas x
  rename_i x
  intro h5
  calc
    l ct = l ((ι1 f g) x) := by exact congrArg l (id h5.symm)
    _ = (l ∘ (ι1 f g)) x := by exact rfl
    _ = h1 x := by exact congrFun l1 x
    _ = PUniv f g h1 h2 h3 (ι1 f g (x))  := by exact rfl
    _ = PUniv f g h1 h2 h3 ct := by exact congrArg (PUniv f g h1 h2 h3) h5
  -- cas y
  rename_i y
  intro h5
  calc
    l ct = l ((ι2 f g) y) := by exact congrArg l (id h5.symm)
    _ = (l ∘ (ι2 f g)) y := by exact rfl
    _ = h2 y := by exact congrFun l2 y
    _ = PUniv f g h1 h2 h3 (ι2 f g (y))  := by exact rfl
    _ = PUniv f g h1 h2 h3 ct := by exact congrArg (PUniv f g h1 h2 h3) h5

-- Així, hem comprovat que el pushout és un colímit en la categoria de Tipus (el colímit és el parell
-- format pel pushout i les aplicacions ι1 i ι2)
end pushout
