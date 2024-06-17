import Mathlib.data.setoid.basic -- per a emprar el quocient

-- Anem a estudiar i comprovar que tenim el colímit coigualador en la categoria de Tipus

namespace coigualador

-- Definim la mínima relació d'equivalència que conté una relació donada
inductive Eqvgen {X : Type} (R : X → X → Prop) : X → X → Prop where
  | base : ∀ {x y: X}, R x y → Eqvgen R x y
  | rfl : ∀(x:X), Eqvgen R x x
  | sim : ∀{x y:X}, Eqvgen R x y → Eqvgen R y x
  | trans : ∀{x y z: X}, Eqvgen R x y →  Eqvgen R y z → Eqvgen R x z

-- Definim θ de forma que ens relaciona f(x) i g(x) per a tot x en el tipus X
def θ {X Y: Type} (f: X → Y) (g: X → Y) : Y → Y → Prop := by
  intro y1 y2
  exact ∃ (x : X), (y1 = f x ∧ y2 = g x)

-- Ara, definim la relació d'equivalència Θ. És la mínima relació d'equivalència generada per θ
def Θ {X Y: Type} (f: X → Y) (g: X → Y) : Y → Y → Prop := Eqvgen (θ f g)

-- Comprovem que, efectivament, és una relació d'equivalència
theorem iseqv {X Y: Type} (f: X → Y) (g: X → Y): Equivalence (Θ f g) := by
  refine { refl := ?refl, symm := ?symm, trans := ?trans }
  -- cas reflexiu
  exact Eqvgen.rfl
  -- cas simètric
  exact Eqvgen.sim
  -- cas transitiu
  exact Eqvgen.trans

-- Un setoid és un parell (Ω,R) on Ω és un tipus i R una relació d'equivalència sobre Ω.
-- Definim el setoide com Y el nostre tipus i Θ la relació sobre Y
def Setoide {X Y: Type} (f: X → Y) (g: X → Y): Setoid Y:= by
  apply Setoid.mk (Θ f g) (iseqv f g)

-- Definim el coigualador com el quocient de Y per la relació d'equivalència Θ
def CoIg {X Y: Type} (f: X → Y) (g: X → Y) : Type :=
  Quotient (Setoide f g)

-- Donat un element d'Y, podem considerar la projecció canònica al coigualador
def proj {X Y: Type} (f g: X → Y): Y → (CoIg f g) := by
  intro y
  exact Quotient.mk (Setoide f g) y

-- Demostrem que el diagrama commuta, és a dir, el cocon està ben definit
theorem TCocon {X Y: Type} {f g: X → Y}: (proj f g) ∘ f = (proj f g) ∘ g := by
  apply funext
  intro x
  apply Quotient.sound
  apply Eqvgen.base
  use x

-- En la categoria de Tipus, el coigualador verifica la Propietat Universal.
-- Per a poder definir l'aplicació de la propietat universal, necessitem definir prèviament
-- com es defineix una aplicació d'un quocient a un tipus Z
-- Comencem per definir el nucli, també anomenat Kernel, d'una aplicació h
def Ker {X Y: Type} (h: X → Y): X → X → Prop := by
  intro x1 x2
  exact h x1 = h x2

-- Comprovem que la pertinença al nucli d'una aplicació és una relació d'equivalència
theorem KerEquiv {X Y: Type} (h: X → Y): Equivalence (Ker h) := by
  refine { refl := ?refl, symm := ?symm, trans := ?trans }
  -- reflexiva
  intro x
  exact rfl
  -- simètrica
  intro x1 x2
  intro h1
  exact h1.symm
  -- transitiva
  intro x1 x2 x3
  intro h1 h2
  exact h1.trans h2

-- Comprovem que si ens donen un cocon (equivalent a donar h de forma que h ∘ f = h ∘ g), aleshores
-- f(x) i g(x) es troben al nucli d'h
theorem PUniv1 {X Y: Type} {f g: X → Y} {Z: Type} (h: Y → Z) (h1: h ∘ f = h ∘ g): ∀ x: X, (Ker h) (f x) (g x) := by
  intro x
  rw [Ker]
  calc
    h (f x) = (h ∘ f) x := by exact rfl
    _ = (h ∘ g) x := by exact congrFun h1 x
    _ = h (g x) := by exact rfl

-- Comprovem que si dos tipus pertanyen a la mateixa classe en el coigualador, aleshores
-- van a tindre la mateixa imatge mitjançant l'aplicació que intentem definir. És a dir,
-- estem comprovant que definir l'aplicació així farà que estiga ben definida, ja que
-- si estan relacionades per Θ, pel Kernel d'h també ho estaran, és a dir, efectivament, Θ
-- és la mínima relació d'equivalència que relaciona f(x) i g(x)
theorem PUniv2 {X Y: Type} {f g: X → Y} {Z: Type} (h: Y → Z) (h1: h ∘ f = h ∘ g): ∀ (y1 y2: Y), ((Θ f g) y1 y2) → ((Ker h) y1 y2) := by
  intro y1 y2
  intro h2
  induction h2
  -- cas base
  rename_i y3 y4 h2
  rw [θ] at h2
  apply Exists.elim h2
  intro x
  intro ⟨ h3, h4 ⟩
  rw [h3, h4]
  exact PUniv1 h h1 x
  -- cas refl
  rename_i y3
  exact rfl
  -- cas sim
  rename_i y3 y4 h2 h3
  exact Equivalence.symm (KerEquiv h) h3
  -- cas transitiu
  rename_i y3 y4 y5 h2 h3 h4 h5
  exact Equivalence.trans (KerEquiv h) h4 h5

-- Definim un setoide com X el nostre tipus i la pertinença al Kernel, la relació sobre X
def SKer {X Y: Type}(h: X → Y) : Setoid X:= by
  apply Setoid.mk (Ker h) (KerEquiv h)

-- Definim el quocient QKer de X per la relació d'equivalència del Kernel
def QKer {X Y: Type}(h: X → Y) : Type :=
  Quotient (SKer h)

-- Definirem l'aplicació PUniv del Coigualador a un tipus Z, la que estem buscant per vore
-- que efectivament, el coigualador té la propietat universal, com la composició de dos aplicacions.
-- La primera és la inclusió del coigualador en el Kernel d'h, ho vorem en Puniv3. Ho podem fer perquè
-- Θ és la mínima relació entre f(x) i g(x), vist en PUniv2. La segona és la que tractem de definir ara,
-- volem establir una aplicació entre el Kernel i un tipus donat Z, de forma que enviem
-- una classe [b] en el Kernel d'h (siguent h: X → Z) a h(b), i així vegem que està ben definida
def Mon {X Y: Type}(h: X → Y) : (QKer h) → Y := by
  intro cx
  have h1 : ∀ (x1 x2: X), ((SKer h).r x1 x2) → (h x1 = h x2) := by
    intro x1 x2 h1
    exact h1
  apply Quotient.lift h h1
  exact cx

-- Donat un element d'X, podem considerar la projecció canònica al Kernel
def projKer {X Y: Type} (h: X → Y): X → (QKer h) := by
  intro x
  exact Quotient.mk (SKer h) x

-- Com hem dit, definim la primera aplicació és la inclusió del coigualador en el Kernel d'h
def PUniv3 {X Y: Type} {f g: X → Y} {Z: Type} (h: Y → Z) (h1: h ∘ f = h ∘ g):  CoIg f g → (QKer h) := by
  intro cy
  have h1 : ∀ (y1 y2: Y), ((Setoide f g).r y1 y2) → (projKer h y1 = projKer h y2) := by
    intro y1 y2
    intro h2
    have h3 : ((Θ f g) y1 y2) := by exact h2
    have h4 : ((Ker h) y1 y2) := by exact PUniv2 h h1 y1 y2 h2
    apply Quotient.sound
    exact h4
  apply Quotient.lift (projKer h) h1
  exact cy

-- Ja podem definir la PUniv que busquem, que és la composició de Mon i PUniv3
def PUniv {X Y: Type} {f g: X → Y} {Z: Type} (h: Y → Z) (h1: h ∘ f = h ∘ g): CoIg f g → Z:=  (Mon h) ∘ (PUniv3 h h1)

-- Comprovem que l'aplicació està ben definida i, efectivament, fa que el diagrama commute
theorem TComm {X Y: Type} {f g: X → Y} (Z: Type) (h: Y → Z) (h1: h ∘ f = h ∘ g): PUniv h h1 ∘ proj f g = h:= by
  apply funext
  intro y
  exact rfl

-- Vegem que PUniv és la única aplicació que satisfà les anteriors condicions
theorem TUniv {X Y: Type} {f g: X → Y} (Z: Type) (h: Y → Z) (h1: h ∘ f = h ∘ g) (l: CoIg f g → Z) (h2: l ∘ proj f g = h ): l = PUniv h h1:= by
  apply funext
  intro cy
  have h3 : ∃ (y : Y), Quotient.mk (Setoide f g) y = cy := by
    exact Quot.exists_rep cy
  apply Exists.elim h3
  intro y
  intro h4
  rw [h4.symm]
  calc
    l (Quotient.mk (Setoide f g) y) =  l ( (proj f g) y) := by exact rfl
    _ = (l ∘ proj f g) y := by exact rfl
    _ = h y := by exact congrFun h2 y
    _  = PUniv h h1 (Quotient.mk (Setoide f g) y) := by exact rfl

-- Així, hem comprovat que el coigualador és un colímit en la categoria de Tipus (el colímit és el parell
-- format pel coigualador i l'aplicació proj)
end coigualador
