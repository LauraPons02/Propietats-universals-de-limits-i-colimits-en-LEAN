import Mathlib.data.setoid.basic --per a que importe Prod.ext

-- Anem a estudiar i comprovar que tenim el límit pullback en la categoria de Tipus

namespace pullback

-- Definim el producte fibrat com
def ProdFib {X Y Z: Type} (f: X → Z) (g: Y → Z):=
  {p : X × Y // f p.1 = g p.2} -- p de parell

-- Donat un element del producte fibrat, podem definir la projecció a la primera component com
def π1 {X Y Z: Type} (f: X → Z) (g: Y → Z): ProdFib f g → X := by
  intro p
  exact p.val.1

-- Donat un element del producte fibrat, podem definir la projecció a la segona component com
def π2 {X Y Z: Type} (f: X → Z) (g: Y → Z): ProdFib f g → Y := by
  intro p
  exact p.val.2

-- Demostrem que el diagrama commuta, és a dir, el con està ben definit
theorem TCon {X Y Z: Type} (f: X → Z) (g: Y → Z): f ∘ π1 f g = g ∘ π2 f g := by
  apply funext
  intro p
  calc
    (f ∘ π1 f g) p = f p.val.1 := by exact rfl
    _  = g p.val.2 := by exact p.property
    _  = (g ∘ π2 f g) p := by exact rfl

-- En la categoria de Tipus, el producte fibrat verifica la Propietat Universal
def PUniv {X Y Z W: Type} (f: X → Z) (g: Y → Z) (h1: W → X) (h2: W → Y) (h3: f ∘ h1 = g ∘ h2): W → ProdFib f g:= by
  intro w
  apply Subtype.mk (h1 w, h2 w) -- demos propietat
  calc
    f (h1 w, h2 w).fst = (f ∘ h1) w := by exact rfl
    _ = (g ∘ h2) w := by exact congrFun h3 w
    _ = g (h1 w, h2 w).snd := by exact rfl

-- Comprovem que les aplicacions projecció estan ben definides i fan que el diagrama commute
theorem TComm1 {X Y Z W: Type} (f: X → Z) (g: Y → Z) (h1: W → X) (h2: W → Y) (h3: f ∘ h1 = g ∘ h2): π1 f g ∘ PUniv f g h1 h2 h3 = h1 := by
  apply funext
  intro w
  exact rfl

theorem TComm2 {X Y Z W: Type} (f: X → Z) (g: Y → Z) (h1: W → X) (h2: W → Y) (h3: f ∘ h1 = g ∘ h2): π2 f g ∘ PUniv f g h1 h2 h3 = h2 := by
  apply funext
  intro w
  exact rfl

-- Vegem que PUniv és la única aplicació que satisfà les anteriors condicions
theorem TUniv {X Y Z W: Type} (f: X → Z) (g: Y → Z) (h1: W → X) (h2: W → Y) (h3: f ∘ h1 = g ∘ h2) (l: W → ProdFib f g) (l1: π1 f g ∘ l = h1) (l2: π2 f g ∘ l = h2) : l = PUniv f g h1 h2 h3 := by
  apply funext
  intro w
  apply Subtype.eq
  have h4: (l w).val.1 = (PUniv f g h1 h2 h3 w).val.1 := by
    calc
      (l w).val.fst = (π1 f g ∘ l) w := by exact rfl
      _ = h1 w := by exact congrFun l1 w
      _  = (PUniv f g h1 h2 h3 w).val.1 := by exact rfl
  have h5: (l w).val.2 = (PUniv f g h1 h2 h3 w).val.2 := by
    calc
      (l w).val.snd = (π2 f g ∘ l) w := by exact rfl
      _ = h2 w := by exact congrFun l2 w
      _  = (PUniv f g h1 h2 h3 w).val.2 := by exact rfl
  exact Prod.ext h4 h5

-- Així, hem comprovat que el pullback és un límit en la categoria de Tipus (el límit és el parell
-- format pel pullback junt a les aplicacions π1 i π2).
end pullback
