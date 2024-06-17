-- Anem a estudiar i comprovar que existeix el límit igualador en la categoria de Tipus

namespace igualador

-- Definim l'igualador com
def Ig {X Y: Type} (f: X → Y) (g: X → Y) : Type :=
  {x : X // f x = g x}

-- Donat un element de l'igualador, podem definir l'aplicació inclusió com
def inc {X Y: Type} (f g: X → Y): (Ig f g) → X := by
  intro h
  exact h.val

-- Demostrem que el diagrama commuta, és a dir, el con està ben definit
theorem TCon {X Y: Type} {f g: X → Y}: f ∘ (inc f g) = g ∘ (inc f g) := by
  apply funext
  intro x
  calc
    (f ∘ inc f g) x = f x.val :=by exact rfl
    _ = g x.val := by exact x.property
    _ = (g ∘ inc f g) x := by exact rfl

-- En la categoria de Tipus, l'igualador verifica la Propietat Universal.
def PUniv {X Y: Type} {f g: X → Y} {Z: Type} (h: Z → X) (h1: f ∘ h = g ∘ h): Z → Ig f g:= by
  intro z
  apply Subtype.mk (h z)
  calc
    f (h z) = (f ∘ h) z := by exact rfl
    _  = (g ∘ h) z:= by exact congrFun h1 z
    _  = g (h z) := by exact rfl

-- Comprovem que l'aplicació està ben definida i, efectivament, fa que el diagrama commute
theorem TComm {X Y: Type} {f g: X → Y} (Z: Type) (h: Z → X) (h1: f ∘ h = g ∘ h): inc f g ∘ PUniv h h1 = h:= by
  apply funext
  intro z
  exact rfl

-- Vegem que PUniv és la única aplicació que satisfà les anteriors condicions
theorem TUniv {X Y: Type} {f g: X → Y} (Z: Type) (h: Z → X) (h1: f ∘ h = g ∘ h) (l: Z → Ig f g) (h2: inc f g ∘ l = h): l = PUniv h h1:= by
  apply funext
  intro z
  apply Subtype.eq
  calc
    (l z).val = (inc f g ∘ l) z := by exact rfl
    _  = h z := by exact congrFun h2 z
    _  = (PUniv h h1 z).val := by exact rfl

-- Així, hem comprovat que el igualador és un límit en la categoria de Tipus (el límit és el parell
-- format per l'igualador i l'aplicació inc).
end igualador
