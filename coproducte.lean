-- Anem a estudiar i comprovar que tenim el colímit coproducte en la categoria de Tipus

namespace coproducte

-- Definim un tipus I que farà d'índex
variable (I : Type)
-- Llavors una família de tipus indexada per I és una variable
variable (𝕏 : I → Type)

-- El coproducte de la família 𝕏 es denota com Σ(i:I), 𝕏 i
#check Σ(i:I), 𝕏 i

-- Donat un element d'una component podem considerar la inclusió i-èssima
def ι {I : Type} {𝕏 : I → Type} (i : I) : 𝕏 i → (Σ(i:I), 𝕏 i) := by
  intro x
  exact ⟨ i, x ⟩

-- En la categoria de Tipus, el coproducte verifica la Propietat Universal
def PUniv {I Z : Type} {𝕏 : I → Type} (𝕗 : ∀(i:I), 𝕏 i → Z ) : (Σ(i:I), 𝕏 i) → Z := by
  intro ⟨ i, x ⟩
  exact 𝕗 i x

-- Comprovem que l'aplicació està ben definida i fa que el diagrama commute
theorem TComm {I Z : Type} {𝕏 : I → Type} (𝕗 : ∀(i:I), 𝕏 i → Z ) (i : I) : (PUniv 𝕗) ∘ (ι i) = 𝕗 i := by
  apply funext
  intro z
  exact rfl

-- Comprovem que l'aplicació PUniv és la única que satisfà les condicions anteriors per a tot i en I
theorem TUniv {I Z : Type} {𝕏 : I → Type} (𝕗 : ∀(i:I), 𝕏 i → Z ) (h :  (Σ(i:I), 𝕏 i) → Z) (hi : ∀(i:I) , h ∘ (ι i) = 𝕗 i) : h = PUniv 𝕗 := by
  apply funext
  intro ⟨ i, x ⟩
  calc
     h { fst := i, snd := x } = (h ∘ (ι i)) x := by exact rfl
    _ = (𝕗 i) x := by exact congrFun (hi i) x
    _ = PUniv 𝕗 { fst := i, snd := x } := by exact rfl

-- Així, hem comprovat que el coprodcute és un colímit en la categoria de Tipus (el colímit és el parell
-- format pel coproducte i l'aplicació ι).
end coproducte
