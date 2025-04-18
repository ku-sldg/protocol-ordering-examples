
Inductive components : Type :=
| bins : components
| config : components
| sel : components
| am : components
| ker : components
| lkim : components
| ima : components
| init : components
| boot : components.

Lemma eqDec_components : 
    forall (x y : components), {x = y} + {x <> y}.
Proof.
    decide equality.
Defined.
