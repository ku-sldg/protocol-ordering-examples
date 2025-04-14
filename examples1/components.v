
Inductive components : Type :=
| sys : components
| vc : components
| ker : components
| a1 : components
| a2 : components
| vm : components
| rtm : components.

Lemma eqDec_components : 
    forall (x y : components), {x = y} + {x <> y}.
Proof.
    decide equality.
Defined.
