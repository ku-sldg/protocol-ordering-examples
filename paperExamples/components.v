
Inductive components : Type :=
| sys : components
| vc : components
| ker : components
| vcm : components
| lkim : components
| rtm : components
| mm : components
| c : components.

Lemma eqDec_components : 
    forall (x y : components), {x = y} + {x <> y}.
Proof.
    decide equality.
Defined.
