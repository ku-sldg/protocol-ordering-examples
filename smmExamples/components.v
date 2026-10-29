
Inductive components : Type :=
| app : components
| stm : components
| mle : components
| sinit : components
| ker : components
| boot : components
| smm : components
| bios : components
| cpu : components
| crtm : components.

Lemma eqDec_components : 
    forall (x y : components), {x = y} + {x <> y}.
Proof.
    decide equality.
Defined.
