
Inductive components : Type :=
| app : components
| pxy : components
| rtlib : components
| nwk : components
| appm : components
| swk : components
| rtm : components.

Lemma eqDec_components : 
    forall (x y : components), {x = y} + {x <> y}.
Proof.
    decide equality.
Defined.
