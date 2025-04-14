
Inductive components : Type := .

Lemma eqDec_components : 
    forall (x y : components), {x = y} + {x <> y}.
Proof. try decide equality. Admitted.
