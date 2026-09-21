Require Import Coq.Lists.List.
Require Import Lia.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.
Require Import AttestationProtocolOrdering.set_relationship.

Require Import ProtocolOrderingExamples.components.
Require Import ProtocolOrderingExamples.trianglelefteq.

Definition advOrder : list (tauTaggedLabel components * tauTaggedLabel components) := 
    (blankTag _ (cor _ vc), blankTag _ (cor _ ker)) ::
    (blankTag _ (cor _ vc), blankTag _ (cor _ vcm)) ::
    (blankTag _ (cor _ vcm), blankTag _ (cor _ lkim)) ::    
    (tauTag _ (cor _ vc), tauTag _ (cor _ ker)) ::
    (tauTag _ (cor _ vc), tauTag _ (cor _ vcm)) ::
    (tauTag _ (cor _ vcm), tauTag _ (cor _ lkim)) ::
    (tauTag _ (cor _ vc), blankTag _ (cor _ mm)) ::
    nil.


Definition level (comp : components) : nat :=
    match comp with
    | vc => 0
    | ker => 1
    | vcm => 1
    | lkim => 2
    | mm => 4
    | _ => 0
    end.

Definition levelAdv (a : advLabel components) : nat :=
    match a with
    | cor _ comp => level comp
    | rep _ comp => level comp
    end.

Definition rank (t : tauTaggedLabel components) : nat :=
    match t with
    | blankTag _ a => 2 * levelAdv a
    | tauTag _ a => 2 * levelAdv a + 1
    end.

Lemma trianglelefteq_charac : forall t1 t2,
    @trianglelefteq _ advOrder t1 t2 -> 
    t1 = t2 \/ rank t1 < rank t2.
Proof.
    intros t1 t2 H; induction H; auto.
    - simpl; lia.
    - right. simpl in H; destruct H as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]];
      try (inversion H; subst;
      simpl; lia).
    - destruct IHtrianglelefteq1 as [|IH1], IHtrianglelefteq2 as [|IH2]; subst; auto.
      simpl; lia.
Qed.

Lemma trianglelefteq_antisymmetric : forall t1 t2,
    @trianglelefteq _ advOrder t1 t2 -> 
    @trianglelefteq _ advOrder t2 t1 -> 
    t1 = t2.
Proof.
    intros t1 t2 H12 H21.
    apply trianglelefteq_charac in H12; apply trianglelefteq_charac in H21.
    destruct H12; auto. destruct H21; auto.
    lia.
Qed.




Definition myOrder_fix := @order_fix components (@trianglelefteq _ advOrder) (@trianglelefteqDec _ eqDec_components advOrder).