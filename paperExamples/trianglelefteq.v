Require Import Coq.Lists.List.
Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.

Section AdversaryOrder.
    Context {components : Type}.

    Context {advOrder : list (tauTaggedLabel components * tauTaggedLabel components)}.

    Inductive trianglelefteq : tauTaggedLabel components -> tauTaggedLabel components -> Prop :=
    | trianglelefteq_refl_intro : forall t, 
        trianglelefteq t t
    | trianglelefteq_tau_intro  : forall l, 
        trianglelefteq (blankTag _ l) (tauTag _ l)
    | trianglelefteq_base_intro : forall t1 t2,
        In (t1, t2) advOrder ->
        trianglelefteq t1 t2
    | trianglelefteq_trans_intro : forall t1 t2 t3,
        trianglelefteq t1 t2 ->
        trianglelefteq t2 t3 ->
        trianglelefteq t1 t3.

    Lemma trianglelefteq_reflexive : forall t, 
        trianglelefteq t t.
    Proof.
        intros; apply trianglelefteq_refl_intro.
    Qed.

    Lemma trianglelefteq_tau : forall l,
        trianglelefteq (blankTag _ l) (tauTag _ l).
    Proof.
        intros; apply trianglelefteq_tau_intro.
    Qed.

    Lemma trianglelefteq_transitive : forall t1 t2 t3,
        trianglelefteq t1 t2 ->
        trianglelefteq t2 t3 ->
        trianglelefteq t1 t3.
    Proof.
        intros; eapply trianglelefteq_trans_intro; eauto.
    Qed.

End AdversaryOrder.