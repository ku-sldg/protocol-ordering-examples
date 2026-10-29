Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.
Require Import AttestationProtocolOrdering.set_relationship.
Require Import AttestationProtocolOrdering.make_adversary_ordering.

Require Import ProtocolOrderingExamples.components.

Definition advOrder : list (tauTaggedLabel components * tauTaggedLabel components) := nil.

Lemma trianglelefteq_antisymmetric : forall t1 t2,
    makeTrianglelefteq advOrder t1 t2 ->
    makeTrianglelefteq advOrder t2 t1 ->
    t1 = t2.
Proof.
    rewrite <- (makeTrianglelefteq_antisymmetric_same eqDec_components advOrder); vm_compute; auto.
Admitted.