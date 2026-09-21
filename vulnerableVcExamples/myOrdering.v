Require Import AttestationProtocolOrdering.set_relationship.

Require Import ProtocolOrderingExamples.components.
Require Import ProtocolOrderingExamples.advOrder.

Require Import ProtocolOrderingExamples.P2.
Require Import ProtocolOrderingExamples.P3.



Lemma P2_P3 : myOrder_fix P2 P3 = equiv.
Proof. auto. Qed.
