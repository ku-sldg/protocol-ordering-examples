Require Import AttestationProtocolOrdering.set_relationship.

Require Import ProtocolOrderingExamples.components.
Require Import ProtocolOrderingExamples.P1.
Require Import ProtocolOrderingExamples.P2.
Require Import ProtocolOrderingExamples.P3.
Require Import ProtocolOrderingExamples.P4.
Require Import ProtocolOrderingExamples.P5.
Require Import ProtocolOrderingExamples.P6.
Require Import ProtocolOrderingExamples.P7.

Lemma P1_P1 : order_fix P1 P1 = equiv.
Proof. auto. Qed.
Lemma P1_P2 : order_fix P1 P2 = geq.
Proof. auto. Qed.
Lemma P1_P3 : order_fix P1 P3 = equiv.
Proof. auto. Qed.
Lemma P1_P4 : order_fix P1 P4 = geq.
Proof. auto. Qed.
Lemma P1_P5 : order_fix P1 P5 = geq.
Proof. auto. Qed.
Lemma P1_P6 : order_fix P1 P6 = geq.
Proof. auto. Qed.
Lemma P1_P7 : order_fix P1 P7 = equiv.
Proof. auto. Qed.

Lemma P2_P1 : order_fix P2 P1 = leq.
Proof. auto. Qed.
Lemma P2_P2 : order_fix P2 P2 = equiv.
Proof. auto. Qed.
Lemma P2_P3 : order_fix P2 P3 = leq.
Proof. auto. Qed.
Lemma P2_P4 : order_fix P2 P4 = incomparable.
Proof. auto. Qed.
Lemma P2_P5 : order_fix P2 P5 = incomparable.
Proof. auto. Qed.
Lemma P2_P6 : order_fix P2 P6 = incomparable.
Proof. auto. Qed.
Lemma P2_P7 : order_fix P2 P7 = leq.
Proof. auto. Qed.

Lemma P3_P1 : order_fix P3 P1 = equiv.
Proof. auto. Qed.
Lemma P3_P2 : order_fix P3 P2 = geq.
Proof. auto. Qed.
Lemma P3_P3 : order_fix P3 P3 = equiv.
Proof. auto. Qed.
Lemma P3_P4 : order_fix P3 P4 = geq.
Proof. auto. Qed.
Lemma P3_P5 : order_fix P3 P5 = geq.
Proof. auto. Qed.
Lemma P3_P6 : order_fix P3 P6 = geq.
Proof. auto. Qed.
Lemma P3_P7 : order_fix P3 P7 = equiv.
Proof. auto. Qed.

Lemma P4_P1 : order_fix P4 P1 = leq.
Proof. auto. Qed.
Lemma P4_P2 : order_fix P4 P2 = incomparable.
Proof. auto. Qed.
Lemma P4_P3 : order_fix P4 P3 = leq.
Proof. auto. Qed.
Lemma P4_P4 : order_fix P4 P4 = equiv.
Proof. auto. Qed.
Lemma P4_P5 : order_fix P4 P5 = incomparable.
Proof. auto. Qed.
Lemma P4_P6 : order_fix P4 P6 = leq. (** interesting *)
Proof. auto. Qed.
Lemma P4_P7 : order_fix P4 P7 = leq.
Proof. auto. Qed.

(** update p5 description *)
Lemma P5_P1 : order_fix P5 P1 = leq.
Proof. auto. Qed.
Lemma P5_P2 : order_fix P5 P2 = incomparable.
Proof. auto. Qed.
Lemma P5_P3 : order_fix P5 P3 = leq.
Proof. auto. Qed.
Lemma P5_P4 : order_fix P5 P4 = incomparable.
Proof. auto. Qed.
Lemma P5_P5 : order_fix P5 P5 = equiv.
Proof. auto. Qed.
Lemma P5_P6 : order_fix P5 P6 = incomparable.
Proof. auto. Qed.
Lemma P5_P7 : order_fix P5 P7 = leq.
Proof. auto. Qed.

Lemma P6_P1 : order_fix P6 P1 = leq.
Proof. auto. Qed.
Lemma P6_P2 : order_fix P6 P2 = incomparable.
Proof. auto. Qed.
Lemma P6_P3 : order_fix P6 P3 = leq.
Proof. auto. Qed.
Lemma P6_P4 : order_fix P6 P4 = geq.
Proof. auto. Qed.
Lemma P6_P5 : order_fix P6 P5 = incomparable.
Proof. auto. Qed.
Lemma P6_P6 : order_fix P6 P6 = equiv.
Proof. auto. Qed.
Lemma P6_P7 : order_fix P6 P7 = leq.
Proof. auto. Qed.

Lemma P7_P1 : order_fix P7 P1 = equiv.
Proof. auto. Qed.
Lemma P7_P2 : order_fix P7 P2 = geq.
Proof. auto. Qed.
Lemma P7_P3 : order_fix P7 P3 = equiv.
Proof. auto. Qed.
Lemma P7_P4 : order_fix P7 P4 = geq.
Proof. auto. Qed.
Lemma P7_P5 : order_fix P7 P5 = geq.
Proof. auto. Qed.
Lemma P7_P6 : order_fix P7 P6 = geq.
Proof. auto. Qed.
Lemma P7_P7 : order_fix P7 P7 = equiv.
Proof. auto. Qed.