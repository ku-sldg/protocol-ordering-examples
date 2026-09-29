Require Import Coq.Lists.List.
Require Import AttestationProtocolOrdering.utilities.reach.
Require Import AttestationProtocolOrdering.attackgraph.
Require Import AttestationProtocolOrdering.adversary_ordering.

Section AdversaryOrder.
    Context {components : Type}.
    Context {eqDec_components : forall (x y : components), {x = y} + {x <> y}}.

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





Lemma eqDec_advLabel : forall (l1 l2 : advLabel components),
    {l1 = l2} + {l1 <> l2}.
Proof.
    repeat decide equality.
Defined.

Lemma eqDec_ttl : forall (t1 t2 : tauTaggedLabel components),
    {t1 = t2} + {t1 <> t2}.
Proof.
    repeat decide equality.
Defined.


(* ==== the one-step successor relation, generated directly from
           advOrder and the built-in tau rule -- no enumeration of
           components needed. ==== *)

    (* The concrete edge function supplied as genericReach's `succ`
        parameter: the direct successors of t1 are exactly the second
        components of advOrder's pairs whose first component is t1
        (advOrder itself, oriented as edges), plus, when t1 is a
        blankTag, its own tauTag counterpart (the built-in tau rule).
        successors_sound/trianglelefteq_to_reachStar below show this
        list is exactly in sync with the two trianglelefteq
        constructors that are not reflexivity/transitivity. *)
    Definition successors (t : tauTaggedLabel components) : list (tauTaggedLabel components) :=
        map snd (filter (fun p => if eqDec_ttl (fst p) t then true else false) advOrder) ++
        match t with
        | blankTag _ a => tauTag _ a :: nil
        | tauTag _ _ => nil
        end.

    (* successors never over-approximates: every t2 it lists is a
        genuine one-step trianglelefteq successor of t1. This is the
        half of the successors/trianglelefteq correspondence used
        directly by reachStar_to_trianglelefteq's rs_step case, and it
        is what makes genericReach.reach_sound (a fact purely about
        `successors`) transfer to a soundness fact about trianglelefteq
        itself. *)
    Lemma successors_sound : forall t1 t2,
        In t2 (successors t1) -> 
        trianglelefteq t1 t2.
    Proof.
        intros t1 t2 H; apply in_app_or in H; destruct H as [H|H].
        - apply in_map_iff in H; destruct H as [[t1' t2'] [HEq HIn]]; simpl in HEq; subst.
          apply filter_In in HIn; destruct HIn as [HIn HIf]; simpl in HIf.
          destruct (eqDec_ttl t1' t1); [|inversion HIf]; subst.
          apply trianglelefteq_base_intro; auto.
        - destruct t1 as [a1|a1]; [inversion H|].
          destruct H; subst; [|inversion H]. 
          apply trianglelefteq_tau_intro.
    Qed.

    (* Forward half of the trianglelefteq / genericReach.reachStar
        equivalence: every trianglelefteq derivation replays as a
        reachStar walk over `successors` -- reflexivity/base/tau/trans
        map onto rs_refl/rs_step/rs_step/rs_trans respectively. Together
        with reachStar_to_trianglelefteq below, this is what lets
        trianglelefteqDec reduce deciding trianglelefteq to deciding
        genericReach's reachStar via reachDec. *)
    Lemma trianglelefteq_reachStar : forall t1 t2,
        trianglelefteq t1 t2 -> 
        reachStar successors t1 t2.
    Proof.
        intros t1 t2 H; induction H.
        - constructor.
        - apply rs_step; apply in_or_app; right; simpl; auto.
        - apply rs_step; apply in_or_app; left; apply in_map_iff.
          exists (t1, t2); split; auto.
          apply filter_In; split; auto.
          simpl; destruct (eqDec_ttl t1 t1); auto.
        - eapply rs_trans; eauto.
    Qed.

    (* Converse half of the equivalence: any genericReach.reachStar
        walk over `successors` witnesses a genuine trianglelefteq
        derivation (rs_refl/rs_step/rs_trans map back onto
        constructor/successors_sound/trianglelefteq_trans_intro). This
        is what trianglelefteqDec's `left` case needs to turn a
        reachDec witness back into a trianglelefteq proof. *)
    Lemma reachStar_trianglelefteq : forall t1 t2,
        reachStar successors t1 t2 -> 
        trianglelefteq t1 t2.
    Proof.
        intros t1 t2 H; induction H.
        - constructor.
        - apply successors_sound; auto.
        - eapply trianglelefteq_trans_intro; eauto.
    Qed.

    (* ==== a finite vertex set closed under successors, derived purely
        from advOrder and a query's start vertex t1 -- not from an
        enumeration of components. ==== *)

    (* Every label mentioned anywhere in advOrder, as endpoints of its
        pairs. This is the finite set that bounds all base-edge (i.e.
        advOrder-edge) successors; combined with its image under
        tauImage below it accounts for every vertex successors can ever
        produce, which is what candidates_closed relies on. *)
    Definition baseLabels : list (tauTaggedLabel components) :=
        flat_map (fun p => fst p :: snd p :: nil) advOrder.

    (* The target of the built-in tau rule: blankTag a and tauTag a
        both map to tauTag a. Mirrors the tau-rule branch of
        `successors` exactly, so that closing candidates under tauImage
        (below) also closes it under that branch of successors. *)
    Definition getTauTag (t : tauTaggedLabel components) : tauTaggedLabel components :=
        match t with
        | blankTag _ a => tauTag _ a
        | tauTag _ a => tauTag _ a
        end.

    (* The finite vertex list supplied as genericReach's `V` parameter
        for a query starting at t1: t1 itself, its tau-image, every
        label mentioned by advOrder, and all of their tau-images. This
        is deliberately independent of any enumeration of components --
        its size is bounded by advOrder's length -- yet candidates_closed
        below shows it is already closed under `successors`, which is
        exactly what genericReach.reachDec needs of V. *)
    Definition candidates (t1 : tauTaggedLabel components) : list (tauTaggedLabel components) :=
        t1 :: getTauTag t1 :: baseLabels ++ map getTauTag baseLabels.

    (* candidates t1 is closed under successors: a base-edge successor
        of any t in candidates t1 lands in baseLabels (it is literally
        the second half of an advOrder pair), and a tau-rule successor
        lands either in tauImage t1 (when t itself was t1) or in the
        tauImage baseLabels part (when t came from baseLabels). This is
        the raw closure fact behind candidates_nodup_closed below, which
        is genericReach's actual V_closed obligation. *)
    Lemma candidates_closed : forall t1 t t',
        In t (candidates t1) -> 
        In t' (successors t) -> 
        In t' (candidates t1).
    Proof.
        intros t1 t t' Ht Ht'; apply in_app_or in Ht'; destruct Ht' as [Ht'|Ht'].
        - apply in_map_iff in Ht'; destruct Ht' as [[t1' t2'] [HEq HIn]]; simpl in HEq; subst.
          apply filter_In in HIn; destruct HIn as [HIn _].
          right; right; apply in_or_app; left.
          apply in_flat_map; exists (t1', t'); split; simpl; auto.
        - destruct t as [a|a]; simpl in Ht'; [destruct Ht'|]; destruct Ht'; subst; try contradiction.
          simpl in Ht; destruct Ht as [Ht|[Ht|Ht]]; subst; simpl; auto.
        -- destruct t1 as [a1|a1]; simpl in Ht; inversion Ht.
        -- apply in_app_or in Ht; destruct Ht as [Ht|Ht].
        --- right; right; apply in_or_app; right.
            apply (in_map getTauTag baseLabels (blankTag components a) Ht).
        --- apply in_map_iff in Ht; destruct Ht as [t [Ht _]].
            destruct t; simpl in Ht; inversion Ht.
    Qed.

    (* candidates_closed restated with `In` tests against the
        nodup-normalized candidates list rather than the raw list
        (nodup doesn't change membership, only literal structure). This
        is exactly the shape of genericReach's V_closed hypothesis, and
        is passed as such to reachDec inside trianglelefteqDec below. *)
    Lemma candidates_nodup_closed : forall t1 t,
        In t (nodup eqDec_ttl (candidates t1)) ->
        forall t', In t' (successors t) ->
        In t' (nodup eqDec_ttl (candidates t1)).
    Proof.
        intros t1 t Ht t' Ht'.
        apply nodup_In; apply nodup_In in Ht.
        eapply candidates_closed; eauto.
    Qed.

    (* The query's own start vertex always lies in its candidates list
        (it's the literal head of `candidates t1`, mod nodup). This
        discharges genericReach.reachDec's Ht1 obligation automatically
        for every call inside trianglelefteqDec below. *)
    Lemma t1_in_candidates : forall t1, 
        In t1 (nodup eqDec_ttl (candidates t1)).
    Proof.
        intros t1; apply nodup_In; left; auto.
    Qed.

    (* The payoff: a decision procedure for trianglelefteq, built by
        instantiating genericReach.reachDec at T := tauTaggedLabel
        components, eqDec := eqDec_tauTaggedLabel, succ := successors,
        V := nodup eqDec_tauTaggedLabel (candidates t1), V_closed :=
        candidates_nodup_closed t1, and Ht1 := t1_in_candidates t1, then
        transporting the resulting {reachStar t1 t2} + {~ reachStar t1
        t2} sumbool across the trianglelefteq_to_reachStar /
        reachStar_to_trianglelefteq equivalence. Note V is built purely
        from t1 and advOrder, not from any enumeration of components,
        so this works whether or not components is finite. *)
    Definition trianglelefteqDec (t1 t2 : tauTaggedLabel components) :
        {trianglelefteq t1 t2} + {~ trianglelefteq t1 t2}.
    Proof.
        destruct (reachDec eqDec_ttl 
                           successors
                           (nodup eqDec_ttl (candidates t1))
                           (candidates_nodup_closed t1)
                           t1 
                           t2 
                           (t1_in_candidates t1)) 
                    as [H|H].
        - left; apply reachStar_trianglelefteq; auto.
        - right; intro HTri; apply H; apply trianglelefteq_reachStar; auto.
    Defined.

End AdversaryOrder.