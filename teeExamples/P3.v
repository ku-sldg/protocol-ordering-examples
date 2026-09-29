Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,0) :: (1,4) :: (3,0) :: (2,1) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ rtlib)
		| 0 => inl (msp _ rtlib app)
		| 1 => inl (msp _ appm rtlib)
		| 3 => inr (cor _ app)
		| 2 => inl (msp _ rtm appm)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A1 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(3,0) :: (1,0) :: (2,1) :: (4,0) :: nil ;
	label := fun ev =>
		match ev with
		| 3 => inr (cor _ app)
		| 0 => inl (msp _ rtlib app)
		| 1 => inl (msp _ appm rtlib)
		| 2 => inl (msp _ rtm appm)
		| 4 => inr (cor _ nwk)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A2 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,1) :: (1,0) :: (3,0) :: (2,5) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ rtlib)
		| 1 => inl (msp _ appm rtlib)
		| 0 => inl (msp _ rtlib app)
		| 3 => inr (cor _ app)
		| 2 => inl (msp _ rtm appm)
		| 5 => inr (cor _ appm)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A3 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,1) :: (1,0) :: (3,0) :: (2,1) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ rtlib)
		| 1 => inl (msp _ appm rtlib)
		| 0 => inl (msp _ rtlib app)
		| 3 => inr (cor _ app)
		| 2 => inl (msp _ rtm appm)
		| 5 => inr (cor _ swk)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P3 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: nil.
