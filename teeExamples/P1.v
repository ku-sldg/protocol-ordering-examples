Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(3,0) :: (2,0) :: (1,3) :: nil ;
	label := fun ev =>
		match ev with
		| 3 => inr (cor _ appm)
		| 0 => inl (msp _ appm app)
		| 2 => inr (cor _ app)
		| 1 => inl (msp _ rtm appm)
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
		(2,0) :: (1,0) :: (3,0) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inr (cor _ app)
		| 0 => inl (msp _ appm app)
		| 1 => inl (msp _ rtm appm)
		| 3 => inr (cor _ swk)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P1 : list (attackgraph components) := 
	A0 :: A1 :: nil.
