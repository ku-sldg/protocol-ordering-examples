Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(3,0) :: (1,0) :: (4,0) :: (2,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ mle app)
		| 3 => inr (cor _ app)
		| 1 => inl (msp _ sinit mle)
		| 4 => inr (cor _ smm)
		| 2 => inl (msp _ cpu sinit)
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
		(4,0) :: (1,4) :: (2,1) :: (3,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ mle app)
		| 4 => inr (cor _ mle)
		| 1 => inl (msp _ sinit mle)
		| 2 => inl (msp _ cpu sinit)
		| 3 => inr (cor _ app)
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
		(4,1) :: (1,0) :: (2,5) :: (5,1) :: (3,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ mle app)
		| 4 => inr (cor _ mle)
		| 1 => inl (msp _ sinit mle)
		| 2 => inl (msp _ cpu sinit)
		| 5 => inr (cor _ sinit)
		| 3 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P1 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: nil.
