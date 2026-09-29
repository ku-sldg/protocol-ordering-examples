Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(2,5) :: (2,1) :: (5,0) :: (1,0) :: (4,0) :: (3,2) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ sinit mle)
		| 5 => inr (cor _ mle)
		| 1 => inl (msp _ sinit smm)
		| 0 => inl (msp _ mle app)
		| 4 => inr (cor _ app)
		| 3 => inl (msp _ cpu sinit)
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
		(2,1) :: (1,5) :: (5,0) :: (3,2) :: (4,0) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ sinit mle)
		| 1 => inl (msp _ sinit smm)
		| 5 => inr (cor _ smm)
		| 0 => inl (msp _ mle app)
		| 3 => inl (msp _ cpu sinit)
		| 4 => inr (cor _ app)
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
		(2,6) :: (6,1) :: (5,1) :: (1,0) :: (3,2) :: (4,0) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ sinit mle)
		| 6 => inr (cor _ sinit)
		| 1 => inl (msp _ sinit smm)
		| 5 => inr (cor _ smm)
		| 0 => inl (msp _ mle app)
		| 3 => inl (msp _ cpu sinit)
		| 4 => inr (cor _ app)
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
		(2,1) :: (1,0) :: (5,2) :: (4,0) :: (3,6) :: (6,2) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ sinit mle)
		| 1 => inl (msp _ sinit smm)
		| 0 => inl (msp _ mle app)
		| 5 => inr (cor _ mle)
		| 4 => inr (cor _ app)
		| 3 => inl (msp _ cpu sinit)
		| 6 => inr (cor _ sinit)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A4 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(2,1) :: (1,0) :: (5,1) :: (3,6) :: (6,2) :: (4,0) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ sinit mle)
		| 1 => inl (msp _ sinit smm)
		| 0 => inl (msp _ mle app)
		| 5 => inr (cor _ smm)
		| 3 => inl (msp _ cpu sinit)
		| 6 => inr (cor _ sinit)
		| 4 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A5 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(2,7) :: (7,1) :: (5,2) :: (4,0) :: (3,6) :: (6,2) :: (1,0) :: nil ;
	label := fun ev =>
		match ev with
		| 2 => inl (msp _ sinit mle)
		| 7 => inr (rep _ sinit)
		| 1 => inl (msp _ sinit smm)
		| 5 => inr (cor _ mle)
		| 4 => inr (cor _ app)
		| 0 => inl (msp _ mle app)
		| 3 => inl (msp _ cpu sinit)
		| 6 => inr (cor _ sinit)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P3 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: A5 :: nil.
