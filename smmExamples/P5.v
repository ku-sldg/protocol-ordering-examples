Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(1,5) :: (1,2) :: (5,0) :: (2,0) :: (4,0) :: (3,1) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ sinit mle)
		| 5 => inr (cor _ mle)
		| 2 => inl (msp _ sinit stm)
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
		(1,2) :: (2,5) :: (5,0) :: (3,1) :: (4,0) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ sinit mle)
		| 2 => inl (msp _ sinit stm)
		| 5 => inr (cor _ stm)
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
		(1,2) :: (2,0) :: (5,1) :: (4,0) :: (3,6) :: (6,1) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ sinit mle)
		| 2 => inl (msp _ sinit stm)
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

Definition A3 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(1,6) :: (6,2) :: (5,2) :: (2,0) :: (3,1) :: (4,0) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ sinit mle)
		| 6 => inr (cor _ sinit)
		| 2 => inl (msp _ sinit stm)
		| 5 => inr (cor _ stm)
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

Definition A4 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(1,2) :: (2,0) :: (5,2) :: (3,6) :: (6,1) :: (4,0) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ sinit mle)
		| 2 => inl (msp _ sinit stm)
		| 0 => inl (msp _ mle app)
		| 5 => inr (cor _ stm)
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
		(1,7) :: (7,2) :: (5,1) :: (4,0) :: (3,6) :: (6,1) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 1 => inl (msp _ sinit mle)
		| 7 => inr (rep _ sinit)
		| 2 => inl (msp _ sinit stm)
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

Definition P5 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: A5 :: nil.
