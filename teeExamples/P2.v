Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,0) :: (3,1) :: (1,0) :: (5,0) :: (2,3) :: nil ;
	label := fun ev =>
		match ev with
		| 4 => inr (cor _ app)
		| 0 => inl (msp _ rtlib app)
		| 3 => inl (msp _ rtm appm)
		| 1 => inl (msp _ appm rtlib)
		| 5 => inr (cor _ nwk)
		| 2 => inl (msp _ pxy rtlib)
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
		(5,0) :: (3,1) :: (1,5) :: (2,3) :: (4,0) :: nil ;
	label := fun ev =>
		match ev with
		| 5 => inr (cor _ rtlib)
		| 0 => inl (msp _ rtlib app)
		| 3 => inl (msp _ rtm appm)
		| 1 => inl (msp _ appm rtlib)
		| 2 => inl (msp _ pxy rtlib)
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
		(5,1) :: (1,0) :: (3,6) :: (6,1) :: (2,5) :: (2,3) :: (4,0) :: nil ;
	label := fun ev =>
		match ev with
		| 5 => inr (cor _ rtlib)
		| 1 => inl (msp _ appm rtlib)
		| 0 => inl (msp _ rtlib app)
		| 3 => inl (msp _ rtm appm)
		| 6 => inr (cor _ appm)
		| 2 => inl (msp _ pxy rtlib)
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
		(5,1) :: (1,0) :: (3,1) :: (2,5) :: (2,3) :: (4,0) :: (6,1) :: nil ;
	label := fun ev =>
		match ev with
		| 5 => inr (cor _ rtlib)
		| 1 => inl (msp _ appm rtlib)
		| 0 => inl (msp _ rtlib app)
		| 3 => inl (msp _ rtm appm)
		| 2 => inl (msp _ pxy rtlib)
		| 4 => inr (cor _ app)
		| 6 => inr (cor _ swk)
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
		(7,1) :: (1,0) :: (5,2) :: (2,3) :: (3,1) :: (4,0) :: (6,2) :: nil ;
	label := fun ev =>
		match ev with
		| 7 => inr (cor _ swk)
		| 1 => inl (msp _ appm rtlib)
		| 0 => inl (msp _ rtlib app)
		| 5 => inr (cor _ rtlib)
		| 2 => inl (msp _ pxy rtlib)
		| 3 => inl (msp _ rtm appm)
		| 4 => inr (cor _ app)
		| 6 => inr (cor _ pxy)
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
		(5,2) :: (2,3) :: (3,7) :: (7,1) :: (1,0) :: (4,0) :: (6,2) :: nil ;
	label := fun ev =>
		match ev with
		| 5 => inr (cor _ rtlib)
		| 2 => inl (msp _ pxy rtlib)
		| 3 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm rtlib)
		| 0 => inl (msp _ rtlib app)
		| 4 => inr (cor _ app)
		| 6 => inr (cor _ pxy)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A6 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(5,2) :: (2,3) :: (2,7) :: (3,1) :: (1,8) :: (7,1) :: (8,0) :: (4,0) :: (6,2) :: nil ;
	label := fun ev =>
		match ev with
		| 5 => inr (cor _ rtlib)
		| 2 => inl (msp _ pxy rtlib)
		| 3 => inl (msp _ rtm appm)
		| 7 => inr (rep _ rtlib)
		| 1 => inl (msp _ appm rtlib)
		| 8 => inr (cor _ rtlib)
		| 0 => inl (msp _ rtlib app)
		| 4 => inr (cor _ app)
		| 6 => inr (cor _ pxy)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P2 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: A5 :: A6 :: nil.
