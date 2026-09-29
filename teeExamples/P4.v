Require Import AttestationProtocolOrdering.attackgraph.
Require Import ProtocolOrderingExamples.components.

Definition A0 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(7,1) :: (1,2) :: (6,0) :: (4,7) :: (5,1) :: (3,4) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 2 => inl (msp _ appm rtlib)
		| 6 => inr (cor _ nwk)
		| 4 => inl (msp _ rtm appm)
		| 5 => inr (cor _ app)
		| 3 => inl (msp _ pxy rtlib)
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
		(4,7) :: (7,1) :: (3,4) :: (3,6) :: (6,2) :: (1,2) :: (2,0) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 3 => inl (msp _ pxy rtlib)
		| 6 => inr (cor _ rtlib)
		| 2 => inl (msp _ appm rtlib)
		| 5 => inr (cor _ app)
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
		(6,0) :: (4,1) :: (1,2) :: (3,4) :: (2,0) :: (7,1) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 6 => inr (cor _ nwk)
		| 4 => inl (msp _ rtm appm)
		| 1 => inl (msp _ appm app)
		| 2 => inl (msp _ appm rtlib)
		| 3 => inl (msp _ pxy rtlib)
		| 7 => inr (cor _ swk)
		| 5 => inr (cor _ app)
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
		(4,1) :: (1,2) :: (3,4) :: (3,6) :: (6,2) :: (5,1) :: (7,1) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 4 => inl (msp _ rtm appm)
		| 1 => inl (msp _ appm app)
		| 2 => inl (msp _ appm rtlib)
		| 3 => inl (msp _ pxy rtlib)
		| 6 => inr (cor _ rtlib)
		| 5 => inr (cor _ app)
		| 7 => inr (cor _ swk)
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
		(4,7) :: (7,1) :: (3,4) :: (1,2) :: (2,6) :: (6,0) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 3 => inl (msp _ pxy rtlib)
		| 2 => inl (msp _ appm rtlib)
		| 6 => inr (cor _ rtlib)
		| 5 => inr (cor _ app)
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
		(7,1) :: (1,2) :: (4,1) :: (3,4) :: (5,1) :: (2,6) :: (6,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 7 => inr (cor _ swk)
		| 1 => inl (msp _ appm app)
		| 2 => inl (msp _ appm rtlib)
		| 4 => inl (msp _ rtm appm)
		| 3 => inl (msp _ pxy rtlib)
		| 5 => inr (cor _ app)
		| 6 => inr (cor _ rtlib)
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
		(4,7) :: (7,1) :: (3,4) :: (3,6) :: (6,2) :: (8,1) :: (1,2) :: (2,0) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 3 => inl (msp _ pxy rtlib)
		| 6 => inr (cor _ rtlib)
		| 2 => inl (msp _ appm rtlib)
		| 8 => inr (cor _ swk)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A7 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,8) :: (8,1) :: (3,4) :: (3,6) :: (6,2) :: (1,2) :: (5,1) :: (7,1) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 4 => inl (msp _ rtm appm)
		| 8 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 3 => inl (msp _ pxy rtlib)
		| 6 => inr (cor _ rtlib)
		| 2 => inl (msp _ appm rtlib)
		| 5 => inr (cor _ app)
		| 7 => inr (cor _ swk)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A8 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(6,0) :: (4,1) :: (1,8) :: (3,4) :: (8,2) :: (2,0) :: (7,1) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 6 => inr (cor _ nwk)
		| 4 => inl (msp _ rtm appm)
		| 1 => inl (msp _ appm app)
		| 8 => inr (rep _ swk)
		| 3 => inl (msp _ pxy rtlib)
		| 2 => inl (msp _ appm rtlib)
		| 7 => inr (cor _ swk)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A9 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,1) :: (1,8) :: (3,4) :: (3,6) :: (6,2) :: (8,2) :: (2,0) :: (5,1) :: (7,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 4 => inl (msp _ rtm appm)
		| 1 => inl (msp _ appm app)
		| 8 => inr (cor _ appm)
		| 3 => inl (msp _ pxy rtlib)
		| 6 => inr (cor _ rtlib)
		| 2 => inl (msp _ appm rtlib)
		| 5 => inr (cor _ app)
		| 7 => inr (cor _ swk)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A10 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(7,1) :: (1,8) :: (6,0) :: (4,7) :: (5,1) :: (3,4) :: (8,2) :: (2,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 8 => inr (rep _ appm)
		| 6 => inr (cor _ nwk)
		| 4 => inl (msp _ rtm appm)
		| 5 => inr (cor _ app)
		| 3 => inl (msp _ pxy rtlib)
		| 2 => inl (msp _ appm rtlib)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A11 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,4) :: (7,1) :: (1,2) :: (4,7) :: (2,0) :: (6,3) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 2 => inl (msp _ appm rtlib)
		| 6 => inr (cor _ rtlib)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A12 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,7) :: (7,1) :: (3,4) :: (3,6) :: (6,2) :: (8,2) :: (2,0) :: (1,8) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 3 => inl (msp _ pxy rtlib)
		| 6 => inr (cor _ rtlib)
		| 2 => inl (msp _ appm rtlib)
		| 8 => inr (cor _ swk)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A13 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,4) :: (4,1) :: (1,2) :: (5,1) :: (7,1) :: (2,0) :: (6,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 1 => inl (msp _ appm app)
		| 2 => inl (msp _ appm rtlib)
		| 5 => inr (cor _ app)
		| 7 => inr (cor _ swk)
		| 6 => inr (cor _ rtlib)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A14 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(7,1) :: (1,8) :: (4,1) :: (3,4) :: (8,2) :: (2,6) :: (5,1) :: (6,0) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 7 => inr (cor _ swk)
		| 1 => inl (msp _ appm app)
		| 8 => inr (rep _ swk)
		| 4 => inl (msp _ rtm appm)
		| 3 => inl (msp _ pxy rtlib)
		| 2 => inl (msp _ appm rtlib)
		| 6 => inr (cor _ rtlib)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A15 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,7) :: (7,1) :: (3,4) :: (1,8) :: (8,2) :: (6,0) :: (2,6) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 3 => inl (msp _ pxy rtlib)
		| 8 => inr (rep _ appm)
		| 2 => inl (msp _ appm rtlib)
		| 6 => inr (cor _ rtlib)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A16 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,8) :: (8,1) :: (3,4) :: (3,6) :: (6,2) :: (1,9) :: (5,1) :: (9,2) :: (2,0) :: (7,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 4 => inl (msp _ rtm appm)
		| 8 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 3 => inl (msp _ pxy rtlib)
		| 6 => inr (cor _ rtlib)
		| 2 => inl (msp _ appm rtlib)
		| 9 => inr (rep _ swk)
		| 5 => inr (cor _ app)
		| 7 => inr (cor _ swk)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A17 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(4,1) :: (1,9) :: (1,8) :: (3,4) :: (3,6) :: (6,2) :: (9,2) :: (2,0) :: (8,2) :: (5,1) :: (7,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 4 => inl (msp _ rtm appm)
		| 1 => inl (msp _ appm app)
		| 9 => inr (rep _ swk)
		| 8 => inr (cor _ appm)
		| 3 => inl (msp _ pxy rtlib)
		| 6 => inr (cor _ rtlib)
		| 2 => inl (msp _ appm rtlib)
		| 5 => inr (cor _ app)
		| 7 => inr (cor _ swk)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A18 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,4) :: (7,1) :: (1,2) :: (4,7) :: (2,0) :: (6,3) :: (9,1) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 2 => inl (msp _ appm rtlib)
		| 6 => inr (cor _ rtlib)
		| 9 => inr (cor _ swk)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A19 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(9,2) :: (2,0) :: (4,7) :: (7,1) :: (3,4) :: (3,6) :: (6,2) :: (8,1) :: (1,9) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 9 => inr (rep _ appm)
		| 2 => inl (msp _ appm rtlib)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 3 => inl (msp _ pxy rtlib)
		| 6 => inr (cor _ rtlib)
		| 8 => inr (cor _ swk)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A20 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,4) :: (4,9) :: (9,1) :: (1,2) :: (5,1) :: (7,1) :: (2,0) :: (6,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 9 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 2 => inl (msp _ appm rtlib)
		| 5 => inr (cor _ app)
		| 7 => inr (cor _ swk)
		| 6 => inr (cor _ rtlib)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A21 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,4) :: (4,1) :: (1,9) :: (9,2) :: (2,0) :: (5,1) :: (7,1) :: (6,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 1 => inl (msp _ appm app)
		| 9 => inr (cor _ appm)
		| 2 => inl (msp _ appm rtlib)
		| 5 => inr (cor _ app)
		| 7 => inr (cor _ swk)
		| 6 => inr (cor _ rtlib)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A22 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(9,2) :: (2,0) :: (4,7) :: (7,1) :: (3,4) :: (3,6) :: (6,2) :: (8,2) :: (1,9) :: (1,8) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 9 => inr (rep _ appm)
		| 2 => inl (msp _ appm rtlib)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 3 => inl (msp _ pxy rtlib)
		| 6 => inr (cor _ rtlib)
		| 8 => inr (cor _ swk)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A23 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,4) :: (7,1) :: (1,9) :: (4,7) :: (9,2) :: (6,3) :: (2,0) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 9 => inr (cor _ swk)
		| 2 => inl (msp _ appm rtlib)
		| 6 => inr (cor _ rtlib)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A24 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,4) :: (4,9) :: (9,1) :: (1,10) :: (5,1) :: (7,1) :: (10,2) :: (2,0) :: (6,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 9 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 10 => inr (rep _ swk)
		| 5 => inr (cor _ app)
		| 7 => inr (cor _ swk)
		| 2 => inl (msp _ appm rtlib)
		| 6 => inr (cor _ rtlib)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A25 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,4) :: (4,1) :: (1,10) :: (1,9) :: (10,2) :: (2,0) :: (9,2) :: (5,1) :: (7,1) :: (6,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 1 => inl (msp _ appm app)
		| 10 => inr (rep _ swk)
		| 9 => inr (cor _ appm)
		| 2 => inl (msp _ appm rtlib)
		| 5 => inr (cor _ app)
		| 7 => inr (cor _ swk)
		| 6 => inr (cor _ rtlib)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A26 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,4) :: (3,9) :: (4,1) :: (1,2) :: (9,2) :: (5,1) :: (7,1) :: (2,10) :: (10,0) :: (6,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 9 => inr (rep _ rtlib)
		| 1 => inl (msp _ appm app)
		| 2 => inl (msp _ appm rtlib)
		| 5 => inr (cor _ app)
		| 7 => inr (cor _ swk)
		| 10 => inr (cor _ rtlib)
		| 6 => inr (cor _ rtlib)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A27 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(9,2) :: (2,10) :: (10,0) :: (8,3) :: (3,9) :: (3,4) :: (7,1) :: (1,2) :: (4,7) :: (6,3) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 9 => inr (rep _ rtlib)
		| 2 => inl (msp _ appm rtlib)
		| 10 => inr (cor _ rtlib)
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 6 => inr (cor _ rtlib)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A28 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,4) :: (7,1) :: (1,10) :: (4,7) :: (10,2) :: (6,3) :: (2,0) :: (9,1) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 10 => inr (rep _ appm)
		| 2 => inl (msp _ appm rtlib)
		| 6 => inr (cor _ rtlib)
		| 9 => inr (cor _ swk)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A29 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,4) :: (10,2) :: (2,0) :: (7,1) :: (1,10) :: (1,9) :: (4,7) :: (9,2) :: (6,3) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 10 => inr (rep _ appm)
		| 2 => inl (msp _ appm rtlib)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 9 => inr (cor _ swk)
		| 6 => inr (cor _ rtlib)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A30 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(8,3) :: (3,4) :: (3,9) :: (4,1) :: (1,11) :: (9,2) :: (5,1) :: (11,2) :: (2,10) :: (7,1) :: (10,0) :: (6,3) :: nil ;
	label := fun ev =>
		match ev with
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 9 => inr (rep _ rtlib)
		| 1 => inl (msp _ appm app)
		| 11 => inr (rep _ swk)
		| 2 => inl (msp _ appm rtlib)
		| 5 => inr (cor _ app)
		| 10 => inr (cor _ rtlib)
		| 7 => inr (cor _ swk)
		| 6 => inr (cor _ rtlib)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition A31 : attackgraph components := 
{|
	event := 
		nat ;
	edges :=
		(9,2) :: (2,10) :: (10,0) :: (8,3) :: (3,9) :: (3,4) :: (7,1) :: (1,11) :: (4,7) :: (11,2) :: (6,3) :: (5,1) :: nil ;
	label := fun ev =>
		match ev with
		| 9 => inr (rep _ rtlib)
		| 2 => inl (msp _ appm rtlib)
		| 10 => inr (cor _ rtlib)
		| 0 => inl (msp _ rtlib app)
		| 8 => inr (cor _ pxy)
		| 3 => inl (msp _ pxy rtlib)
		| 4 => inl (msp _ rtm appm)
		| 7 => inr (cor _ appm)
		| 1 => inl (msp _ appm app)
		| 11 => inr (rep _ appm)
		| 6 => inr (cor _ rtlib)
		| 5 => inr (cor _ app)
		| _ => inl (ms _)
		end ;
	eqDec_event := 
		ltac:(decide equality) ;
	eqDec_component := 
		eqDec_components
|}.

Definition P4 : list (attackgraph components) := 
	A0 :: A1 :: A2 :: A3 :: A4 :: A5 :: A6 :: A7 :: A8 :: A9 :: A10 :: A11 :: A12 :: A13 :: A14 :: A15 :: A16 :: A17 :: A18 :: A19 :: A20 :: A21 :: A22 :: A23 :: A24 :: A25 :: A26 :: A27 :: A28 :: A29 :: A30 :: A31 :: nil.
