Require Import List.
Require Import Streams.
Require Import PeanoNat.
Require Import Permutation.
Require Import Lia.

Import ListNotations.

Fixpoint take {A : Type} (n : nat) (s : Stream A) : list A :=
    match n with
      | O => nil
      | S m => (hd s) :: take m (tl s)
    end.

Lemma firstn_take : forall {A : Type} (n m: nat) (s : Stream A), n < m -> firstn n (take m s) = take n s.
Proof.
intros A n m s H.
revert s m H.
induction n.
- auto.
- intros s m H. simpl. destruct m; [easy |]. simpl. f_equal. apply IHn. lia.
Qed.

Lemma take_elim : forall {A : Type} (ls : list A) (n : nat) (s : Stream A), ls = take (S n) s -> firstn n ls = take n s.
Proof.
intros A ls n s H.
revert n H.
induction ls; intros n H.
- exfalso. now simpl in H.
- rewrite H. apply firstn_take. lia.
Qed.


Lemma Str_nth_0_hd : forall {A : Type} (s : Stream A), Str_nth 0 s = hd s.
Proof.
auto.
Qed.

Lemma Str_nth_S_tl : forall {A : Type} (s : Stream A) (n : nat), Str_nth (S n) s = Str_nth n (tl s).
Proof.
auto.
Qed.

(*
infinite two-player games on finite graphs
*)
Structure Arena A := mkArena 
{ positions : list A
; player_positions : A -> bool (* with decider partitioning holds trivially. Every non-player node is an opponent node. *)
; edges : list (A * A)
; positions_nodup : NoDup positions
; edges_between_positions : forall (p : A * A), In p edges -> In (fst p) positions /\ In (snd p) positions
; out_edges_positions : forall (p : A), In p positions -> exists v', In (p, v') edges (* every position has at least one outgoing edge *)
}.

Arguments mkArena {_} _ _ _ _ _.
Arguments positions {_} _.
Arguments player_positions {_} _. 
Arguments edges {_} _.

Section games.

Context {A : Type} (arena : Arena A) (winCon : Stream A -> Prop).

Definition play' (s : Stream A) : Prop := forall (n : nat), In (Str_nth n s, Str_nth (S n) s) (edges arena).

Lemma play'_elim : forall (s : Stream A), play' s -> (In ((hd s), (hd (tl s))) (edges arena)) /\ play' (tl s).
Proof.
intros s H. unfold play' in H. split.
- now specialize (H 0).
- unfold play'. intros n. destruct n.
+ specialize (H 1). unfold Str_nth in H. now unfold Str_nth.
+ specialize (H (S (S n))). unfold Str_nth in H. now unfold Str_nth.
Qed.


CoInductive play : Stream A -> Prop :=
  C_play : forall (v v' : A) (s : Stream A),
    In (v, v') (edges arena) -> play (Cons v' s) -> play (Cons v (Cons v' s)).

Lemma play_elim : forall (s : Stream A), play s -> (In ((hd s), (hd (tl s))) (edges arena)) /\ play (tl s).
Proof.
intros s H. destruct H. now split.
Qed.

Lemma play_play'_ext_eq : forall (s : Stream A), play' s <-> play s.
Proof.
intros s. split.
- revert s. cofix CoH. intros s H. destruct s as [s_hd s_tl]. destruct s_tl as [s_tl_hd s_tl_tl]. constructor.
{
    specialize (H 0). now cbn in H.
}
apply CoH.
now apply play'_elim in H as [H1 H2].
- intros H.
intros n. revert H. revert s. induction n.
{
    intros s H.
    apply play_elim in H. now destruct H.
}
intros s H.
apply play_elim in H as [H1 H2].
now apply IHn.
Qed.

Section strategies.

Context (player : bool) (f : list A -> A -> A).

Definition is_strategy : Prop := 
    forall (l : list A), (Forall (fun x => In x (positions arena)) l) -> 
    forall (v : A), ((player_positions arena) v = player) ->
    In (v, f l v) (edges arena).

Definition consistent_with (s : Stream A) : Prop :=  
    forall (n : nat), (player_positions arena) (Str_nth n s) = player -> f (take n s) (Str_nth n s) = Str_nth (S n) s.

Definition memoryless : Prop := is_strategy -> forall (l : list A) (v : A), f nil v = f l v.

Definition winningFrom (v : A) : Prop := 
    forall (s : Stream A), consistent_with s -> (v = hd s) -> winCon s.

End strategies.

(* Note that the strategies for different positions in the winning region may be different. *)
Definition winningRegion (player : bool) (pos : list A) : Prop :=  
    forall (v : A), In v pos -> 
    exists (f : list A -> A -> A), 
    winningFrom player f v.

Definition uniform_winning (player : bool) (f : list A -> A -> A) : Prop := 
    forall (w : list A), winningRegion player w -> forall (v : A), In v w -> winningFrom player f v.

(*
!!!!!!!!!!!!!
Folgende Lemma zeigen
!!!!!!!!!!!!!
*)

CoFixpoint play_for_strategies (ps os : list A -> A -> A) (memory : list A) (v : A) : Stream A :=
    if (player_positions arena v) 
    then Cons v (play_for_strategies ps os (memory ++ [v]) (ps memory v))
    else Cons v (play_for_strategies ps os (memory ++ [v]) (os memory v)).

Lemma play_for_strategies_spec : forall (ps os : list A -> A -> A) (memory : list A) (v : A) (s : Stream A), s = play_for_strategies ps os memory v ->
  (hd (play_for_strategies ps os memory v) = v) /\ 
  (if (player_positions arena v) 
  then (tl (play_for_strategies ps os memory v)) = (play_for_strategies ps os (memory ++ [v]) (ps memory v))
  else (tl (play_for_strategies ps os memory v)) = (play_for_strategies ps os (memory ++ [v]) (os memory v))).
Proof.
intros ps os memory v s H.
split.
- simpl. destruct (player_positions arena v); easy. 
- simpl. assert (exists b, player_positions arena v = b) as [b Hb].
{
    now eexists.
} 
rewrite Hb. destruct b; easy.
Qed.

Lemma play_for_strategies_unique : 
  forall (ps os : list A -> A -> A),
  is_strategy true ps -> is_strategy false os -> 
  forall (v : A),
  exists (s : Stream A), v = hd s -> play s -> 
  consistent_with true ps s -> consistent_with false os s ->
  forall (s' : Stream A), v = hd s' -> play s' -> 
  consistent_with true ps s' -> consistent_with false os s' ->
  EqSt s s'.
Proof.
intros ps os H_ps H_os v.
eexists (play_for_strategies ps os [] v).
assert (forall n, exists s v' ls, ls = take n (play_for_strategies ps os [] v) -> s = play_for_strategies ps os ls v').
{
    intros n. induction n.
    {
        eexists (play_for_strategies ps os [] v). eexists v. eexists []. easy.
    }
    destruct IHn as [s' [v'' [ls' IHn]]].
    eexists (tl s').
    assert (exists b, player_positions arena v'' = b) as [b Hb].
    {
        now eexists.
    }
    destruct b.
    {
        eexists (ps ls' v''). eexists (ls' ++ [Str_nth n s']).
        intros H.

    }
}
destruct H as [s Hs].
rewrite <- Hs.
intros H_v_s H_s H_ps_s H_os_s s'. 
revert H_v_s H_s H_ps_s H_os_s Hs.
revert v s s'.
cofix CoH.
intros v s s' H_v_s H_s H_ps_s H_os_s Hs H_v_s' H_s' H_ps_s' H_os_s'.
constructor.
- now rewrite H_v_s in H_v_s'.
- assert (exists b, player_positions arena v  = b) as [b Hb].
{
    now eexists.
}
destruct b.
{
    assert (exists v', v' = hd (tl s)) as [v' Hv'].
    {
        now eexists.
    }
    apply (CoH v' (tl s) (tl s')).
    + easy.
    + now apply play_elim in H_s as [H_s1 H_s2].
    + rewrite H_v_s in Hb. now apply consistent_with_elim in H_ps_s. 
    + apply consistent_with_elim in H_os_s. now destruct H_os_s.
    + rewrite Hs. rewrite Hv'. apply play_for_strategies_spec in Hs. rewrite Hb in Hs. destruct Hs.
    + admit.
    + admit.
    + admit.
    + admit.
}

assert (exists v', v' = os [] v) as [v' Hv'].
{
    now eexists.
}
apply (CoH v' (tl s) (tl s')).
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
Admitted.


Lemma both_player_strategies_unique_play : 
  forall (ps os : list A -> A -> A) (s s' : Stream A), 
  is_strategy true ps -> is_strategy false os -> play s ->
  consistent_with true ps s -> consistent_with false os s ->
  play s' ->
  consistent_with true ps s' -> consistent_with false os s' ->
  forall (v : A), v = hd s -> v = hd s' ->
  EqSt s s'.
Proof.
intros ps os. cofix CoH.
intros s s' H_ps H_os H_s H_p_s H_o_s H_s' H_p_s' H_o_s' v H_v_s H_v_s'. 
(*
unfold consistent_with in H_p_s. specialize (H_p_s H_ps H_s).
unfold consistent_with in H_o_s. specialize (H_o_s H_os H_s).
unfold consistent_with in H_p_s'. specialize (H_p_s' H_ps H_s').
unfold consistent_with in H_o_s'. specialize (H_o_s' H_os H_s').
*)
constructor.
- now rewrite H_v_s in H_v_s'.
- apply play_elim in H_s. destruct H_s as [H_s_1 H_s_2]. 
apply play_elim in H_s'. destruct H_s' as [H_s'_1 H_s'_2]. 
Abort.





(*
Note that the strategies   and   of the two players together uniquely
identify a specific play: |Plays(A,  , v) \ Plays(A,  , v)| = 1.
*)

(*
It is easy to see that no position can be in the winning regions of both players. Suppose
that there exists a position v and strategies   and   that are winning from v for Player 0
and 1, respectively. Then the unique play that is consistent with   and   would need to be
both in Win, because   is winning, and not in Win, because   is winning.
*)

Definition determined : Prop := forall (ps os : list A), winningRegion true ps -> winningRegion false os -> Permutation (positions arena) (ps ++ os).

End games.

