Require Import List.
Require Import ListDec.
Require Import Streams.
Require Import PeanoNat.
Require Import Permutation.
Require Import Lia.
Require Import Bool.
Require Import DecBool.

Require Import ListSet.

Import ListNotations.

Fixpoint take {A : Type} (n : nat) (s : Stream A) : list A :=
    match n with
      | O => nil
      | S m => (hd s) :: take m (tl s)
    end.

Lemma firstn_take : forall {A : Type} (n m: nat) (s : Stream A), 
  n < m -> 
  firstn n (take m s) = take n s.
Proof.
intros A n m s H.
revert s m H.
induction n.
- auto.
- intros s m H. simpl. 
destruct m; [easy |]. simpl. 
f_equal. apply IHn. lia.
Qed.

Lemma take_elim : forall {A : Type} (ls : list A) (n : nat) (s : Stream A), 
  ls = take (S n) s -> 
  firstn n ls = take n s /\ length ls = (S n).
Proof.
intros A ls n s H.
split.
{
revert n H.
induction ls; intros n H.
- exfalso. now simpl in H.
- rewrite H. apply firstn_take. lia.
}
rewrite H. clear H.
revert s. induction n; intros s.
+ easy.
+ destruct s. simpl. f_equal. 
specialize (IHn s). now rewrite <- IHn.
Qed.


Lemma eqst_takeeq : forall {A : Type} (n : nat) (s1 s2 : Stream A), 
  EqSt s1 s2 -> 
  take n s1 = take n s2.
Proof. 
induction n. 
- intros s1 s2 H. case H. easy.
- intros s1 s2 H. simpl.
case H. intros H_hd H_tl. f_equal; auto.
Qed.

Lemma takeeq_eqst : forall {A : Type} (s1 s2 : Stream A), 
  (forall (n : nat), take n s1 = take n s2) -> 
  EqSt s1 s2.
Proof.
cofix CoH. 
intros A s1 s2 H.
constructor.
- specialize (H 1). simpl in H. now inversion H.
- apply CoH. intros n. specialize (H (S n)). 
simpl in H. now inversion H.
Qed.

Lemma Str_nth_0_hd : forall {A : Type} (s : Stream A), 
  Str_nth 0 s = hd s.
Proof.
auto.
Qed.

Lemma Str_nth_S_tl : forall {A : Type} (s : Stream A) (n : nat), 
  Str_nth (S n) s = Str_nth n (tl s).
Proof.
auto.
Qed.

Lemma take_S : forall {A : Type} (n : nat) (s1 s2 : Stream A), 
  take (S n) s1 = take (S n) s2 -> 
  take n s1 = take n s2.
Proof.
intros A n. 
induction n; intros s1 s2 H.
- easy.
- simpl. f_equal.
+ now inversion H.
+ apply IHn. inversion H. simpl. now f_equal.
Qed.

Lemma take_elim_nth : forall {A : Type} (n : nat) (s : Stream A), 
  take (S n) s = take n s ++ [Str_nth n s].
Proof.
intros A n. induction n; intros s.
- simpl. now rewrite Str_nth_0_hd.
- assert (take (S (S n)) s = (hd s) :: take (S n) (tl s)) as H.
{
    easy.
}
rewrite H. rewrite (IHn (tl s)). simpl. now rewrite Str_nth_S_tl.
Qed.

Lemma take_eq : forall {A : Type} (n : nat) (s1 s2 : Stream A), 
  take n s1 = take n s2 -> 
  Str_nth n s1 = Str_nth n s2 -> 
  take (S n) s1 = take (S n) s2.
Proof.
intros A n s1 s2.
destruct n; intros H1 H2. 
- simpl. f_equal. rewrite Str_nth_0_hd in H2. now rewrite Str_nth_0_hd in H2.
- rewrite take_elim_nth. rewrite H1. rewrite H2. now rewrite <- take_elim_nth.
Qed.

Lemma filter_const_false {A : Type} (l : list A) : filter (fun _ => false) l = [].
Proof.
induction l; auto.
Qed.

Lemma set_in_map_iff: forall {A B : Type} (dec : forall x y : B, {x = y} + {x <> y}) (f : A -> B) (l : set A) (b : B), 
  set_In b (set_map dec f l) <-> 
  (exists a : A, f a = b /\ set_In a l).
Proof.
intros A B dec f l b.
split.
- intros H.
induction l.
+ now exfalso.
+ simpl in H. apply set_add_elim in H as [H | H].
{
    exists a. split; [now symmetry | now left]. 
}
specialize (IHl H). destruct IHl as [x [E H_x]].
exists x. split; [easy | now right].
- intros [a [E H]].
induction l.
{
    now exfalso.
}
simpl. apply set_add_intro. simpl in H. destruct H.
{
    left. congruence.
}
right. now apply IHl.
Qed.

Lemma set_map_eq_nil: forall {A B : Type} (dec : forall x y : B, {x = y} + {x <> y}) (f : A -> B) (l : set A), 
  set_map dec f l = [] -> 
  l = [].
Proof.
intros A B dec f l H.
destruct l.
- easy.
- now apply set_add_not_empty in H.
Qed.

Section Fun.

Context {X Y : Type} (f : nat -> Y) (P : X -> Y -> Prop).
Context (f_mon : forall i j, i <= j -> forall x, P x (f i) -> P x (f j)) (P_dec : forall x y, {P x y} + {not (P x y)}).

Lemma find (x : X) (n : nat) : 
  not (P x (f 0)) -> 
  P x (f n) -> 
  exists i, (not (P x (f i))) /\ P x (f (S i)).
Proof.
  induction n as [|n ?]; [|destruct (P_dec x (f n))]; eauto.
Qed.

End Fun.

(*
infinite two-player games on finite graphs
*)
Structure Arena A := mkArena 
{ positions : set A
; pos_is_set : NoDup positions
; player_positions : A -> bool (* with decider partitioning holds trivially. Every non-player node is an opponent node. *)
; edges : set (A * A)
; edges_is_set : NoDup edges
; edges_between_positions : forall (p : A * A), set_In p edges -> set_In (fst p) positions /\ set_In (snd p) positions
; out_edges_positions : forall (p : A), set_In p positions -> exists v', set_In (p, v') edges (* every position has at least one outgoing edge *)
}.

Arguments mkArena {_} _ _ _ _ _.
Arguments positions {_} _.
Arguments player_positions {_} _. 
Arguments edges {_} _.

Section games.

Context {A : Type} (arena : Arena A) (winCon : Stream A -> Prop).

Definition play' (s : Stream A) : Prop := forall (n : nat), 
  set_In (Str_nth n s, Str_nth (S n) s) (edges arena).

Lemma play'_elim : forall (s : Stream A), 
  play' s -> 
  (set_In ((hd s), (hd (tl s))) (edges arena)) /\ play' (tl s).
Proof.
intros s H. unfold play' in H. split.
- now specialize (H 0).
- unfold play'. intros n. destruct n.
+ specialize (H 1). unfold Str_nth in H. now unfold Str_nth.
+ specialize (H (S (S n))). unfold Str_nth in H. now unfold Str_nth.
Qed.


CoInductive play : Stream A -> Prop :=
  C_play : forall (v v' : A) (s : Stream A),
    set_In (v, v') (edges arena) -> play (Cons v' s) -> play (Cons v (Cons v' s)).

Lemma play_elim : forall (s : Stream A), 
  play s -> 
  (set_In ((hd s), (hd (tl s))) (edges arena)) /\ play (tl s).
Proof.
intros s H. destruct H. now split.
Qed.

Lemma play_play'_ext_eq : forall (s : Stream A), 
  play' s <-> 
  play s.
Proof.
intros s. split.
- revert s. cofix CoH. intros s H. destruct s as [s_hd s_tl]. 
destruct s_tl as [s_tl_hd s_tl_tl]. constructor.
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

(*
l noch zu allgemein, muss wahrscheinlich auf "konsistent" memories eingeschränkt werden
*)
Definition is_strategy : Prop := 
    forall (l : list A), 
    (Forall (fun x => set_In x (positions arena)) l) -> 
    forall (v : A), 
    (In v (positions arena)) -> 
    ((player_positions arena) v = player) ->
    set_In (v, f l v) (edges arena).

Definition consistent_with (s : Stream A) : Prop :=  
  forall (n : nat), 
  (player_positions arena) (Str_nth n s) = player -> 
  f (take n s) (Str_nth n s) = Str_nth (S n) s.

Definition memoryless : Prop := forall (l : list A) (v : A), f nil v = f l v.

Definition winningFrom (v : A) : Prop := 
  forall (s : Stream A), 
  play s -> 
  consistent_with s -> 
  (v = hd s) ->
  winCon s.

End strategies.

(* Note that the strategies for different positions in the winning region may be different. *)
(* Falsch: *)
Definition winningRegion' (player : bool) (pos : set A) : Prop :=  
  forall (v : A), 
  set_In v pos -> 
  exists (f : list A -> A -> A), 
  winningFrom player f v.

Definition winningRegion (player : bool) (pos : set A) : Prop :=  
    forall (v : A), 
    set_In v (positions arena) ->
    (exists (f : list A -> A -> A), winningFrom player f v) -> 
    set_In v pos.    

Definition uniform_winning (player : bool) (f : list A -> A -> A) : Prop := 
    forall (w : set A), 
    winningRegion player w -> 
    forall (v : A), 
    set_In v w -> 
    winningFrom player f v.

(*
Note that the strategies   and   of the two players together uniquely
identify a specific play: |Plays(A,  , v) \ Plays(A,  , v)| = 1.
*)

CoFixpoint play_for_strategies (ps os : list A -> A -> A) (memory : list A) (v : A) : Stream A :=
    if (player_positions arena v) 
    then Cons v (play_for_strategies ps os (memory ++ [v]) (ps memory v))
    else Cons v (play_for_strategies ps os (memory ++ [v]) (os memory v)).

Lemma play_for_strategies_unique : 
  forall (ps os : list A -> A -> A),
  forall (v : A),
  forall (s : Stream A), 
  v = hd s ->
  consistent_with true ps s ->
  consistent_with false os s ->
  forall (s' : Stream A), 
  v = hd s' -> 
  consistent_with true ps s' -> consistent_with false os s' ->
  EqSt s s'.
Proof.
intros ps os.
intros v s H_v_s H_ps_s H_os_s. 
intros s' H_v_s' H_ps_s' H_os_s'.
apply takeeq_eqst.
induction n.
- easy. 
- rewrite take_elim_nth. rewrite take_elim_nth. f_equal; [easy | f_equal]. 
destruct n.
+ rewrite Str_nth_0_hd. rewrite Str_nth_0_hd. now rewrite <- H_v_s.
+ rewrite take_elim_nth in IHn. rewrite take_elim_nth in IHn. apply app_inj_tail_iff in IHn.
destruct IHn as [H1 H2].
assert (exists b, player_positions arena (Str_nth n s) = b) as [b Hb].
{
    now eexists.
}
destruct b.
{
    rewrite <- (H_ps_s n Hb). rewrite H2 in Hb. rewrite <- (H_ps_s' n Hb). now f_equal.
}
rewrite <- (H_os_s n Hb). rewrite H2 in Hb. rewrite <- (H_os_s' n Hb). now f_equal.
Qed.


Lemma play_for_strategies_unique_strong : 
  forall (ps os : list A -> A -> A),
  forall (v : A),
  exists (s : Stream A), 
  v = hd s -> 
  consistent_with true ps s -> 
  consistent_with false os s ->
  forall (s' : Stream A), 
  v = hd s' ->
  consistent_with true ps s' -> 
  consistent_with false os s' ->
  EqSt s s'.
Proof.
intros ps os v.
eexists (play_for_strategies ps os [] v).
intros H_v_s H_ps_s H_os_s.
intros s' H_v_s' H_ps_s' H_os_s'.
apply takeeq_eqst.
induction n.
- easy.
- rewrite take_elim_nth. rewrite take_elim_nth. f_equal; [easy | f_equal]. 
destruct n.
+ rewrite Str_nth_0_hd. rewrite Str_nth_0_hd. now rewrite <- H_v_s.
+ rewrite take_elim_nth in IHn. rewrite take_elim_nth in IHn. apply app_inj_tail_iff in IHn.
destruct IHn as [H1 H2].
assert (exists b, player_positions arena (Str_nth n s') = b) as [b Hb].
{
    now eexists.
}
destruct b.
{
    rewrite <- (H_ps_s' n Hb). rewrite <- H2 in Hb. rewrite <- (H_ps_s n Hb). now f_equal.
}
rewrite <- (H_os_s' n Hb). rewrite <- H2 in Hb. rewrite <- (H_os_s n Hb). now f_equal.
Qed.

(*
It is easy to see that no position can be in the winning regions of both players. Suppose
that there exists a position v and strategies   and   that are winning from v for Player 0
and 1, respectively. Then the unique play that is consistent with   and   would need to be
both in Win, because   is winning, and not in Win, because   is winning.
*)

(* We use concatenation here, because we need a decider for set_union and because the winning regions of both players have to be disjoint *)
Definition determined : Prop := forall (ps os : set A), 
  winningRegion true ps -> 
  winningRegion false os -> 
  Permutation (positions arena) (ps ++ os).

End games.

Section reachability_games.
Context {A : Type} (carrier_dec : forall x y : A, {x = y} + {x <> y}) (arena : Arena A) (reach : set A) (reach_pos : incl reach (positions arena)).

Inductive winCon : Stream A -> Prop := 
  | reach_hd : forall (s : Stream A), set_In (hd s) reach -> winCon s
  | reach_tl : forall (p : A) (s : Stream A), winCon s -> winCon (Cons p s).

Definition carrier_eqb (x y : A) : bool :=
    match carrier_dec x y with
      | left _ => true
      | right _ => false
    end.

Lemma carrier_eqb_refl : forall (x : A), 
  carrier_eqb x x = true.
Proof.
intros x.
unfold carrier_eqb. now destruct (carrier_dec x x).
Qed.

Definition edge_dec : forall x y : A * A, {x = y} + {x <> y}.
Proof.
decide equality. 
Defined.

Section fix_player.
Context (player : bool).

Definition cpre (r' : set A) : set A :=
    match r' with
    | nil => nil
    | r => let r_pl := filter (fun x => Bool.eqb (player_positions arena x) player) (positions arena) in
           let r_op := filter (fun x => negb (Bool.eqb (player_positions arena x) player)) (positions arena) in
           let e_in := filter (fun e => set_mem carrier_dec (snd e) r) (edges arena) in
           set_union carrier_dec
           (set_map carrier_dec fst (filter (fun e => set_mem carrier_dec (fst e) r_pl) e_in)) 
           (filter (fun v => forallb (fun x => set_mem edge_dec x e_in) (filter (fun e => carrier_eqb (fst e) v) (edges arena))) r_op)
    end.

Lemma cpre_nil : cpre [] = [].
Proof.
easy.
Qed.

Lemma cpre_ran (l : set A): incl (cpre l) (positions arena).
Proof.
intros x H.
destruct l.
- now rewrite cpre_nil in H. 
- simpl in H. apply set_union_elim in H. destruct H.
{ 
    enough (forall ps : list (A * A), incl ps (edges arena) -> In x (set_map carrier_dec fst ps) -> In x (positions arena)).
    {
        specialize (H0 ((filter (fun e : A * A => set_mem carrier_dec (fst e) (filter (fun x : A => Bool.eqb (player_positions arena x) player) (positions arena)))
        (filter (fun e : A * A => if carrier_dec (snd e) a then true else set_mem carrier_dec (snd e) l) (edges arena))))).
        apply H0.
        {
            intros p H_p. Search In filter. apply filter_In in H_p as [H_p _]. now apply filter_In in H_p as [H_p _].
        }
        exact H.
    }
    clear H.
    intros ps H1 H2.
    apply set_in_map_iff in H2.
    destruct H2 as [p [E H]].
    rewrite <- E. apply H1 in H. now apply (edges_between_positions) in H.
}
apply filter_In in H. destruct H as [H _]. now apply filter_In in H. 
Qed.



Lemma cpre_elim (a : A) (l : set A): 
  incl 
  (cpre (a :: l)) 
  (set_union carrier_dec (set_map carrier_dec fst (filter (fun x => carrier_eqb a (snd x)) (edges arena))) (cpre l)).
Proof.
intros x H.
destruct (Bool.eqb (player_positions arena x) player) eqn: Hb;
apply set_union_elim in H as [H | H].
{
    apply set_in_map_iff in H as [p [E H]].
    apply filter_In in H as [H Hpos].
    destruct (In_dec edge_dec (x,a) (edges arena)).
    {
        apply set_union_intro1.
        apply set_in_map_iff. exists (x,a).
        split; auto. apply filter_In. split; auto.
        simpl. apply carrier_eqb_refl.    
    }
    apply set_union_intro2.
    assert (In (snd p) l) as H2.
    {
        apply filter_In in H as [Hp H].
        apply set_mem_correct1 in H.
        destruct H as [E2 | H].
        {
            assert (p = (x,a)).
            {
                rewrite <- E. rewrite E2. apply surjective_pairing.
            }
            exfalso. congruence.
        }
        easy.
    }
    destruct l.
    {
        now exfalso.
    }
    apply set_union_intro1. apply set_in_map_iff.
    exists p. split; auto.
    apply filter_In. split. 
    {
        apply filter_In. apply filter_In in H as [Hp H].
        split; auto. apply set_mem_correct2.
        apply set_mem_correct1 in H.
        destruct H as [Hf | H].
        {
            exfalso. 
            assert (p = (x,a)).
            {
                rewrite <- E. rewrite Hf. apply surjective_pairing.
            }
            congruence.
        }
        easy.
    }
    easy.
}
{
    exfalso.
    apply filter_In in H as [H1 H2].
    apply filter_In in H1 as [H1 E].
    now rewrite Hb in E.
}
{
    exfalso.
    apply set_in_map_iff in H. destruct H as [p [E H]].
    apply filter_In in H as [H1 H2].
    apply set_mem_correct1 in H2. apply filter_In in H2 as [H2 H3].
    congruence.
}
apply filter_In in H as [Hpos H].
destruct (In_dec edge_dec (x,a) (edges arena)) as [He | He].
{
    apply set_union_intro1.
    apply set_in_map_iff. exists (x,a).
    split; auto. apply filter_In. split; auto.
    simpl. apply carrier_eqb_refl.    
}
apply set_union_intro2.
apply filter_In in Hpos as [Hpos Hb2].
assert (forallb
(fun x : A * A =>
 set_mem edge_dec x
   (filter (fun e : A * A => set_mem carrier_dec (snd e) l)
      (edges arena)))
(filter (fun e : A * A => carrier_eqb (fst e) x) (edges arena)) = true) as H1.
{
    apply forallb_forall. intros p Hp.
    apply set_mem_correct2. apply filter_In. split.
    {
        now apply filter_In in Hp.
    }
    apply set_mem_correct2.
    apply forallb_forall with (x := p) in H.
    {
        apply set_mem_correct1 in H. apply filter_In in H as [H1 H2].
        apply set_mem_correct1 in H2 as [Hf | H].
        {
            exfalso. 
            apply filter_In in Hp as [_ E].
            assert (p = (x,a)).
            {
                unfold carrier_eqb in E. destruct (carrier_dec (fst p) x).
                {
                    rewrite <- e. rewrite Hf. apply surjective_pairing.
                }
                easy.
            }
            congruence.   
        }
        easy.
    }
    easy.
}
clear H.
destruct l eqn: H.
{
    exfalso. 
    simpl in H1. rewrite filter_const_false in H1. 
    simpl in H1. 
    destruct (filter (fun e : A * A => carrier_eqb (fst e) x) (edges arena)) eqn: H2.
    {
        apply out_edges_positions in Hpos as [v H3].
        assert (In (x, v) (filter (fun e : A * A => carrier_eqb (fst e) x) (edges arena))) as Hf.
        {
            apply filter_In. simpl. now rewrite carrier_eqb_refl.
        }
        now rewrite H2 in Hf.
    }
    easy.
}
destruct (In_dec edge_dec (x,a0) (edges arena)) as [He2 | He2].
{
    apply set_union_intro2. apply filter_In.
    split; auto. now apply filter_In.
}
apply set_union_intro2.
apply filter_In. split; auto.
now apply filter_In.
Qed.


Lemma cpre_nodup (s : set A) : 
  NoDup s ->
  NoDup (cpre s).
Proof.
intros H.
induction s.
{
    now rewrite cpre_nil.
}
apply set_union_nodup. 
{
    enough (forall ps : set (A * A), NoDup ps -> NoDup (set_map carrier_dec fst ps)).
    {
        apply H0.
        repeat (apply NoDup_filter). apply edges_is_set.
    }
    intros ps Hps.
    unfold set_map. unfold set_fold_right.
    induction ps.
    {
        apply NoDup_nil.
    }
    apply set_add_nodup. apply IHps.
    now apply NoDup_cons_iff in Hps as [_ Hps].
}
repeat (apply NoDup_filter). apply pos_is_set.
Qed.

Lemma cpre_monotonicity (l1 l2 : set A) : 
  incl l1 l2 -> 
  incl (cpre l1) (cpre l2).
Proof.
revert l1. destruct l2; destruct l1.
- intros H. now rewrite !cpre_nil.
- intros H x H_x. exfalso. now apply incl_l_nil in H.
- intros H x H_x. exfalso. now rewrite cpre_nil in H_x.
- intros H. 
intros x H_x. 
apply set_union_intro.
destruct (Bool.eqb (player_positions arena x) player) eqn: Hb.
{
    left. simpl in H_x. apply set_union_elim in H_x as [Hx | Hx].
    {
        apply set_in_map_iff in Hx as [p [E1 Hp]].
        apply filter_In in Hp as [Hp Hpos]. apply filter_In in Hp as [Hp Hd].
        apply set_in_map_iff. exists p. split; auto. apply filter_In. split.
        {
            apply filter_In. split; auto. apply set_mem_correct2.
            specialize (H (snd p)). apply H.
            destruct (carrier_dec (snd p) a0).
            {
                simpl. now left. 
            }
            simpl. right. now apply set_mem_correct1 in Hd.
        }
        easy.
    }
    exfalso.
    apply filter_In in Hx as [Hpos Hx]. apply filter_In in Hpos as [Hpos Hf].
    now rewrite Hb in Hf.
}
right.
apply filter_In. split.
{
    apply filter_In. split.
    {
        now apply cpre_ran in H_x.
    }
    now rewrite Hb.
}
apply forallb_forall. intros p Hp.
apply set_mem_correct2. apply filter_In. split.
{
    now apply filter_In in Hp as [Hp _].
}
apply set_mem_correct2. 
apply set_union_elim in H_x as [Hx | Hx].
{
    exfalso.
    apply set_in_map_iff in Hx as [p' [E1 Hp']].
    apply filter_In in Hp' as [_ Hf]. apply set_mem_correct1 in Hf. 
    apply filter_In in Hf as [Hpos Hf]. congruence.
}
apply filter_In in Hx as [Hpos Hx]. 
destruct (filter (fun e : A * A => carrier_eqb (fst e) x) (edges arena)).
{
    now exfalso.
}
apply forallb_filter_id in Hx. rewrite <- Hx in Hp.
apply filter_In in Hp as [_ Hp]. apply set_mem_correct1 in Hp. apply filter_In in Hp as [_ Hp].
apply set_mem_correct1 in Hp. now apply H.
Qed.

Fixpoint attractor (n : nat) (r : set A) : set A :=
    match n with
      | O => r
      | S m => let attr := attractor m r in set_union carrier_dec attr (cpre attr)
    end.

Lemma attractor_monotonicity_index : forall i j : nat, 
  i <= j -> 
  incl (attractor i reach) (attractor j reach).
Proof.
induction i.
- intros j H x Hx. induction j; [easy | apply set_union_intro1; apply IHj; lia].
- intros j H x Hx. destruct j.
{
    now exfalso.
}
apply set_union_elim in Hx as [Hx | Hx].
{
    apply IHi; [lia | easy].
}
apply set_union_intro2. revert x Hx.
apply cpre_monotonicity. apply IHi. lia.
Qed.

Lemma attractor_monotonicity (n : nat) (r : set A) : incl r (attractor n r).
Proof.
intros a H.
induction n.
{
    easy.
} 
apply set_union_intro; auto.
Qed.

Lemma attractor_ran (n : nat) (l : set A) : 
  incl l (positions arena) -> 
  incl (attractor n l) (positions arena).
Proof.
intros H x H_x.
induction n.
- specialize (H x). now apply H in H_x.
- simpl in H_x. apply set_union_elim in H_x. destruct H_x as [H1 | H1]; auto.
now apply cpre_ran with (l := (attractor n l)).
Qed.

Lemma attractor_nil (n : nat) : attractor n [] = [].
Proof.
induction n. 
- easy.
- simpl. rewrite IHn. now rewrite cpre_nil.
Qed.


Fixpoint attractor' (n : nat) (r : set A) : set A :=
    match n with
    | O => r
    | S m => attractor' m (set_union carrier_dec r (cpre r))
    end.

Lemma attractor_attractor' : forall n l, 
  (attractor n l) = (attractor' n l).
Proof.
  intros n. induction n as [|n IH].
  - easy.
  - intros l. unfold attractor. fold attractor. rewrite IH.
   clear IH. revert l. induction n as [|n IH].
        + easy.
        + intros l. apply IH.
Qed.

Lemma attractor'_monotonicity (n : nat) : forall (l1 l2 : set A), 
  incl l1 l2 -> 
  incl (attractor' n l1) (attractor' n l2).
Proof.
induction n as [|n IH].
- easy.
- intros l1 l2 H. apply IH. intros x H_x.
apply set_union_elim in H_x. destruct H_x.
{
    apply H in H0. now apply set_union_intro1.
}
apply cpre_monotonicity with (l2 := l2) in H0; auto. now apply set_union_intro2.
Qed.

Lemma attractor_nodup (n : nat) (r : set A) : 
  NoDup r -> 
  NoDup (attractor n r).
Proof.
revert r. induction n; intros r H.
{
    easy.
}
apply set_union_nodup.
{
    now apply IHn.
}
apply cpre_nodup. now apply IHn.
Qed.

Lemma attractor_terminates : forall (r : set A), 
  NoDup r -> 
  incl r (positions arena) -> 
  exists (n : nat), 
  (n <= (length (positions arena))) /\ Permutation (attractor n r) (attractor (S n) r).
Proof.
intros r H_nodup H_r.
exists (length (positions arena)).
split.
{
    lia.
}
apply NoDup_Permutation.
- induction (length (positions arena)); auto. simpl. apply set_union_nodup. 
{
    easy.
} 
now apply cpre_nodup. 
- induction (length (positions arena)); auto. simpl. apply set_union_nodup. 
{
    easy.
} 
{
    now apply cpre_nodup.
}
now apply attractor_nodup.
- intros x. split; intros H.
+ destruct (length (positions arena)); now apply set_union_intro1.
+ rewrite attractor_attractor' in *.  revert r H_nodup H_r x H. 
enough (forall (t r : set A), incl (positions arena) (set_union carrier_dec t r) -> NoDup r -> incl r (positions arena) -> incl (attractor' (S (length t)) r) (attractor' (length t) r)) as Hi. 
{
    intros r. apply Hi. intros a Ha. now apply set_union_intro1.
}
intros t.
induction t as [t IH] using (Nat.measure_induction _ (@length A)).
intros r H_t H_nodup H_r.
destruct (Exists_dec (fun x => In x t) (cpre r)) as [H|H].
{
    intros. now apply (in_dec carrier_dec).
}
{
    apply Exists_exists in H. destruct H as [x [H1 H2]]. apply in_split in H2. destruct H2 as [t1 [t2 H2]].
    subst t. rewrite (Add_length (Add_app x t1 t2)).
    apply IH.
    {
        rewrite !app_length. cbn. lia.
    }
    { 
        intros y H_y%H_t. apply set_union_elim in H_y. apply set_union_intro. 
        destruct H_y.
        {
            apply in_app_iff in H. destruct H as [H | H].
            {
                left. apply in_app_iff. now left.
            }
            destruct H.
            {
                right. apply set_union_intro2. now rewrite <- H.
            }
            left. apply in_app_iff. now right.
        }
        right. apply set_union_intro. now left.
    }
    {
        apply set_union_nodup; auto. now apply cpre_nodup.
    }
    intros a H_a. apply set_union_elim in H_a. destruct H_a.
    {
        now apply H_r in H.
    }
    now apply cpre_ran in H.
}
simpl.
apply attractor'_monotonicity.
intros x H_x. apply set_union_elim in H_x.
destruct H_x as [H_x | H_x]; [easy | ].
apply Forall_Exists_neg in H.
eapply Forall_forall in H; [|eassumption].
apply cpre_ran in H_x.
apply H_t in H_x.
apply set_union_elim in H_x as [|]; [now exfalso | easy].
Qed.

Fixpoint find_smaller_attractor (v : A) (n : nat) : nat :=
    match In_dec carrier_dec v (attractor n reach) with
    | left _ => match n with
                |  O => O
                |  S m => find_smaller_attractor v m
                end
    |  right _ => n
    end.

Lemma find_smaller_lower_bound (v : A) (n : nat) : find_smaller_attractor v n <= n.
Proof.
induction n.
- simpl. now destruct In_dec.
- simpl. destruct In_dec.
{
    now apply Nat.le_le_succ_r.
}
easy.
Qed.

Definition sigma (_ : list A) (v : A) : A :=
    let attr := attractor ((find_smaller_attractor v (length (positions arena)))) reach in
    if (Bool.eqb ((player_positions arena) v) player)
    then let succs := set_map carrier_dec snd (filter (fun p => carrier_eqb (fst p) v) (edges arena)) in 
      match (set_inter carrier_dec succs attr) with
      | nil => List.hd v succs
      | (v' :: vs) => v'
      end
    else v.


Lemma sigma_memoryless : memoryless sigma.
Proof.
easy.
Qed.

Lemma sigma_strategy : is_strategy arena player sigma.
Proof.
intros l Hl v Hv Hb.
rewrite <- sigma_memoryless.
unfold sigma. rewrite Hb. rewrite Bool.eqb_reflx. apply out_edges_positions in Hv as [v' He].
assert (In v' (set_map carrier_dec snd (filter (fun p : A * A => carrier_eqb (fst p) v) (edges arena)))) as H2.
{
    apply set_in_map_iff. exists (v,v'). split; auto.
    apply filter_In. now rewrite carrier_eqb_refl.
}
destruct (set_map carrier_dec snd (filter (fun p : A * A => carrier_eqb (fst p) v) (edges arena))) eqn: Hv.
{
    now exfalso.
}
destruct (set_inter carrier_dec (a :: s) (attractor (find_smaller_attractor v (length (positions arena))) reach)) eqn: Hi.
{
    assert (In a (set_map carrier_dec snd (filter (fun p : A * A => carrier_eqb (fst p) v) (edges arena)))).
    {
        rewrite Hv. simpl. now left.
    }
    apply set_in_map_iff in H as [p [E2 Hp]]. apply filter_In in Hp as [Hp H1].
    unfold carrier_eqb in H1. destruct (carrier_dec (fst p) v) as [E1 | E1].
    {
        rewrite <- E1. rewrite <- E2. now rewrite <- surjective_pairing.
    }
    now exfalso.
}
assert (In a0 (set_inter carrier_dec (a :: s) (attractor (find_smaller_attractor v (length (positions arena))) reach))).
{
    rewrite Hi. simpl. now left.
}
apply set_inter_elim in H as [H _].
rewrite <- Hv in H.
apply set_in_map_iff in H as [p [E2 H]]. apply filter_In in H as [H E1].
rewrite <- E2. unfold carrier_eqb in E1. destruct (carrier_dec (fst p) v).
{
    rewrite <- e. now rewrite <- surjective_pairing.
}
now exfalso.
Qed.

Lemma added_to_attractor (p : A) (n : nat) : 
  not (In p reach) -> 
  In p (attractor n reach) -> 
  exists i, 
  (not (In p (attractor i reach))) /\ In p (attractor (S i) reach).
Proof.
apply (find (fun n => attractor n reach) (fun x y => In x y) attractor_monotonicity_index (In_dec carrier_dec)).
Qed.

Lemma attr_find_smaller (p : A) (n : nat) : 
  In p (attractor (S n) reach) <-> 
  find_smaller_attractor p (S n) = find_smaller_attractor p n.
Proof.
split.
{
    intros H.
    destruct n; now apply ifdec_left.
}
destruct n; intros E.
- simpl in E. destruct (In_dec carrier_dec p reach) as [H1 | H1].
{
    now apply set_union_intro1.
}
destruct (In_dec carrier_dec p (set_union carrier_dec reach (cpre reach))) as [H2 | H2].
{
    apply set_union_elim in H2 as [H2 | H2].
    {
        now exfalso.
    }
    now apply set_union_intro2.
}
exfalso. lia.
- unfold find_smaller_attractor in E. destruct (In_dec carrier_dec p (attractor (S (S n)) reach)) as [H1 | H1].
{
    easy.
}
exfalso. destruct (In_dec carrier_dec p (attractor (S n) reach)) as [H2 | H2].
{
    apply attractor_monotonicity_index with (j := S (S n)) in H2; [easy | lia].
}
lia.
Qed.

Lemma attr_find_smaller' (p : A) (n m k : nat) : 
  find_smaller_attractor p n = m -> 
  n <= k -> 
  find_smaller_attractor p k = m.
Proof.
Admitted.

Lemma added_to_attractor' (p : A) (n : nat) : 
  not (In p reach) -> 
  In p (attractor n reach) -> 
  (not (In p (attractor (find_smaller_attractor p n) reach))) /\ In p (attractor (S (find_smaller_attractor p n)) reach).
Proof.
induction n; intros Hr Hp.
{
    easy.
}
destruct (In_dec carrier_dec p (attractor n reach)) as [H | H].
{
    apply attr_find_smaller in Hp. rewrite Hp. now apply IHn.
}
enough ((find_smaller_attractor p (S n)) = n) as H1.
{
    now rewrite H1.
}
unfold find_smaller_attractor. destruct In_dec; [| easy].
{
    destruct n.
    {
        now destruct In_dec.
    }
    now destruct In_dec.
}
Qed.

Lemma sigma_attractor_pred (v : A) (n : nat) : 
  In v (positions arena) -> 
  In v (attractor (S n) reach) -> 
  not (In v (attractor n reach)) -> 
  eqb (player_positions arena v) player = true -> 
  In (sigma [] v) (attractor n reach). 
Proof.
intros Hv Hs H Hb.
unfold attractor in Hs.
fold (attractor n reach) in Hs.
apply set_union_elim in Hs as [Hs | Hs].
{
    now exfalso.
}
destruct (attractor n reach) eqn: Ea.
{
    now exfalso.
}
apply set_union_elim in Hs as [Hs | Hs].
{
    rewrite <- Ea in *.
    apply set_in_map_iff in Hs as [p [Hp1 Hp2]].
    apply filter_In in Hp2 as [Hp2 _].
    apply filter_In in Hp2 as [Hp Hp2].
    apply set_mem_correct1 in Hp2.
    assert (find_smaller_attractor v (length (positions arena)) = n) as El.
    {
        admit.
    }
    unfold sigma.
    rewrite Hb, El.
    apply (set_inter_iff carrier_dec _ (set_map carrier_dec snd (filter (fun p => carrier_eqb (fst p) v) (edges arena)))).
    destruct (set_inter _ _ _) eqn:E.
    {
        exfalso.
        assert (In (snd p) (set_inter carrier_dec (set_map carrier_dec snd (filter (fun p : A * A => carrier_eqb (fst p) v) (edges arena))) (attractor n reach))) as Hf.
        {
            apply set_inter_intro.
            {
                apply set_in_map_iff. exists p. split; auto.
                apply filter_In. rewrite Hp1. now rewrite carrier_eqb_refl.
                }
                easy.
        }
        now rewrite E in Hf.
    }
    now left.
}
exfalso.
apply filter_In in Hs as [Hs _].
apply filter_In in Hs as [_ Hs].
now rewrite Hb in Hs.
Admitted.

Lemma attractor_winning_region (pos : set A) : 
  winningRegion arena winCon player pos <-> 
  (incl pos (attractor (length (positions arena)) reach) /\ incl (attractor (length (positions arena)) reach) pos).
Proof.
split.
{
    intros Hw.
    unfold winningRegion in Hw.
    admit.
}
intros [H1 H2] v Hv [f Hf].
unfold winningFrom in Hf.
apply H2.


Lemma attractor_winning_region' : winningRegion' arena winCon player (attractor (length (positions arena)) reach).
Proof.
unfold winningRegion.
intros v Hv.
exists sigma.
destruct (In_dec carrier_dec v reach) as [Hr | Hr].
{
    intros s Hp Hc Ev.
    apply reach_hd. now rewrite <- Ev.
}
apply (added_to_attractor' v (length (positions arena)) Hr) in Hv as [Hnm Hm]. 
assert (exists m, m = find_smaller_attractor v (length (positions arena))) as [m Em].
{
    now eexists.
}
revert v Hr Em Hnm Hm.
induction m.
{
    intros v Hv Em Hnm Hm s Hp Hc Ev.
    rewrite <- Em in *.
    destruct s. apply reach_tl. apply reach_hd.
    apply play_play'_ext_eq in Hp. 
    specialize (Hp 0). rewrite Str_nth_S_tl in Hp. rewrite !Str_nth_0_hd in Hp. simpl in Hp. 
    specialize (Hc 0). rewrite Str_nth_S_tl in Hc. rewrite !Str_nth_0_hd in Hc. simpl in Hc.
    simpl in Ev. rewrite <- Ev in *.
    destruct (Bool.eqb (player_positions arena v) player) eqn: Hb.
    {
        rewrite <- Hc in *; try now apply Bool.eqb_prop in Hb.
        enough (In (sigma [] v) (attractor 0 reach)).
        {
            easy.
        }
        apply sigma_attractor_pred; auto.
        now apply edges_between_positions in Hp.
    }
    apply set_union_elim in Hm as [H1 | H1].
    {
        now exfalso.
    }
    destruct reach eqn: Hr.
    {
        exfalso. now rewrite cpre_nil in H1.
    }
    apply set_union_elim in H1 as [H1 | H1].
    {
        exfalso.
        apply set_in_map_iff in H1 as [p [H1 H2]].
        apply filter_In in H2 as [_ H2]. rewrite H1 in H2.
        apply set_mem_correct1 in H2. apply filter_In in H2 as [_ H2]. congruence.
    }
    rewrite <- Hr in *.
    apply filter_In in H1 as [_ H1].
    apply forallb_forall with (x := (v, hd s)) in H1.
    {
        apply set_mem_correct1 in H1.
        apply filter_In in H1 as [_ H1].
        now apply set_mem_correct1 in H1.
    }
    apply filter_In. simpl. now rewrite carrier_eqb_refl.
}
intros v Hv Em Hnm Hm.
intros s. destruct s. intros Hp Hc Ev.
simpl in Ev. rewrite <- Ev in *. clear Ev. rewrite <- Em in *.
apply reach_tl.
apply (IHm (hd s)).
{
    (* aus Hnm und Hm sollte man schließen können, 
    dass mindestens zwei Schritte in Reach benötigt werden. 
    Da (hd s) einem Schritt entspricht, kann es nicht in Reach sein. *)
    apply play_play'_ext_eq in Hp. 
    specialize (Hp 0). rewrite Str_nth_S_tl in Hp. rewrite !Str_nth_0_hd in Hp. simpl in Hp. 
    specialize (Hc 0). rewrite Str_nth_S_tl in Hc. rewrite !Str_nth_0_hd in Hc. simpl in Hc.
    destruct (Bool.eqb (player_positions arena v) player) eqn: Hb.
    {
        rewrite <- Hc in *; try now apply Bool.eqb_prop in Hb.
        admit.
    }
    admit.
}
{
    (* sollte aus der Attractor-Definition folgen ?! *)
    admit.
}
{
    (* sollte ebenfalls aus Hnm und Hm folgen *)
    admit.
}
{
    (* Hm := In (hd (Cons v s)) attractor (S (S m)) => In (hd s) attractor (S m)
    Die Anzahl an benötigten Schritten muss also mit jedem tl Aufruf kleiner werden... gut!*)
    admit.
}
{
    apply play_play'_ext_eq. apply play_play'_ext_eq in Hp. 
    intros x.
    now specialize (Hp (S x)). 
}
{
    unfold consistent_with in Hc.
    intros x. now specialize (Hc (S x)).
}
easy.
Admitted.


Lemma attractor_winning_region'' : winningRegion' arena winCon player (attractor (length (positions arena)) reach).
Proof.
unfold winningRegion.
intros v Hv.
exists sigma.
destruct (In_dec carrier_dec v reach) as [Hr | Hr].
{
    intros s Hp Hc Ev.
    apply reach_hd. now rewrite <- Ev.
}
apply (added_to_attractor' v (length (positions arena)) Hr) in Hv as [Hnm Hm]. 
assert (exists m, m = find_smaller_attractor v (length (positions arena))) as [m Em].
{
    now eexists.
}
revert v Hr Em Hnm Hm.
induction m.
{
    intros v Hv Em _ H1 s Hp Hc Ev.
    rewrite <- Em in *.
    destruct s. apply reach_tl. apply reach_hd.
    apply set_union_elim in H1 as [H1 | H1].
    {
        now exfalso.
    }
    destruct reach eqn: Hr.
    {
        exfalso. now rewrite cpre_nil in H1.
    }
    destruct (Bool.eqb (player_positions arena v) player) eqn: Hb; apply set_union_elim in H1 as [H1 | H1].
    {
        rewrite <- Hr in *.
        apply play_play'_ext_eq in Hp. 
        specialize (Hp 0). rewrite Str_nth_S_tl in Hp. rewrite !Str_nth_0_hd in Hp. simpl in Hp. 
        specialize (Hc 0). rewrite Str_nth_S_tl in Hc. rewrite !Str_nth_0_hd in Hc. simpl in Hc.
        simpl in Ev. rewrite <- Ev in *.
        rewrite <- Hc in *; try now apply Bool.eqb_prop in Hb.
        unfold sigma. rewrite Hb.
        rewrite <- Em.
        destruct set_inter eqn: Ei.
        {
            exfalso. 
            apply set_in_map_iff in H1 as [p [H1 H2]].
            apply filter_In in H2 as [H2 _].
            apply filter_In in H2 as [H2 H3].
            assert (In (snd p) (set_inter carrier_dec (set_map carrier_dec snd (filter (fun p : A * A => carrier_eqb (fst p) v) (edges arena))) (attractor 0 reach))).
            {
                apply set_inter_intro.
                {
                    apply set_in_map_iff. exists p. split; try easy.
                    apply filter_In. rewrite H1. split; try easy. apply carrier_eqb_refl.
                }
                now apply set_mem_correct1 in H3.
            }
            now rewrite Ei in H.
        }
        assert (In a1 (set_inter carrier_dec (set_map carrier_dec snd (filter (fun p : A * A => carrier_eqb (fst p) v) (edges arena))) (attractor 0 reach))).
        {
            rewrite Ei. now left.
        }
        now apply set_inter_elim in H as [H2 H3].
    }
    {
        exfalso.
        apply filter_In in H1 as [H1 _]. apply filter_In in H1 as [_ H1]. now rewrite Hb in H1.
    }
    {
        exfalso.
        apply set_in_map_iff in H1 as [p [H1 H2]].
        apply filter_In in H2 as [_ H2]. rewrite H1 in H2.
        apply set_mem_correct1 in H2. apply filter_In in H2 as [_ H2]. congruence.
    }
    rewrite <- Hr in *.
    apply filter_In in H1 as [_ H1].
    apply play_play'_ext_eq in Hp. 
        specialize (Hp 0). rewrite Str_nth_S_tl in Hp. rewrite !Str_nth_0_hd in Hp. simpl in Hp. 
        specialize (Hc 0). rewrite Str_nth_S_tl in Hc. rewrite !Str_nth_0_hd in Hc. simpl in Hc.
        simpl in Ev. rewrite <- Ev in *.
        apply forallb_forall with (x := (v, hd s)) in H1.
        {
            apply set_mem_correct1 in H1.
            apply filter_In in H1 as [_ H1].
            now apply set_mem_correct1 in H1.
        }
        apply filter_In. simpl. now rewrite carrier_eqb_refl.
}
intros v Hv Em Hnm Hm.
intros s. destruct s. intros Hp Hc Ev.
simpl in Ev. rewrite <- Ev in *. clear Ev. rewrite <- Em in *.
apply reach_tl.
apply (IHm (hd s)).
{
    (* aus Hnm und Hm sollte man schließen können, 
    dass mindestens zwei Schritte in Reach benötigt werden. 
    Da (hd s) einem Schritt entspricht, kann es nicht in Reach sein. *)
    unfold attractor in Hm. fold (attractor (S m) reach) in Hm.
    apply set_union_elim in Hm as [H1 | H1]; try now exfalso.
    destruct (attractor (S m) reach) eqn: Ea.
    {
        now exfalso.
    }
    destruct (Bool.eqb (player_positions arena v) player) eqn: Hb; apply set_union_elim in H1 as [H1 | H1].
    {
        apply play_play'_ext_eq in Hp. 
        specialize (Hp 0). rewrite Str_nth_S_tl in Hp. rewrite !Str_nth_0_hd in Hp. simpl in Hp. 
        specialize (Hc 0). rewrite Str_nth_S_tl in Hc. rewrite !Str_nth_0_hd in Hc. simpl in Hc.
        rewrite <- Hc in *; try now apply Bool.eqb_prop in Hb.
        unfold sigma. rewrite Hb.
        rewrite <- Em.
        destruct set_inter eqn: Ei.
        {
            apply set_in_map_iff in H1 as [p [H1 H2]].
            apply filter_In in H2 as [H2 _].
            apply filter_In in H2 as [H2 H3].
            assert (In (snd p) (set_inter carrier_dec (set_map carrier_dec snd (filter (fun p : A * A => carrier_eqb (fst p) v) (edges arena))) (attractor (S m) reach))).
            {
                apply set_inter_intro.
                {
                    apply set_in_map_iff. exists p. split; try easy.
                    apply filter_In. rewrite H1. split; try easy. apply carrier_eqb_refl.
                }
                rewrite <- Ea in H3.
                now apply set_mem_correct1 in H3.
            }
            now rewrite Ei in H.
        }
        assert (In a1 (set_inter carrier_dec (set_map carrier_dec snd (filter (fun p : A * A => carrier_eqb (fst p) v) (edges arena))) (attractor (S m) reach))).
        {
            rewrite Ei. now left.
        }
        apply set_inter_elim in H as [H2 H3].
        admit.
    }
    admit.
}
{
    (* sollte aus der Attractor-Definition folgen ?! *)
    admit.
}
{
    (* sollte ebenfalls aus Hnm und Hm folgen *)
    admit.
}
{
    (* Hm := In (hd (Cons v s)) attractor (S (S m)) => In (hd s) attractor (S m)
    Die Anzahl an benötigten Schritten muss also mit jedem tl Aufruf kleiner werden... gut!*)
    admit.
}
{
    apply play_play'_ext_eq. apply play_play'_ext_eq in Hp. 
    intros x.
    now specialize (Hp (S x)). 
}
{
    unfold consistent_with in Hc.
    intros x. now specialize (Hc (S x)).
}
easy.
Admitted.

End fix_player.
End reachability_games.


Definition test_positions : set nat := [0;1;2;3;4;5;6;7;8].

Definition test_pl_pos (n : nat) : bool :=
    match n with
    | 1 => true
    | 3 => true
    | 7 => true
    | 8 => true
    | _ => false
    end.

Definition test_edges : set (nat * nat) := [(0,1);(0,3);(1,0);(1,2);(2,1);(2,5);(3,4);(3,6);(4,0);(4,7);(4,8);(5,1);(5,7);(6,7);(7,6);(7,8);(8,5)].

Lemma test_ebp : forall p : nat * nat, set_In p test_edges -> set_In (fst p) test_positions /\ set_In (snd p) test_positions.
Proof.
intros p H.
split; repeat destruct H as [H | H]; try rewrite <- H; simpl; repeat (auto; try (right; auto)).
Qed.

Lemma test_oep : forall p : nat, set_In p test_positions -> exists v' : nat, set_In (p, v') test_edges.
Proof.
intros p H.
repeat destruct H as [H | H]; eexists; try rewrite <- H; simpl; eauto; repeat (right; eauto).
Unshelve. now exfalso.
Qed.

Lemma test_pos_set : NoDup test_positions.
Proof.
unfold test_positions.
repeat (apply NoDup_cons; [intros H; simpl in H; repeat (destruct H; [easy |]); easy |]).
apply NoDup_nil.
Qed.

Lemma test_edges_set : NoDup test_edges.
Proof.
unfold test_positions.
repeat (apply NoDup_cons; [intros H; simpl in H; repeat (destruct H; [easy |]); easy |]).
apply NoDup_nil.
Qed.


Definition test_arena : Arena nat := {|
    positions := test_positions;
    pos_is_set := test_pos_set;
    player_positions := test_pl_pos;
    edges := test_edges;
    edges_is_set := test_edges_set;
    edges_between_positions := test_ebp;
    out_edges_positions := test_oep
|}.

Definition nat_dec : (forall x y : nat, {x = y} + {x <> y}).
Proof.
decide equality.
Defined.

Definition test_strategy (_ : list nat) (n : nat) : nat :=
    match n with
      | 1 => 2
      | 3 => 4
      | 7 => 8
      | 8 => 5
      | _ => 10
    end.

Check is_strategy.

Lemma test_is_memoryless_strat : is_strategy test_arena true test_strategy /\ memoryless test_strategy.
Proof.
split.
{
intros l Hl v Hv Hb.
simpl in Hv.
repeat (destruct Hv as [Hv | Hv]); try rewrite <- Hv in *; try easy; firstorder.
}
easy.
Qed.

Lemma win_from_4 : winningFrom test_arena (winCon [4; 5]) true test_strategy 4.
Proof.
intros s Hp Hs Ev.
apply reach_hd. rewrite <- Ev. simpl. tauto.
Qed.

Lemma win_from_5 : winningFrom test_arena (winCon [4; 5]) true test_strategy 5.
Proof.
intros s Hp Hs Ev.
apply reach_hd. rewrite <- Ev. simpl. tauto.
Qed.

Lemma win_from_3 : winningFrom test_arena (winCon [4; 5]) true test_strategy 3.
Proof.
intros s Hp Hs Ev.
destruct s as [s0 s]. destruct s as [s1 s]. 
simpl in Ev. rewrite <- Ev in *.
apply reach_tl. 
assert (H := Hs). specialize (Hs 0). 
rewrite !Str_nth_S_tl in Hs.
rewrite !Str_nth_0_hd in Hs. simpl in Hs.                    
rewrite <- Hs in *; auto.
apply win_from_4; auto.
{
    now apply play_elim in Hp as [_ Hp].
}
intros n.
specialize (H (S n)).
now rewrite !Str_nth_S_tl in H.
Qed.

Lemma win_from_8 : winningFrom test_arena (winCon [4; 5]) true test_strategy 8.
Proof.
intros s Hp Hs Ev.
destruct s as [s0 s]. destruct s as [s1 s]. 
simpl in Ev. rewrite <- Ev in *.
apply reach_tl. 
assert (H := Hs). specialize (Hs 0). 
rewrite !Str_nth_S_tl in Hs.
rewrite !Str_nth_0_hd in Hs. simpl in Hs.                    
rewrite <- Hs in *; auto.
apply win_from_5; auto.
{
    now apply play_elim in Hp as [_ Hp].
}
intros n.
specialize (H (S n)).
now rewrite !Str_nth_S_tl in H.
Qed.

Lemma win_from_7 : winningFrom test_arena (winCon [4; 5]) true test_strategy 7.
Proof.
intros s Hp Hs Ev.
destruct s as [s0 s]. destruct s as [s1 s]. 
simpl in Ev. rewrite <- Ev in *.
apply reach_tl. 
assert (H := Hs). specialize (Hs 0). 
rewrite !Str_nth_S_tl in Hs.
rewrite !Str_nth_0_hd in Hs. simpl in Hs.                    
rewrite <- Hs in *; auto.
apply win_from_8; auto.
{
    now apply play_elim in Hp as [_ Hp].
}
intros n.
specialize (H (S n)).
now rewrite !Str_nth_S_tl in H.
Qed.

Lemma win_from_6 : winningFrom test_arena (winCon [4; 5]) true test_strategy 6.
Proof.
intros s Hp Hs Ev.
destruct s as [s0 s]. destruct s as [s1 s].
simpl in Ev. rewrite <- Ev in *.
apply reach_tl. 
assert (H := Hp).
apply play_play'_ext_eq in Hp.
specialize (Hp 0). rewrite !Str_nth_S_tl in Hp.
rewrite !Str_nth_0_hd in Hp. simpl in Hp.
repeat (destruct Hp as [Hp | Hp]); try easy.
apply pair_equal_spec in Hp as [Hp1 Hp2].
rewrite <- Hp2 in *.
apply win_from_7; auto.
{
    now apply play_elim in H as [_ H].
}
intros n.
specialize (Hs (S n)).
now rewrite !Str_nth_S_tl in Hs.
Qed.

Lemma test_strategy_uniform_winning : forall v : nat, 
  set_In v (attractor nat_dec test_arena true (length (test_positions)) [4;5]) -> 
  winningFrom test_arena (winCon [4; 5]) true test_strategy v.
Proof.
intros v Hv s Hp Hs Ev.
cbv in Hv.
destruct s as [s0 s]. simpl in Ev.
repeat destruct Hv as [Hv | Hv]; try rewrite <- Hv in *; rewrite <- Ev in *; try easy.
Admitted.












Compute cpre nat_dec test_arena true [4;5].

Compute attractor nat_dec test_arena true 2 [4;5].
Check attractor.

Compute find_smaller_attractor nat_dec test_arena [4;5] true 6 5.