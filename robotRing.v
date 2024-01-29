Require Export ltl.
Require Export safety.
Require Import ZArith.
Require Import List.
Require Import Program.
Require Import Bool.
Require Import Sorting.

Global Open Scope Z_scope.

Import ListNotations.

Arguments rev {A}.

Inductive move : Set :=
  | Clockwise : move
  | CounterClockwise : move
  | Idle : move. 

Section robotRing.

(* k robots on a ring of n nodes *)
Context (k n : nat).

Context (strategy : list Z -> option move).

(* Configurations *)

Definition configuration := list Z.

Definition configurationSearchSpace := 
    map (map snd) (list_power (seq 0 k) (map (compose Z.pred Z.of_nat) (seq 0 (n+1)))).

Definition isConfig (c : configuration) : bool := 
    Z.eqb (fold_right Z.add 0 c) (Z.of_nat (n - k)).

Definition configurations : list(configuration) := 
    filter isConfig configurationSearchSpace.

(* Quotient of Configurations *)

Definition rotate (l : configuration) : configuration :=
    match l with
      | [] => []
      | x :: l' => l' ++ [x]
    end.

Definition rotations (l : configuration) : list (configuration) := 
    map (fun (x : nat) => Nat.iter x rotate l) (seq 0 (length l)).

Definition observational_equivalence_class (c : configuration) : list configuration := 
    let rot := rotations c in 
      rot ++ (map rev rot).

Fixpoint configuration_min (l l' : configuration) : configuration :=
    match l, l' with
    | [], _ => []
    | _, [] => []
    | (x :: xs), (y :: ys) => if Z.eqb x y then (x :: configuration_min xs ys) else (if Z.ltb x y then l else l')
    end.

Definition rep (c : configuration) : configuration := fold_right configuration_min (repeat (Z.of_nat n) k) (observational_equivalence_class c).

Definition dec_configuration : forall x y : configuration, {x = y} + {x <> y}.
Proof.
repeat decide equality.
Defined.

Definition configuration_quotient : list configuration := nodup dec_configuration (map rep configurations).

(* Helper for the following definitions*)
Fixpoint elemIndices (i : nat) (e : Z) (c : configuration) : list nat :=
    match c with
      | [] => []
      | e' :: tl => if Z.eqb e e' then i :: (elemIndices (Nat.succ i) e tl) else elemIndices (Nat.succ i) e tl
    end.

(* posTower computes the begin- and end-indices of each tower in the configuration *)
(* We need to assume, that c == rep c ... we make it explicit at this point *)
Definition posTower (c : configuration) : list (nat * nat) := fold_left (fun (ps : list (nat * nat)) (s : nat) => 
    match ps with
      | [] => (s, Nat.succ (Nat.modulo s k)) :: []
      | (i,j) :: tl => if Nat.eqb s j then (i, Nat.succ (Nat.modulo s k)) :: tl else (s, Nat.succ (Nat.modulo s k)) :: (i,j) :: tl
    end) (elemIndices 1 (-1) (rep c)) [].

(* pos computes the union of posTower and the indices of isolated robots as pairs (i,i) *)
(* We need to assume, that c == rep c ... we make it explicit at this point *)
Definition posIsolated (c : configuration) : list (nat * nat) := 
    fold_left 
      (fun (ps : list (nat * nat)) (i : nat) => 
        if (forallb (fun (p : nat * nat) => 
          match p with 
            | (x,y) => forallb (fun e => negb (Nat.eqb e i)) (seq x (Nat.succ(y-x))) end)) (posTower (rep c)) 
        then (i,i) :: ps else ps) 
        (seq 1 k) [].

Definition dec_pos : forall x y : (nat * nat), {x = y} + {x <> y}.
Proof.
repeat decide equality.
Defined.

Definition pos (c : configuration) : list (nat * nat) := nodup (dec_pos) ((posTower c) ++ (posIsolated c)).

(*
Inductive move : Set :=
  | Clockwise : move
  | CounterClockwise : move
  | Idle : move. 
*)

Definition move_eqb (m m' : move) : bool :=
  match m, m' with
    | Clockwise, Clockwise => true
    | CounterClockwise, CounterClockwise => true
    | Idle, Idle => true
    | _,_ => false
  end. 

Definition dec_move : forall x y : move, {x = y}+{x <> y}.
Proof.
decide equality.
Defined.

Definition interpretMove (i : nat) (m : move) : list Z :=
  match i, m with
    | _, Idle => repeat 0 k
    | (S O), Clockwise => (- 1) :: (repeat 0 (k-2)) ++ [1]
    | i, Clockwise =>  (repeat 0 (i-2)) ++ [1; -1] ++ (repeat 0 (k-2-(i-2)))
    | (S O), CounterClockwise => (1) :: (repeat 0 (k-2)) ++ [-1]
    | i, CounterClockwise =>  (repeat 0 (i-2)) ++ [-1; 1] ++ (repeat 0 (k-2-(i-2)))
  end.

Definition modifyMove (i : nat) (new : move) (ms : list move) : list move :=
  map (fun p: nat * move => if (Nat.eqb (fst p) i) then new else snd p) (combine (seq 1 k) ms).

Definition countMoveInRange (m : move) (ms : list move) (i j : nat) : nat :=
  length (filter (fun x => move_eqb m x) (firstn (j-i+1) (skipn (i-1) ms))).

Definition reorganizeTower (mos : list move) (p : nat * nat) : list move :=
  match p with
    | (i,j) => fold_left 
      (fun (movs : list move) (l : nat) => 
        if Nat.leb l (i + (countMoveInRange CounterClockwise mos i j) - 1) 
        then modifyMove l CounterClockwise movs 
        else if Nat.leb (j - (countMoveInRange Clockwise mos i j) + 1) l 
        then modifyMove l Clockwise movs 
        else modifyMove l Idle movs) (seq i (j - i + 1)) mos
  end.

Definition reorganizeMoves (ps : list (nat * nat)) (ms : list move) : list move :=
  fold_left reorganizeTower ps ms.

Definition lookup (x : nat) (ls : list (nat * nat)) : nat :=
  match find (fun p => Nat.eqb (fst p) x) ls with
    | Some x => snd x
    | None => 0
  end.

(*
  j' = Nat.succ (Nat.modulo j k)
  r = lookup (Nat.succ (Nat.modulo j k))) (pos c)
  nc = countMoveInRange Clockwise mt i j
  ncc = countMoveInRange CounterClockwise mt (Nat.succ (Nat.modulo j k)) (lookup (Nat.succ (Nat.modulo j k)) (pos c))
*)

Definition modifyMoveInRange (c : configuration) (mt : list move) (p : nat * nat) : list move :=
  match p with
    |(i, j) => if Z.eqb (nth (Nat.pred j) c (-1)) 0 
      then if Nat.leb (countMoveInRange CounterClockwise mt (Nat.succ (Nat.modulo j k)) (lookup (Nat.succ (Nat.modulo j k)) (pos c))) (countMoveInRange Clockwise mt i j) 
        then fold_left 
          (fun (mvs : list move) (a : nat) => 
            if andb (Nat.leb (Nat.succ (Nat.sub j (Nat.sub (countMoveInRange Clockwise mt i j) (countMoveInRange CounterClockwise mt (Nat.succ (Nat.modulo j k)) (lookup (Nat.succ (Nat.modulo j k)) (pos c)))))) a) (Nat.leb a j)
            then modifyMove a Clockwise mvs
            else if andb (Nat.leb (Nat.succ (Nat.sub j (countMoveInRange Clockwise mt i j))) a) (Nat.leb a (Nat.sub j (Nat.sub (countMoveInRange Clockwise mt i j) (countMoveInRange CounterClockwise mt (Nat.succ (Nat.modulo j k)) (lookup (Nat.succ (Nat.modulo j k)) (pos c))))))
             then modifyMove a Idle mvs
             else if andb (Nat.leb (Nat.succ (Nat.modulo j k)) a) (Nat.leb a (Nat.pred (Nat.add (Nat.succ (Nat.modulo j k)) (countMoveInRange CounterClockwise mt (Nat.succ (Nat.modulo j k)) (lookup (Nat.succ (Nat.modulo j k)) (pos c))))))
               then modifyMove a Idle mvs
               else mvs 
          : list move
          )
          (seq i ((Nat.succ (Nat.modulo j k)) - i + 1)) 
          mt
        else fold_left 
          (fun (mos : list move) (b : nat) =>
            if andb (Nat.leb (Nat.succ (Nat.modulo j k)) b) (Nat.leb b (Nat.pred (Nat.add (Nat.succ (Nat.modulo j k)) (Nat.sub (countMoveInRange CounterClockwise mt (Nat.succ (Nat.modulo j k)) (lookup (Nat.succ (Nat.modulo j k)) (pos c))) (countMoveInRange Clockwise mt i j)))))
            then modifyMove b CounterClockwise mos
            else if andb (Nat.leb (Nat.add (Nat.succ (Nat.modulo j k)) (Nat.sub (countMoveInRange CounterClockwise mt (Nat.succ (Nat.modulo j k)) (lookup (Nat.succ (Nat.modulo j k)) (pos c))) (countMoveInRange Clockwise mt i j))) b) (Nat.leb b (Nat.pred (Nat.add (Nat.succ (Nat.modulo j k)) (countMoveInRange CounterClockwise mt (Nat.succ (Nat.modulo j k)) (lookup (Nat.succ (Nat.modulo j k)) (pos c))))))
              then modifyMove b Idle mos
              else if andb (Nat.leb (Nat.succ (Nat.sub j (countMoveInRange Clockwise mt i j))) b) (Nat.leb b j)
                then modifyMove b Idle mos
                else mos 
          : list move
          ) 
          (seq i ((Nat.succ (Nat.modulo j k)) - i + 1)) 
          mt
      else mt
  end.

Definition successor (c : configuration) (moves : list move) : configuration :=
  rep (fold_left (fun (xs : list Z) (ys : list Z) => map (fun p => (fst p) + (snd p)) (combine xs ys)) (map (fun p => interpretMove (fst p) (snd p)) (combine (seq 1 k) (fold_left (modifyMoveInRange c) (pos c) (reorganizeMoves (pos c) moves)))) c).


  (*
Possible Lemma: For each input, successor computes a valid configuration.
*)


Fixpoint sequence (l : list (list (option move))) : list (list (option move)) :=
  match l with
    | [] => [[]]
    | m :: ms => flat_map (fun x => flat_map (fun xs => [(x :: xs)]) (sequence ms)) m
  end.

Fixpoint sequence' (l : list (list move)) : list (list move) :=
  match l with
    | [] => [[]]
    | m :: ms => flat_map (fun x => flat_map (fun xs => [(x :: xs)]) (sequence' ms)) m
  end.

Definition possibleMoves : list (list (option move)) :=  sequence (repeat [Some Clockwise; Some CounterClockwise; Some Idle; None] k).

Fixpoint dropWhile ( p: Z -> bool) (l:list Z) : list Z :=
  match l with
  | [] => []
  | (x :: xs) => if p x then dropWhile p xs else (x :: xs)
  end.

Definition views (c : configuration) : list (list Z) := map (fun x => rev (dropWhile (fun z => Z.eqb z (-1)) (rev (dropWhile (fun z => Z.eqb z (-1)) x)))) (rotations c).

Definition list_eqb (l1 l2 : list Z) : bool := 
  match list_eq_dec Z.eq_dec l1 l2 with
    | left _ => true
    | right _ => false
  end.

Definition option_eqb (o1 o2 : option move) : bool :=
  match o1, o2 with
    | None, None => true
    | Some m, Some n => move_eqb m n 
    | _, _ => false
  end.

Definition movesSatisfyConfig (c : configuration) (ms : list (option move)) : bool :=
  forallb
    (fun (p : (list Z) * (option move)) => 
      (if list_eqb (fst p) (rev (fst p)) then (orb (option_eqb (snd p) None) (option_eqb (snd p) (Some Idle))) else true) && 
      (match snd p with
        | Some m => true
        | None => list_eqb (fst p) (rev (fst p))
      end) && 
      (forallb (fun p' => if list_eqb (fst p) (fst p') 
                       then option_eqb (snd p) (snd p') 
                       else if list_eqb (fst p) (rev (fst p')) 
                            then if option_eqb (snd p) (Some Clockwise) 
                                  then option_eqb (snd p') (Some CounterClockwise)
                                  else if option_eqb (snd p) (Some CounterClockwise) 
                                       then option_eqb (snd p') (Some Clockwise)
                                       else option_eqb (snd p) (snd p')
                            else true) 
        (combine (views c) ms))) 
    (combine (views c) ms).


Definition dec_option_move : forall x y : option move, {x = y}+{x <> y}.
Proof.
decide equality.
apply dec_move.
Defined.

Definition opponentChoices (ms : list (option move)) : list (list move) :=
  map (fun x => 
    fst (fold_right 
      (fun (om : option move) (p : (list move) * (list move)) => 
        match om with
          | Some m => (m :: (fst p), snd p)
          | None => ((hd Clockwise (snd p)) :: (fst p), tl (snd p))
        end) 
      ([], x)
      ms)) (sequence' (repeat [Clockwise; CounterClockwise] (count_occ dec_option_move ms None))).

Definition gatheredConfig : configuration := (repeat (-1) (Nat.pred k)) ++ [Z.of_nat (Nat.pred n)].

Definition dec_listZ : forall x y : list Z, {x = y} + {x <> y}.
Proof.
repeat decide equality.
Defined.


Definition losingConfigs : list configuration :=
  filter
    (fun c => (negb (list_eqb c gatheredConfig)) && (
      let vs := nodup dec_listZ (views c) in
      if Nat.eqb (length vs) 1 then let v := hd [] vs in (list_eqb v (rev v)) || ((Z.even (hd 1 v)) && (Z.even (last v 1))) else false
      ))
    configuration_quotient.

(* init for ltl *)
Definition nonLosing (c : configuration) : Prop := In c (flat_map (fun conf => remove dec_configuration conf configuration_quotient) losingConfigs).


Definition allTransitions : list (configuration * configuration) :=
  flat_map 
  (fun c => map (fun s => (c, s)) (map (successor c) (opponentChoices (map strategy (views c)))))
  configuration_quotient.


Definition allTransitionsLabeled (u : unit) : relation configuration :=
  fun l r => In (l,r) allTransitions.

Lemma def_eq_stream : forall s : stream configuration, s = cons_str (head_str s) (tl_str s).
  Proof. 
  intros s. 
  destruct s. 
  simpl. 
  reflexivity.
  Qed.

(*
Lemma elim_none_or_one_step : forall (s s': configuration), none_or_one_step allTransitionsLabeled s s' -> ((s = s') \/ (step allTransitionsLabeled s s')).
  Proof.
  intros s s' H.
  destruct H.
  - left. reflexivity.
  - right. assumption.
  Qed.
*)

CoFixpoint zip_stream {A : Set} (s1 s2 : stream A) : stream (A * A) :=
  match s1, s2 with
    | cons_str h1 t1, cons_str h2 t2 => cons_str (h1, h2) (zip_stream t1 t2)
  end.

Definition respectsTransitions := forall (s : stream configuration) (st : configuration), ((head_str s) = st) /\ 
  always (state2stream_formula (fun p => step allTransitionsLabeled (fst p) (snd p))) (zip_stream s (tl_str s)).

Definition correctStrategy := forall (s : stream configuration) (st : configuration), 
  nonLosing st -> 
  (((head_str s) = st) /\ always (state2stream_formula (fun p => step allTransitionsLabeled (fst p) (snd p))) (zip_stream s (tl_str s))) -> 
  ltl.eventually (state2stream_formula (fun c => c = gatheredConfig)) s.

End robotRing.

Definition winningStrategy_k3_n6 (v : list Z) : option move := 
  match v with
    | [1;1;1] => Some Idle
    | [0;0;3] => Some Clockwise
    | [0;3;0] => Some Idle
    | [3;0;0] => Some CounterClockwise
    | [0;1;2] => Some Clockwise
    | [1;2;0] => Some CounterClockwise
    | [2;0;1] => Some CounterClockwise
    | [0;4] => Some Idle
    | [4; -1; 0] => Some CounterClockwise
    | [1;3] => Some Clockwise
    | [3; -1; 1] => Some CounterClockwise
    | [2;2] => Some Idle
    | [2; -1; 2] => Some Clockwise
    | [5] => Some Idle
    | _ => None
  end.


Lemma elim_stream : forall {A : Set} (s : stream A), s = cons_str (head_str s) (tl_str s).
Proof.
intros A s.
destruct s. reflexivity.
Qed.

Lemma stream_eq_head : forall {A : Set} (s s' : stream A), s = s' -> (head_str s) = (head_str s').
Proof.
intros A s s' E.
f_equal. assumption.
Qed.

Lemma zip_stream_eq_head : forall {A : Set} (s s' : stream A), head_str (zip_stream s s') = (head_str s, head_str s').
Proof.
intros A s s'. destruct s. destruct s'. reflexivity.
Qed.

Lemma strategy_step : forall (s : stream configuration),
  (always (state2stream_formula (fun p => step (allTransitionsLabeled 3 6 winningStrategy_k3_n6) (fst p) (snd p))) (zip_stream s (tl_str s))) ->
  step (allTransitionsLabeled 3 6 winningStrategy_k3_n6) (head_str s) (head_str (tl_str s)).
Proof.
intros s H_trans.
destruct s. eapply C_trans with (a := ()). simpl. simpl in H_trans. 
assert (exists (str : stream (configuration * configuration)), str =  (zip_stream (cons_str c s) s) /\ always (state2stream_formula (fun p : configuration * configuration => step (allTransitionsLabeled 3 6 winningStrategy_k3_n6) (fst p) (snd p))) str).
{
  eexists. now split.
}
destruct H as [str [E_str H]]. destruct H. destruct H. simpl in H.  
eapply stream_eq_head in E_str. rewrite zip_stream_eq_head in E_str. simpl in E_str. 
rewrite E_str in H. simpl in H. assumption.
Qed.

Lemma always_state_elim : forall {A : Set} (s : stream A) (P : state_formula A), 
always (state2stream_formula P) s -> (P (head_str s) /\ always (state2stream_formula P) (tl_str s)).
Proof.
intros A s P H.
destruct H.
split.
- assumption.
- assumption.
Qed.


Compute allTransitions 3 6 winningStrategy_k3_n6.


Lemma strategyWins : correctStrategy 3 6 winningStrategy_k3_n6.
Proof.
unfold correctStrategy.
intros s init H_nonL H_run.
destruct H_run as [H_init H_trans].
unfold nonLosing in H_nonL. 
simpl in H_nonL.
repeat (destruct H_nonL as [H_c_init | H_nonL]).
- destruct s as [s_hd s_tl]. apply ev_t. destruct s_tl as [s_tl_hd s_tl_tl]. apply ev_t. apply ev_h. unfold state2stream_formula.
eapply always_state_elim in H_trans.
simpl in H_trans. destruct H_trans as [H_trans_hd H_trans_tl].
eapply strategy_step in H_trans_tl. destruct H_trans_tl. simpl in H. destruct H_trans_hd. unfold allTransitionsLabeled in H. destruct H.
simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. simpl in H_init. rewrite H_init in H0. rewrite <- H_c_init in H0. clear -H0. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }  
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0.
}
destruct H. simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0.
}
destruct H. simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0.
}
destruct H. simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0.
}
destruct H. simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0.
}
destruct H. simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0.
}
destruct H. simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0.
}
destruct H.
- destruct s as [s_hd s_tl]. apply ev_t. destruct s_tl as [s_tl_hd s_tl_tl]. apply ev_t. apply ev_h. unfold state2stream_formula.
eapply always_state_elim in H_trans.
simpl in H_trans. destruct H_trans as [H_trans_hd H_trans_tl].
eapply strategy_step in H_trans_tl. destruct H_trans_tl. simpl in H. destruct H_trans_hd. unfold allTransitionsLabeled in H. destruct H.
simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. simpl in H_init. rewrite H_init in H0. rewrite <- H_c_init in H0. clear -H0. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }  
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0.
}
destruct H. simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0.
}
destruct H. simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0.
}
destruct H. simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0.
}
destruct H. simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0.
}
destruct H. simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0.
}
destruct H. simpl in H.
{
  eapply pair_equal_spec in H. destruct H. unfold allTransitionsLabeled in H0. destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. unfold rep in H2. simpl in H2. unfold successor in H2. simpl in H2. rewrite <- H2 in H. clear -H. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0. simpl in H0.
  {
    eapply pair_equal_spec in H0. destruct H0. rewrite <- H1. unfold gatheredConfig. easy.
  }
  destruct H0.
}
destruct H.
- destruct s as [s_hd s_tl]. apply ev_t. apply ev_h. unfold state2stream_formula.
eapply strategy_step in H_trans. rewrite H_init in H_trans. destruct H_trans. simpl in H. unfold allTransitionsLabeled in H. destruct H. 
{
  simpl in H. eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
simpl in H. destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H0. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
easy.
- destruct s as [s_hd s_tl]. apply ev_t. apply ev_h. unfold state2stream_formula.
eapply strategy_step in H_trans. rewrite H_init in H_trans. destruct H_trans. simpl in H. unfold allTransitionsLabeled in H. destruct H. 
{
  simpl in H. eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
simpl in H. destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H0. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
easy.
- destruct s as [s_hd s_tl]. apply ev_t. apply ev_h. unfold state2stream_formula.
eapply strategy_step in H_trans. rewrite H_init in H_trans. destruct H_trans. simpl in H. unfold allTransitionsLabeled in H. destruct H. 
{
  simpl in H. eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
simpl in H. destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H0. easy.
}
destruct H.
{
  eapply pair_equal_spec in H. destruct H. rewrite <- H_c_init in H. exfalso. clear -H. easy.
}
easy.
- apply ev_h. 
symmetry in H_c_init.
transitivity init; assumption.
- easy.
Qed.


