Require Export ltl.
Require Export safety.
Require Import ZArith.
Require Import List.
Require Import Program.
Require Import Bool.
Require Import Sorting.
Require Import Arith.
Require Import Coq.Arith.Wf_nat.

Require Import Permutation.
Require Import Lia.

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

Context (enoughRobots : Nat.lt 2 k : Prop).

Context (enoughNodes : Nat.le k n : Prop).

Context (strategy : list Z -> option move).

(* Configurations *)

Definition configuration := list Z.

Definition configurationSearchSpace := 
    map (map snd) (list_power (seq 0 k) (map (compose Z.pred Z.of_nat) (seq 0 (n+1)))).

Definition isConfig (c : configuration) : bool := 
    Nat.eqb k (length c) && Z.eqb (fold_right Z.add 0 c) (Z.of_nat (n - k)).

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

Definition rep (c : configuration) : configuration := 
  if (isConfig c) then fold_right configuration_min (repeat (Z.of_nat n) k) (observational_equivalence_class c) else c.

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
  if Nat.eqb (length moves) k  
  then rep (fold_left (fun (xs : list Z) (ys : list Z) => map (fun p => (fst p) + (snd p)) (combine xs ys)) (map (fun p => interpretMove (fst p) (snd p)) (combine (seq 1 k) (fold_left (modifyMoveInRange c) (pos c) (reorganizeMoves (pos c) moves)))) c)
  else [].

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

Lemma list_eqb_prop : forall (l1 l2 : list Z), list_eqb l1 l2 = true -> l1 = l2.
Proof.
intros l1 l2 H.
unfold list_eqb in H. now destruct list_eq_dec as [EQ | NEQ].
Qed.

Lemma not_list_eqb_prop : forall (l1 l2 : list Z), list_eqb l1 l2 = false -> l1 <> l2.
Proof.
intros l1 l2 H.
unfold list_eqb in H. now destruct list_eq_dec as [EQ | NEQ].
Qed.


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
  sequence' (map (fun o =>
    match o with
      | Some m => [m]
      | None => [Clockwise; CounterClockwise]
    end
  ) ms).

Definition gatheredConfig : configuration := (repeat (-1) (Nat.pred k)) ++ [Z.of_nat (Nat.pred n)].

Definition dec_listZ : forall x y : list Z, {x = y} + {x <> y}.
Proof.
repeat decide equality.
Defined.

(* Look up the concrete definition in literature, this will do it for our cases at the moment 
I looked it up:
Gathering is impossible for periodic and edge-edge-symmetric configurations

periodic means, that all robots have the same view and are disoriented.
edge-edge-symmetric means, that if k and n are even, all robots have the same view
*)


Definition losingConfigs : list configuration :=
  filter
    (fun c => (negb (list_eqb c gatheredConfig)) && (
      let vs := nodup dec_listZ (views c) in
      if Nat.eqb (length vs) 1 then let v := hd [] vs in (list_eqb v (rev v)) || (Nat.even k && Nat.even n) else false
      ))
    configuration_quotient.

Definition nonLosingConfigs : list configuration :=
  filter
  (fun c => (list_eqb c gatheredConfig) || (
    let vs := nodup dec_listZ (views c) in
    negb (Nat.eqb (length vs) 1) ||  let v := hd [] vs in (list_eqb v (rev v)) || (Nat.even k && Nat.even n))
    )
    configuration_quotient.

Lemma losing_dec : forall (c : configuration), In c configurations -> (In c losingConfigs) \/ (In c nonLosingConfigs).
Proof.
intros c.
intros H.
unfold configurations in H. apply filter_In in H. destruct H as [H1 H2].
unfold configurationSearchSpace in H1. apply in_map_iff in H1. destruct H1. destruct H.
Admitted.



(* init for ltl *)
Definition nonLosing (c : configuration) : Prop := In c (flat_map (fun conf => remove dec_configuration conf configuration_quotient) losingConfigs).

Definition nonLosing' (c : configuration) : Prop := In c nonLosingConfigs.

Lemma nonLosing_spec_test (c: configuration) : nonLosing c -> False.
Proof.
intros H.
unfold nonLosing in H.
apply in_flat_map in H.
destruct H as [x [H_in_nL H_in_conf]].
unfold losingConfigs in H_in_nL.
apply filter_In in H_in_nL.
destruct H_in_nL as [H_cq H].
apply in_remove in H_in_conf.
destruct H_in_conf.
Abort.


(* Look up the concrete definition in literature, this will do it for our cases at the moment 
I looked it up:
Gathering is impossible for periodic and edge-edge-symmetric configurations

periodic means, that all robots have the same view and are disoriented.
edge-edge-symmetric means, that if k and n are even, all robots have the same view
*)
(*
This should be the correct one...
*)
Lemma nonLosing_spec (c : configuration) : nonLosing' c -> In c configuration_quotient -> c = gatheredConfig \/ ((length (nodup dec_listZ (views c))) <> S 0) \/
(hd [] (nodup dec_listZ (views c)) = rev (hd [] (nodup dec_listZ (views c)))) \/ (Nat.Even k /\ Nat.Even n).
Proof.
intros H_nonL H_cq.
unfold nonLosing' in H_nonL.
unfold nonLosingConfigs in H_nonL.
apply filter_In in H_nonL.
destruct H_nonL as [H H_spec]. clear H.
apply orb_true_iff in H_spec.
destruct H_spec as [H | H_spec].
{
  apply or_introl. now apply list_eqb_prop in H.
}
apply orb_true_iff in H_spec.
destruct H_spec as [H_l | H_spec].
{
  apply or_intror. apply or_introl. intros H. apply Nat.eqb_eq in H. apply negb_true_iff in H_l. now rewrite H_l in H.
}
apply orb_true_iff in H_spec.
destruct H_spec as [H_r | H_e].
{
  apply or_intror. apply or_intror. apply or_introl. now apply list_eqb_prop in H_r.
}
apply or_intror.  apply or_intror. apply or_intror. apply andb_true_iff in H_e. 
destruct H_e as [H_k H_n]. apply Nat.even_spec in H_k. apply Nat.even_spec in H_n. now split.
Qed.

Definition allTransitions : list (configuration * configuration) :=
  flat_map 
  (fun c => map (fun s => (c, s)) (map (successor c) (opponentChoices (map strategy (views c)))))
  configuration_quotient.

Lemma opponentChoices_spec ms ls : In ms (opponentChoices ls) -> Forall2 (fun m l => 
  match l with
    | Some x => x = m
    | None => Clockwise = m \/ CounterClockwise = m
  end
  ) ms ls.
Proof.
revert ms.
induction ls.
- simpl. now intros ms [<- | ?].
- intros ms. cbn. intros H. apply in_flat_map in H as [m [H_m H_ms]]. apply in_flat_map in H_ms as [ms' [H_ms' H]]. apply IHls in H_ms'. destruct H; [ | easy].
subst ms. constructor; [ | easy]. destruct a.
+ now destruct H_m.
+ cbn in H_m. destruct H_m as [? | [? | ?]]; tauto.
Qed.


Lemma Forall2_map_r (X Y Z : Type) (P : X -> Z -> Prop) (f : Y -> Z) l1 l2 : Forall2 P l1 (map f l2) -> Forall2 (fun x y => P x (f y)) l1 l2.  
Proof.
intros H.
assert (exists l, (map f l2) = l /\ Forall2 P l1 l).
{
  eexists. now split.
}
destruct H0 as [l [E H_l]].
clear H.
revert l2 E.
induction H_l.
- intros l2 E. apply map_eq_nil in E. rewrite E. apply Forall2_nil.
- intros [ | z l2].
  + easy.
  + simpl. intros [=E1 E2]. subst. constructor.
    * easy.
    * now apply IHH_l.
Qed.

Lemma allTransitions_spec c1 c2 : In (c1, c2) allTransitions -> exists ms, In c1 configuration_quotient /\ successor c1 ms = c2 /\ Forall2 (fun (x : move) (y : list Z) => match strategy y with
| Some x0 => x0 = x
| None => Clockwise = x \/ CounterClockwise = x
end) ms (views c1).
Proof.
intros H.
apply in_flat_map in H.
destruct H as [x [H_x H_t]].
apply in_map_iff in H_t.
destruct H_t as [c [[=E1 E2] H_c]].
apply in_map_iff in H_c.
destruct H_c as [ms [H_c H_ms]].
apply opponentChoices_spec in H_ms.
apply Forall2_map_r in H_ms.
subst. 
now exists ms.
Qed.

Lemma allTransitions_spec' c1 c2 : In (c1, c2) allTransitions -> exists ms, In c1 configuration_quotient /\ successor c1 ms = c2 /\ In ms (opponentChoices (map strategy (views c1))).
Proof.
intros H.
apply in_flat_map in H.
destruct H as [x [H_x H_t]].
apply in_map_iff in H_t.
destruct H_t as [c [[=E1 E2] H_c]].
apply in_map_iff in H_c.
destruct H_c as [ms [H_c H_ms]].
subst. 
now exists ms.
Qed.

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

Definition correctStrategy' := forall (s : stream configuration) (st : configuration), 
  In st configuration_quotient ->
  nonLosing' st ->
  (((head_str s) = st) /\ always (state2stream_formula (fun p => step allTransitionsLabeled (fst p) (snd p))) (zip_stream s (tl_str s))) -> 
  ltl.eventually (state2stream_formula (fun c => c = gatheredConfig)) s.

(* for odd k, only periodic configurations are losing  *)
Definition isPeriodic (c : configuration) := Nat.Odd k -> exists (n : nat) (p : list Z), c = concat (repeat p (n+2)%nat).

Definition correctStrategyForOddNumberOfRobots := forall (s : stream configuration) (st : configuration), 
  In st configuration_quotient ->
  not (isPeriodic st) ->
  (((head_str s) = st) /\ always (state2stream_formula (fun p => step allTransitionsLabeled (fst p) (snd p))) (zip_stream s (tl_str s))) -> 
  ltl.eventually (state2stream_formula (fun c => c = gatheredConfig)) s.

Definition forOddRobotsPeriodicIsLosing := forall (s : stream configuration) (st : configuration), 
  In st configuration_quotient ->
  (isPeriodic st /\ not (st = gatheredConfig)) ->
  (((head_str s) = st) /\ always (state2stream_formula (fun p => step allTransitionsLabeled (fst p) (snd p))) (zip_stream s (tl_str s))) -> 
  ltl.always (state2stream_formula (fun c => isPeriodic c)) s.

(*
In LTL it should hold, that
not (eventually P) = alway(not P)
*)

Definition forOddRobotsPeriodicIsLosing' := forall (st : configuration), 
  In st configuration_quotient -> 
  (isPeriodic st /\ not (st = gatheredConfig)) -> not (forall (s : stream configuration),
  (((head_str s) = st) /\ always (state2stream_formula (fun p => step allTransitionsLabeled (fst p) (snd p))) (zip_stream s (tl_str s))) -> 
  ltl.eventually (state2stream_formula (fun c => c = gatheredConfig)) s).

Definition wfTransitions : list (configuration * configuration) :=
  flat_map 
  (fun c => if list_eqb c gatheredConfig then [] else map (fun s => (c, s)) (map (successor c) (opponentChoices (map strategy (views c)))))
  configuration_quotient.

Check well_founded (step (fun (u : unit) l r => In (l,r) wfTransitions)).

Lemma configuration_quotient_spec c : In c configuration_quotient -> exists c', rep c' = c /\ isConfig c' = true.
Proof.
intros H.
unfold configuration_quotient in H.
apply nodup_In in H.
apply in_map_iff in H.
destruct H as [x [E_rep H]].
unfold configurations in H.
apply filter_In in H. destruct H as [H E_conf].
eexists x. split; easy.
Qed.

Lemma test_correct : well_founded (step (fun (u : unit) l r => In (l,r) wfTransitions)) -> correctStrategy'.
Proof.
unfold correctStrategy'.
intros H_wf s init H_conf H_nonL H_run.
destruct H_run as [H_init H_trans].
apply nonLosing_spec in H_nonL; [| easy].
destruct H_nonL as [H_i | H_s].
{ 
  apply ev_h. now transitivity init.
}

Admitted.






Lemma fold_right_eq {A B : Type} (f : B -> A -> A) i : forall l1 l2, l1 = l2 -> fold_right f i l1 = fold_right f i l2.
Proof.
intros l1 l2 E.
now rewrite E.
Qed.

Lemma seq_elim len : seq 0 (S len) = seq 0 len ++ [len].
Proof.
induction len.
- now cbv.
- simpl. assert (forall x y, (seq x (S y)) = (x :: seq (S x) y)).
{
  now intros x y.
}
rewrite <- H.
rewrite <- seq_shift.
rewrite IHlen. 
rewrite map_app. 
now rewrite seq_shift.
Qed.

Lemma map_seq_eq {A : Type} (f g : nat -> A) (x : nat) : (forall y, (0 <= y < x)%nat -> f y = g y) -> map f (seq 0 x) = map g (seq 0 x).
induction x.
- easy.
- intros H. rewrite seq_elim. rewrite map_app. rewrite map_app. simpl. rewrite IHx.
{
  rewrite H.
  {
    easy.
  }
  lia.
}
intros y H_y.
apply (H y). 
lia.
Qed.

Lemma rotate_length : forall (c : configuration), isConfig c = true -> length (rotate c) = k.
Proof.
intros c H_c.
destruct c.
{
  unfold isConfig in H_c. apply andb_true_iff in H_c. destruct H_c as [H_false H].
  apply Nat.eqb_eq in H_false. cbv in H_false. unfold Nat.lt in enoughRobots. lia.
}
unfold rotate.
unfold isConfig in H_c. apply andb_true_iff in H_c. destruct H_c as [H1 H2].
apply Nat.eqb_eq in H1.
rewrite H1. rewrite app_length. simpl. lia.
Qed.

Lemma fold_right_cons_elim {A B : Type} (f : B -> A -> A) (a : A) (b : B) (l : list B): fold_right f a (b :: l) = f b (fold_right f a l).
Proof.
now cbn.
Qed.

Lemma fold_right_nil_elim {A B : Type} (f : B -> A -> A) (a : A) : fold_right f a [] = a.
Proof.
now cbn.
Qed.

Lemma sum_app_elim z c : fold_right Z.add 0 (c ++ [z]) = (fold_right Z.add 0 c) + z.
Proof.
induction c.
- cbn. lia.
- rewrite <- app_comm_cons. rewrite fold_right_cons_elim. rewrite fold_right_cons_elim. rewrite IHc. apply Z.add_assoc.
Qed.

Lemma rotate_sum : forall (c : configuration), isConfig c = true -> fold_right Z.add 0 (rotate c) = Z.of_nat (n - k).
Proof.
intros c H_c.
destruct c.
{
  unfold isConfig in H_c. apply andb_true_iff in H_c. destruct H_c as [H_false H].
  apply Nat.eqb_eq in H_false. cbv in H_false. unfold Nat.lt in enoughRobots. lia.
}
unfold rotate.
unfold isConfig in H_c. apply andb_true_iff in H_c. destruct H_c as [H1 H2].
apply Z.eqb_eq in H2.
rewrite <- H2.
rewrite sum_app_elim.
rewrite fold_right_cons_elim. lia.
Qed.

Lemma iter_rotate_config : forall (c : configuration) (m : nat), isConfig c = true -> isConfig (Nat.iter m rotate c) = true.
Proof.
intros c m. revert c.
induction m.
- intros. easy.
- intros c H_c. simpl.
unfold isConfig.
apply andb_true_iff.
split.
{
  apply Nat.eqb_eq.
  symmetry.
  apply rotate_length.
  apply IHm; easy.
}
apply Z.eqb_eq.
apply rotate_sum.
apply IHm; easy.
Qed.

Lemma iter_rotate_length : forall (c : configuration) (m : nat), isConfig c = true -> length (Nat.iter m rotate c) = k.
Proof.
intros c m H_c.
destruct c.
{
  unfold isConfig in H_c. apply andb_true_iff in H_c. destruct H_c as [H_false H].
  apply Nat.eqb_eq in H_false. cbv in H_false. unfold Nat.lt in enoughRobots. lia.
}
induction m.
{
  simpl.
  unfold isConfig in H_c. apply andb_true_iff in H_c. destruct H_c as [H1 H2].
  apply Nat.eqb_eq in H1. now simpl in H1.
}
rewrite Nat.iter_succ. rewrite rotate_length; [easy | ].
now apply iter_rotate_config.
Qed.

Lemma rotate_elim : forall (c : configuration), isConfig c = true -> rotate c = (tl c) ++ [(hd (-2) c)].
Proof.
intros c H.
destruct c.
{
  unfold isConfig in H. apply andb_true_iff in H. destruct H as [H_false H].
  apply Nat.eqb_eq in H_false. cbv in H_false. unfold Nat.lt in enoughRobots. lia.
}
easy.
Qed.

Lemma rotate_elim_skipn_firstn : forall (c : configuration), isConfig c = true -> rotate c = (skipn 1%nat c) ++ firstn 1%nat c.
Proof.
intros c H.
destruct c.
{
  unfold isConfig in H. apply andb_true_iff in H. destruct H as [H_false H].
  apply Nat.eqb_eq in H_false. cbv in H_false. unfold Nat.lt in enoughRobots. lia.
}
easy.
Qed.

Lemma list_eq_elim {A : Type} (a a' : A) (l l' : list A) : a :: l = a' :: l' -> a = a' /\ l = l'.
Proof.
now intros [=E1 E2].
Qed.

Lemma firstn_skipn_succ {A : Type} (l : list A) (m : nat) : firstn m l ++ (skipn m (firstn (S m) l)) = firstn (S m) l.
Proof.
revert m.
induction l.
{
  intros m. simpl. rewrite firstn_nil. now rewrite skipn_nil.
}
intros m.
destruct m.
{
  easy.
}
rewrite firstn_cons. rewrite firstn_cons. rewrite skipn_cons.
rewrite <- app_comm_cons.
f_equal. 
now apply IHl.
Qed.


Compute Nat.iter 2 rotate [1;2;3;4].
Compute (skipn 2 [1;2;3;4]) ++ (firstn 2 [1;2;3;4]).

Lemma rotate_nat_elim : forall (c : configuration) (m : nat), isConfig c = true -> (m <= k)%nat -> Nat.iter m rotate c = (skipn m c) ++ (firstn m c).
Proof.
intros c m H_c H_m.
revert H_c. revert c.
induction m.
- intros. simpl. now rewrite app_nil_r.
- intros c H_c.
destruct c.
{
  unfold isConfig in H_c. apply andb_true_iff in H_c. destruct H_c as [H_false H].
  apply Nat.eqb_eq in H_false. cbv in H_false. unfold Nat.lt in enoughRobots. lia.
}
rewrite Nat.iter_succ.
rewrite rotate_elim_skipn_firstn.
{
  rewrite IHm; [| lia | easy].
  rewrite skipn_app.
  unfold isConfig in H_c. apply andb_true_iff in H_c. destruct H_c as [H_length H_sum]. apply Nat.eqb_eq in H_length.
  rewrite skipn_length.
  rewrite skipn_skipn.
  rewrite <- app_assoc.
  assert (skipn (1 - (length (z :: c) - m)) (firstn m (z :: c)) ++ firstn 1 (skipn m (z :: c) ++ firstn m (z :: c)) = firstn (S m) (z :: c)).
  {
    rewrite <- H_length.
    assert ((1 - (k - m) = 0)%nat \/ (1 - (k - m) = 1)%nat).
    {
      lia.
    }
    destruct H as [H | H].
    {
      rewrite H.
      rewrite skipn_O.
      rewrite firstn_app.
      rewrite skipn_length. rewrite <- H_length. rewrite H. rewrite firstn_O. rewrite app_nil_r.
      rewrite firstn_skipn_comm.
      assert (m + 1 = S m)%nat. 
      {
        lia.
      }
      rewrite H0.
      apply firstn_skipn_succ.
    }
    exfalso.
    lia.
  }
  rewrite H. easy.
}
now apply iter_rotate_config.
Qed.


Lemma rotate_eq : forall (c : configuration), isConfig c = true -> Nat.iter k rotate c = c.
Proof.
intros c H_c.
rewrite rotate_nat_elim; [| easy| lia].
unfold isConfig in H_c. apply andb_true_iff in H_c. destruct H_c as [H_length H_sum]. apply Nat.eqb_eq in H_length.
rewrite H_length.
rewrite skipn_all2; [| easy].
now rewrite firstn_all2; [| easy].
Qed.

Lemma rotate_mod_k : forall (c : configuration) (m : nat), isConfig c = true -> (k < m)%nat -> Nat.iter m rotate c = Nat.iter (Nat.modulo m k) rotate c.
intros c m H_c H_m.
induction m.
- easy.
- simpl.
admit.
Admitted.

Lemma rotations_rotate_perm : forall (c : configuration) (m : nat), isConfig c = true -> Permutation (rotations c) (rotations (Nat.iter m rotate c)).
Proof.
Admitted.

Lemma rotations_rotate : forall (c : configuration) (m : nat), isConfig c = true -> incl (rotations (Nat.iter m rotate c)) (rotations c).
Proof.
intros c m H_c.
induction m.
(*
- unfold rotations. rewrite (rotate_length c 0 H_c).
unfold isConfig in H_c. apply andb_true_iff in H_c. destruct H_c as [H1 H2].
apply Nat.eqb_eq in H1. rewrite <- H1.
unfold incl. intros a H_incl.
now simpl in H_incl.
- unfold incl. intros a H_incl.
unfold incl in IHm. apply IHm. 

unfold rotations in H_incl. 
rewrite rotate_length in H_incl; [ | easy].
unfold rotations. rewrite rotate_length; [ | easy].
apply in_map_iff. apply in_map_iff in H_incl. destruct H_incl as [x [E_x H_x]].
rewrite <- Nat.iter_add in E_x. rewrite <- E_x. 
eexists (S x). split.
{
  rewrite <- E_x. rewrite <- Nat.iter_add. rewrite <- Nat.iter_add. rewrite  Nat.add_succ_l. rewrite Nat.add_succ_r. easy.
}
*)
Admitted.

Lemma rotations_rotate_r : forall (c : configuration) (m : nat), isConfig c = true -> incl (rotations c) (rotations (Nat.iter m rotate c)).
Proof.
Admitted.

Lemma configuration_min_max l : isConfig l = true -> configuration_min (repeat (Z.of_nat n) k) l = l.
Proof.
Admitted.

Lemma aux_fold_min_elim l1 l2 : incl l1 l2 -> configuration_min (fold_right configuration_min (repeat (Z.of_nat n) k) l1) (fold_right configuration_min (repeat (Z.of_nat n) k) l2) = fold_right configuration_min (repeat (Z.of_nat n) k) l1.
Proof.
revert l2.
induction l1 as [|x l1 IH]; cbn.
- intros l2 H. 
Admitted.

Lemma fold_min_elim l1 l2 : Permutation l2 l1 -> fold_right configuration_min (repeat (Z.of_nat n) k) l1 = fold_right configuration_min (repeat (Z.of_nat n) k) l2.
Proof.
intros H.
induction H; cbn.
- easy.
- congruence.
- admit.
- congruence.
Admitted.


Lemma fold_min_elim' l1 l2 : incl l1 l2 -> incl l2 l1 -> fold_right configuration_min (repeat (Z.of_nat n) k) l1 = fold_right configuration_min (repeat (Z.of_nat n) k) l2.
Proof.
revert l2.
induction l1.
- intros l2 H1 H2.
destruct l2.
{
  easy.
}
apply incl_l_nil in H2. now exfalso.
- intros l2. induction l2.
{
  intros H1 H2.
  apply incl_l_nil in H1. now exfalso.  
}
intros H1 H2.
rewrite (fold_right_cons_elim). rewrite fold_right_cons_elim.

Admitted.

Lemma map_seq {A : Type} (f : nat -> A) start len : (0 <= start < len)%nat -> map f (seq start len) = (f start) :: (map f (seq (S start) len)).
Proof.
intros H.
rewrite <- map_cons.
f_equal. 
destruct H as [H1 H2].
induction len.
- easy.
- intros. destruct H2.
Admitted.



Lemma rotations_elim c : isConfig c = true -> rotations c = (Nat.iter 0 rotate c) :: (map (fun x : nat => Nat.iter x rotate c) (seq 1 (length c))).
Proof.
intros H.
unfold rotations.
cbn.
apply (@map_seq configuration (fun x : nat => Nat.iter x rotate c) 0 (length c)).
unfold isConfig in H. apply andb_true_iff in H. destruct H as [H H1]. apply Nat.eqb_eq in H.
rewrite <- H.
destruct enoughRobots; lia.
Qed.

Lemma incl_rotations c1 c2: In c1 (rotations c2) -> incl (rotations c1) (rotations c2).
Proof.
Admitted.

Lemma map_rotations f c : map f (rotations c) = rotations (f c).
Proof.
Admitted.

Lemma obs_rep' : forall (c1 c2 : configuration), isConfig c1 = true -> isConfig c2 = true -> In c1 (observational_equivalence_class c2) -> rep c1 = rep c2.
Proof.
intros c1 c2 H_c1 H_c2 H_obs.
unfold rep.
rewrite H_c1. rewrite H_c2.
unfold observational_equivalence_class in H_obs.
apply in_app_or in H_obs.
destruct H_obs.
{
  unfold rotations in H. apply in_map_iff in H. destruct H as [x [E_x H_x]].
  apply fold_min_elim; unfold observational_equivalence_class.
  rewrite <- E_x.
  apply Permutation_app.
  {
    apply rotations_rotate_perm; easy.
  }
  apply Permutation_map.
  apply rotations_rotate_perm; easy.
}
rewrite map_rotations in H.
unfold rotations in H. apply in_map_iff in H. destruct H as [x [E_x H_x]].
apply fold_min_elim; unfold observational_equivalence_class.
assert (Permutation c2 c1).
{
  rewrite <- E_x.
  admit.
}
apply Permutation_app.
{
  rewrite <- E_x.
  admit.
}
apply Permutation_map.
rewrite <- E_x.
admit.
Admitted.

(*
Lemma obs_rep : forall (c1 c2 : configuration), isConfig c1 = true -> isConfig c2 = true -> In c1 (observational_equivalence_class c2) -> rep c1 = rep c2.
Proof.
intros c1 c2 H_c1 H_c2 H_obs.
unfold rep.
rewrite H_c1. rewrite H_c2.
unfold observational_equivalence_class in H_obs.
apply in_app_or in H_obs.
destruct H_obs.
{
  unfold rotations in H. apply in_map_iff in H. destruct H as [x [E_x H_x]].
  apply fold_min_elim; unfold observational_equivalence_class.
  {  
    apply incl_app; rewrite <- E_x.
    {
      apply incl_appl.
      now apply rotations_rotate.
    }
    apply incl_appr.
    apply incl_map.
    now apply rotations_rotate.
  }
  apply incl_app; rewrite <- E_x.
  {
    apply incl_appl.
    now apply rotations_rotate_r.
  }
  apply incl_appr.
    apply incl_map.
    now apply rotations_rotate_r.
}
apply in_map_iff in H.
destruct H as [x [E_x H_x]].
apply fold_min_elim; unfold observational_equivalence_class.
{
  rewrite <- E_x.
  apply incl_app.
  {
    apply incl_appr.
    apply incl_rotations in H_x.
    rewrite <- map_rotations.
    now apply incl_map.
  }
  apply incl_appl.
  rewrite map_rotations.
  rewrite rev_involutive.
  now apply incl_rotations in H_x.
}
rewrite <- E_x.
apply incl_app.
Admitted.
*)

Lemma uniqueViews : forall (c1 c2 : configuration) v, isConfig c1 = true -> isConfig c2 = true -> In v (views c1) -> In v (views c2) ->
  incl (observational_equivalence_class c1) (observational_equivalence_class c2).
Proof.
intros c1 c2 v H_c1 H_c2.
induction v.
- intros H_f1 H_f2.
unfold views in H_f1. apply in_map_iff in H_f1. destruct H_f1 as [x [E_x H_x]].
assert (forall (A : Type) (l : list A), (rev l) = [] -> l = []) as H_rev.
{
  intros A l.
  induction l.
  intros H.
  {
    easy.
  }
  intros H.
  simpl in H. clear -H. apply app_eq_nil in H. now destruct H.
}
apply H_rev in E_x.
admit.
-admit.
Admitted.



Lemma uniqueViews'' : forall (c1 c2 : configuration) v, isConfig c1 = true -> isConfig c2 = true -> In v (views c1) -> In v (views c2) ->
  incl (observational_equivalence_class c1) (observational_equivalence_class c2).
Proof.
intros c1 c2 v H_c1 H_c2 H_v1 H_v2.
unfold views in H_v1. apply in_map_iff in H_v1. destruct H_v1 as [c_v1 [H_v_v1 H_c_v1]].
unfold views in H_v2. apply in_map_iff in H_v2. destruct H_v2 as [c_v2 [H_v_v2 H_c_v2]].
unfold rotations in H_c_v1. apply in_map_iff in H_c_v1. destruct H_c_v1 as [x [E_x H_x]]. 
unfold rotations in H_c_v2. apply in_map_iff in H_c_v2. destruct H_c_v2 as [y [E_y H_y]]. 
apply in_seq in H_x. apply in_seq in H_y.
unfold incl.
intros a H.
(*
apply obs_rep in H.
- unfold observational_equivalence_class. apply in_or_app. apply or_introl.
unfold rotations. apply in_map_iff. eexists y. split; [ | now apply in_seq].

- admit.
- easy.
*)
Admitted.

Lemma uniqueViews' : forall (c1 c2 : configuration) v, isConfig c1 = true -> isConfig c2 = true -> In v (views c1) -> In v (views c2) -> rep c1 = rep c2.
Proof.
intros c1 c2 v H_c1 H_c2 H_v1 H_v2.
unfold views in H_v1. apply in_map_iff in H_v1. destruct H_v1 as [c_v1 [H_v_v1 H_c_v1]].
unfold views in H_v2. apply in_map_iff in H_v2. destruct H_v2 as [c_v2 [H_v_v2 H_c_v2]].
unfold rotations in H_c_v1. apply in_map_iff in H_c_v1. destruct H_c_v1 as [x [E_x H_x]]. 
unfold rotations in H_c_v2. apply in_map_iff in H_c_v2. destruct H_c_v2 as [y [E_y H_y]]. 
apply in_seq in H_x. apply in_seq in H_y.
unfold rep. rewrite H_c1. rewrite H_c2.
(* unfold observational_equivalence_class. *)
eapply fold_right_eq.
assert (rotations c1 = rotations c2).
{
  unfold rotations.
  unfold isConfig in H_c1. apply andb_true_iff in H_c1. destruct H_c1 as [H_length_c1 H_sum_c1].
  unfold isConfig in H_c2. apply andb_true_iff in H_c2. destruct H_c2 as [H_length_c2 H_sum_c2].
  apply Nat.eqb_eq in H_length_c1. rewrite <- H_length_c1.
  apply Nat.eqb_eq in H_length_c2. rewrite <- H_length_c2.
  rewrite <- H_length_c1 in H_x.
  rewrite <- H_length_c2 in H_y.
  apply map_seq_eq.
  intros z.
  induction z.
  {
    intros H_z.
    simpl.
    admit.
  }
  admit.
}

Admitted.

Lemma uniqueViews''' : forall (c1 c2 : configuration) v, In c1 configuration_quotient -> In c2 configuration_quotient -> In v (views c1) -> In v (views c2) -> c1 = c2.
Proof.
intros c1 c2 v H_c1 H_c2 H_v1 H_v2.
apply configuration_quotient_spec in H_c1. destruct H_c1 as [r1 [E_r1_c1 E_r1]].
apply configuration_quotient_spec in H_c2. destruct H_c2 as [r2 [E_r2_c2 E_r2]].
unfold views in H_v1. apply in_map_iff in H_v1. destruct H_v1 as [c_v1 [H_v_v1 H_c_v1]].
unfold views in H_v2. apply in_map_iff in H_v2. destruct H_v2 as [c_v2 [H_v_v2 H_c_v2]].
unfold rotations in H_c_v1. apply in_map_iff in H_c_v1. destruct H_c_v1 as [x [E_x H_x]].
induction x.
- simpl in E_x.

Admitted.

Lemma uniqueViews''''' : forall (c1 c2 : configuration), In c1 configuration_quotient -> In c2 configuration_quotient -> c1 <> c2 -> views c1 <> views c2.
Proof.
intros c1 c2 H_c1 H_c2 NE E.
apply configuration_quotient_spec in H_c1.
destruct H_c1 as [r1 [E_r1_c1 E_r1]].
apply configuration_quotient_spec in H_c2.
destruct H_c2 as [r2 [E_r2_c2 E_r2]].
unfold views in E. 
unfold rotations in E. 
rewrite (map_map (fun x : nat => Nat.iter x rotate c1)) in E. rewrite (map_map (fun x : nat => Nat.iter x rotate c2)) in E.
induction c1.
-

unfold isConfig in E_r1. apply andb_true_iff in E_r1. unfold rep in E_r1_c1.
unfold rotate in E.
rewrite <- E_r1_c1 in E.

Admitted.

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

  Definition rw_winningStrategy_k3_n6 (v : list Z) : option move := 
    match v with
      | [1;1;1] => None
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

Compute losingConfigs 4 10.
Compute nodup dec_listZ (views [1;2;1;2]).

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

Lemma zip_stream_eq_tail : forall {A : Set} (s s' : stream A), tl_str (zip_stream s s') = zip_stream (tl_str s) (tl_str s').
Proof.
intros A s s'. destruct s. destruct s'. cbn. reflexivity.
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

Lemma always_elim : forall {A : Set} (s : stream A) (P : stream_formula A), 
always P s -> (P s /\ always P (tl_str s)).
Proof.
intros A s P H.
destruct H.
split.
- assumption.
- assumption.
Qed.

Lemma concat_repeat_nil {A : Type} : forall (n : nat), (@nil A) = concat (repeat [] n).
intros n. 
induction n. 
- now cbv.
- now cbn.
Qed.


Lemma periodicAssumption {A : Type} (n : nat) (l1 l2 : list A) : l1 = concat (repeat l2 n) -> Nat.modulo (length l1) (length l2) = 0%nat /\ (length l1) = Nat.mul (length l2) n /\ l1 = concat (repeat l2 n).
Proof.
intros H. split.
- admit.
- admit.
Admitted.

Compute allTransitions 3 6 winningStrategy_k3_n6.

Lemma strategyLosesforOddRobotsIfPeriodic' : forOddRobotsPeriodicIsLosing 3 6 rw_winningStrategy_k3_n6.
Proof.
unfold forOddRobotsPeriodicIsLosing.
intros s init H_conf H_p H_run.
destruct H_run as [H_init H_trans].
destruct H_p as [H_p H_g].
unfold isPeriodic in H_p.
cbv in H_conf.
assert (Nat.Odd 3) as H_o.
{
  unfold Nat.Odd. eexists 1%nat. lia.
}
apply H_p in H_o.
repeat (destruct H_conf as [H | H_conf]).
- revert H_trans. revert H_init. revert s. cofix CoH. intros s H_init H_trans. destruct s as [s_hd s_tl]. constructor.
{
  unfold state2stream_formula. rewrite H_init. rewrite <- H. unfold isPeriodic. intros H3. eexists 1%nat. eexists [1]. now cbv. 
}
simpl in H_trans.
apply CoH.
{
  eapply always_state_elim in H_trans. destruct H_trans as [H_step1 H_always].
  rewrite zip_stream_eq_head in H_step1. simpl in H_step1. simpl in H_init.
  rewrite H_init in H_step1.
  destruct H_step1 as [a1 H_step1].
  apply allTransitions_spec' in H_step1.
  destruct H_step1 as [m1 [H_conf_init [H_succ_init H_forall_init]]]. 
  rewrite <- H in H_forall_init. cbn in H_forall_init. repeat (destruct H_forall_init as [H_m | H_forall_init]).
  + rewrite <- H_succ_init. rewrite <- H. rewrite <- H_m. now cbv.
  + rewrite <- H_succ_init. rewrite <- H. rewrite <- H_m. cbv. admit. (* Ab hier gehts schief...*)
  + rewrite <- H_succ_init. rewrite <- H. rewrite <- H_m. cbv. admit.
  + rewrite <- H_succ_init. rewrite <- H. rewrite <- H_m. cbv. admit.
  + rewrite <- H_succ_init. rewrite <- H. rewrite <- H_m. cbv. admit.
  + rewrite <- H_succ_init. rewrite <- H. rewrite <- H_m. cbv. admit.
  + rewrite <- H_succ_init. rewrite <- H. rewrite <- H_m. cbv. admit.
  + rewrite <- H_succ_init. rewrite <- H. rewrite <- H_m. now cbv.
  + now clear -H_forall_init.
}
eapply always_state_elim in H_trans. destruct H_trans as [H_step1 H_always].
now rewrite zip_stream_eq_tail in H_always. 
- admit.
- admit.
- admit.
- admit.
- assert (forall (n : nat) (p : list Z), ([-1; 0; 4] = concat (repeat p (n+2)%nat)) -> False) as H_false.
{
  intros n p E.
  apply periodicAssumption in E. destruct E as [E1 [E2 E3]].
  assert (length [-1; 0; 4] = 3%nat).
  {
    easy.
  }
  rewrite H0 in E1.
  rewrite H0 in E2.
  destruct n. 
  {
    clear -E2. lia.
  }
  revert E3.
  destruct p.
  {
    now intros H1.
  }
  intros H1.
  
}
destruct H_o as [m [l E]]. admit.
- rewrite <- H in H_g. now cbv in H_g. 
- easy.
Admitted.

Lemma not_eventually_always_not {A : Set} : forall s : stream A, forall P : stream_formula A, (not (ltl.eventually P s)) <-> (ltl.always (fun x => not (P x)) s).
Proof.
intros s P.
split.
- revert s P. cofix CoH. intros s P H. destruct s. constructor.
{
  intros H_p. assert (ltl.eventually P (cons_str a s)) as H_f.
  {
    now constructor. 
  }
  now apply H in H_f.
}
apply CoH. 
intros H_e.
assert (ltl.eventually P (cons_str a s)) as H_f.
{
  now apply ev_t.
}
now apply H in H_f.
- intros H_a H_e. induction H_e.
{
  apply always_elim in H_a.
  destruct H_a as [H_f H_tl].
  now apply H_f in H.
}
apply always_elim in H_a.
destruct H_a as [H_p H_tl].
simpl in H_tl.
now apply IHH_e in H_tl.
Qed.

CoFixpoint losing_stream : stream configuration := cons_str [1;1;1] losing_stream.

Lemma strategyLosesforOddRobotsIfPeriodic'' : forOddRobotsPeriodicIsLosing' 3 6 rw_winningStrategy_k3_n6.
Proof.
unfold forOddRobotsPeriodicIsLosing'.
intros init H_conf [H_p H_g] H_s.
unfold isPeriodic in H_p.
cbv in H_conf.
assert (Nat.Odd 3) as H_o.
{
  unfold Nat.Odd. eexists 1%nat. lia.
}
apply H_p in H_o.
repeat (destruct H_conf as [H | H_conf]).
- specialize (H_s losing_stream). rewrite <- H in H_s. 
assert (head_str losing_stream = [1; 1; 1] /\ 
always 
(state2stream_formula (fun p : configuration * configuration => step (allTransitionsLabeled 3 6 rw_winningStrategy_k3_n6) (fst p) (snd p))) 
(zip_stream losing_stream (tl_str losing_stream))) as H_arg.
{
  split; [easy |].
  simpl. cofix CoH. rewrite (elim_stream (zip_stream losing_stream losing_stream)).
  constructor.
  {
    unfold state2stream_formula. cbn. apply C_trans with (a := ()). cbv. now apply or_introl.
  }
  simpl. apply CoH. 
}
specialize (H_s H_arg).
revert H_s.
apply not_eventually_always_not.
rewrite elim_stream. simpl.
cofix CoH. 
constructor.
{
  intros H_f.
  unfold state2stream_formula in H_f. simpl in H_f. now clear -H_f.
}
now rewrite elim_stream. 
- assert (forall (n : nat) (p : list Z), (init = concat (repeat p (n+2)%nat)) -> False) as H_f.
{
  intros n l.
  rewrite <- H.
  destruct n as [|[|n]].
  - now destruct l as [|? [|? [|? [|? ?]]]].
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; congruence.
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; [|try congruence ..].
    now induction n.
}
destruct H_o as [m [l E]]. now apply (H_f m l) in E.
- assert (forall (n : nat) (p : list Z), (init = concat (repeat p (n+2)%nat)) -> False) as H_f.
{
  intros n l.
  rewrite <- H.
  destruct n as [|[|n]].
  - now destruct l as [|? [|? [|? [|? ?]]]].
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; congruence.
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; [|try congruence ..].
    now induction n.
}
destruct H_o as [m [l E]]. now apply (H_f m l) in E.
- assert (forall (n : nat) (p : list Z), (init = concat (repeat p (n+2)%nat)) -> False) as H_f.
{
  intros n l.
  rewrite <- H.
  destruct n as [|[|n]].
  - now destruct l as [|? [|? [|? [|? ?]]]].
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; congruence.
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; [|try congruence ..].
    now induction n.
}
destruct H_o as [m [l E]]. now apply (H_f m l) in E.
- assert (forall (n : nat) (p : list Z), (init = concat (repeat p (n+2)%nat)) -> False) as H_f.
{
  intros n l.
  rewrite <- H.
  destruct n as [|[|n]].
  - now destruct l as [|? [|? [|? [|? ?]]]].
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; congruence.
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; [|try congruence ..].
    now induction n.
}
destruct H_o as [m [l E]]. now apply (H_f m l) in E.
- assert (forall (n : nat) (p : list Z), (init = concat (repeat p (n+2)%nat)) -> False) as H_f.
{
  intros n l.
  rewrite <- H.
  destruct n as [|[|n]].
  - now destruct l as [|? [|? [|? [|? ?]]]].
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; congruence.
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; [|try congruence ..].
    now induction n.
}
destruct H_o as [m [l E]]. now apply (H_f m l) in E.
- rewrite <- H in H_g. now cbv in H_g.
- easy.
Qed.

Lemma strategyLosesforOddRobotsIfPeriodic : forOddRobotsPeriodicIsLosing 3 6 winningStrategy_k3_n6.
Proof.
unfold forOddRobotsPeriodicIsLosing.
intros s init H_conf H_p H_run.
destruct H_run as [H_init H_trans].
destruct H_p as [H_p H_g].
unfold isPeriodic in H_p.
cbv in H_conf.
assert (Nat.Odd 3) as H_o.
{
  unfold Nat.Odd. eexists 1%nat. lia.
}
apply H_p in H_o.
repeat (destruct H_conf as [H | H_conf]).
- revert H_trans. revert H_init. revert s. cofix CoH. intros s H_init H_trans. destruct s as [s_hd s_tl]. constructor.
{
  unfold state2stream_formula. rewrite H_init. rewrite <- H. unfold isPeriodic. intros H3. eexists 1%nat. eexists [1]. now cbv. 
}
simpl in H_trans.
apply CoH.
{
  eapply always_state_elim in H_trans. destruct H_trans as [H_step1 H_always].
  rewrite zip_stream_eq_head in H_step1. simpl in H_step1. simpl in H_init.
  rewrite H_init in H_step1.
  destruct H_step1 as [a1 H_step1].
  apply allTransitions_spec' in H_step1.
  destruct H_step1 as [m1 [H_conf_init [H_succ_init H_forall_init]]]. 
  rewrite <- H in H_forall_init. cbn in H_forall_init. destruct H_forall_init as [H_m1 | H_false]; [| easy].
  rewrite <- H in H_succ_init. rewrite <- H_m1 in H_succ_init. 
  rewrite <- H_succ_init. rewrite <- H. now cbv.
}
eapply always_state_elim in H_trans. destruct H_trans as [H_step1 H_always].
now rewrite zip_stream_eq_tail in H_always. 
- assert (forall (n : nat) (p : list Z), (init = concat (repeat p (n+2)%nat)) -> False) as H_false.
{
  intros n l.
  rewrite <- H.
  destruct n as [|[|n]].
  - now destruct l as [|? [|? [|? [|? ?]]]].
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; congruence.
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; [|try congruence ..].
    now induction n.
}
destruct H_o as [m [l E]]. now apply (H_false m l) in E.
- assert (forall (n : nat) (p : list Z), (init = concat (repeat p (n+2)%nat)) -> False) as H_false.
{
  intros n l.
  rewrite <- H.
  destruct n as [|[|n]].
  - now destruct l as [|? [|? [|? [|? ?]]]].
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; congruence.
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; [|try congruence ..].
    now induction n.
}
destruct H_o as [m [l E]]. now apply (H_false m l) in E.
- assert (forall (n : nat) (p : list Z), (init = concat (repeat p (n+2)%nat)) -> False) as H_false.
{
  intros n l.
  rewrite <- H.
  destruct n as [|[|n]].
  - now destruct l as [|? [|? [|? [|? ?]]]].
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; congruence.
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; [|try congruence ..].
    now induction n.
}
destruct H_o as [m [l E]]. now apply (H_false m l) in E.
- assert (forall (n : nat) (p : list Z), (init = concat (repeat p (n+2)%nat)) -> False) as H_false.
{
  intros n l.
  rewrite <- H.
  destruct n as [|[|n]].
  - now destruct l as [|? [|? [|? [|? ?]]]].
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; congruence.
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; [|try congruence ..].
    now induction n.
}
destruct H_o as [m [l E]]. now apply (H_false m l) in E.
- assert (forall (n : nat) (p : list Z), (init = concat (repeat p (n+2)%nat)) -> False) as H_false.
{
  intros n l.
  rewrite <- H.
  destruct n as [|[|n]].
  - now destruct l as [|? [|? [|? [|? ?]]]].
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; congruence.
  - destruct l as [|? [|? [|? [|? ?]]]]; cbn; [|try congruence ..].
    now induction n.
}
destruct H_o as [m [l E]]. now apply (H_false m l) in E.
- rewrite <- H in H_g. now cbv in H_g. 
- easy.
Qed.

Lemma strategyWinsOddRobots : correctStrategyForOddNumberOfRobots 3 6 winningStrategy_k3_n6.
Proof.
unfold correctStrategyForOddNumberOfRobots.
intros s init H_conf H_nonL H_run.
destruct H_run as [H_init H_trans].
unfold isPeriodic in H_nonL.
cbv in H_conf.
repeat (destruct H_conf as [H | H_conf]; [
  match goal with 
    | H : ([1; 1; 1] = init) |- _ => 
        rewrite <- H in H_nonL; assert (Nat.Odd 3 -> exists (n : nat) (p : list Z), [1; 1; 1] = concat (repeat p n)) as H_periodic; [ intros H_odd; eexists 3%nat; now eexists [1] | now apply H_nonL in H_periodic]
    | H : ([0; 1; 2] = init) |- _ => 
        eapply always_state_elim in H_trans; destruct H_trans as [H_step1 H_always];
        rewrite zip_stream_eq_head in H_step1; simpl in H_step1;
        eapply always_state_elim in H_always; destruct H_always as [H_step2 H_always];
        rewrite zip_stream_eq_tail in H_step2; rewrite zip_stream_eq_head in H_step2; simpl in H_step2;
        rewrite H_init in H_step1;
        destruct H_step1 as [a1 H_step1];
        apply allTransitions_spec' in H_step1;
        destruct H_step1 as [m1 [H_conf_init [H_succ_init H_forall_init]]]; 
        destruct H_step2 as [a2 H_step2];
        apply allTransitions_spec' in H_step2;
        destruct H_step2 as [m2 [H_conf_succ [H_succ_succ H_forall_succ]]];
  
        destruct s as [s_hd s_tl]; apply ev_t; destruct s_tl as [s_tl_hd s_tl_tl]; apply ev_t; apply ev_h;
  
        rewrite <- H in H_forall_init; cbn in H_forall_init; destruct H_forall_init as [H_m1 | H_false]; [
          rewrite <- H_succ_init in H_conf_succ; rewrite <- H in H_conf_succ; rewrite <- H_m1 in H_conf_succ; cbv in H_conf_succ;
          repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); 
          destruct H_conf_succ as [H_false | H_conf_succ]; [ 
            unfold state2stream_formula; simpl in H_succ_succ; simpl in H_forall_succ; simpl in H_succ_init; 
            rewrite <- H_succ_init in H_forall_succ; rewrite <- H_m1 in H_forall_succ; rewrite <- H in H_forall_succ; cbv in H_forall_succ;
            destruct H_forall_succ as [H_m2 | H_f]; [
              rewrite <- H_m2 in H_succ_succ; rewrite <- H_succ_succ; rewrite <- H_succ_init; rewrite <- H_m1; rewrite <- H; now cbv
          |     now clear -H_f ]
        |     repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); exfalso ; now clear -H_conf_succ ]
        |exfalso ; now clear -H_false ]
    | H : ([-1; 2; 2] = init) |- _ => 
        eapply always_state_elim in H_trans; destruct H_trans as [H_step1 H_always];
        rewrite zip_stream_eq_head in H_step1; simpl in H_step1;
        eapply always_state_elim in H_always; destruct H_always as [H_step2 H_always];
        rewrite zip_stream_eq_tail in H_step2; rewrite zip_stream_eq_head in H_step2; simpl in H_step2;
        rewrite H_init in H_step1;
        destruct H_step1 as [a1 H_step1];
        apply allTransitions_spec' in H_step1;
        destruct H_step1 as [m1 [H_conf_init [H_succ_init H_forall_init]]]; 
        destruct H_step2 as [a2 H_step2];
        apply allTransitions_spec' in H_step2;
        destruct H_step2 as [m2 [H_conf_succ [H_succ_succ H_forall_succ]]];
  
        destruct s as [s_hd s_tl]; apply ev_t; destruct s_tl as [s_tl_hd s_tl_tl]; apply ev_t; apply ev_h;
  
        rewrite <- H in H_forall_init; cbn in H_forall_init; destruct H_forall_init as [H_m1 | H_false]; [
          rewrite <- H_succ_init in H_conf_succ; rewrite <- H in H_conf_succ; rewrite <- H_m1 in H_conf_succ; cbv in H_conf_succ;
          repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); 
          destruct H_conf_succ as [H_false | H_conf_succ]; [ 
            unfold state2stream_formula; simpl in H_succ_succ; simpl in H_forall_succ; simpl in H_succ_init; 
            rewrite <- H_succ_init in H_forall_succ; rewrite <- H_m1 in H_forall_succ; rewrite <- H in H_forall_succ; cbv in H_forall_succ;
            destruct H_forall_succ as [H_m2 | H_f]; [
              rewrite <- H_m2 in H_succ_succ; rewrite <- H_succ_succ; rewrite <- H_succ_init; rewrite <- H_m1; rewrite <- H; now cbv
          |     now clear -H_f ]
        |     repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); exfalso ; now clear -H_conf_succ ]
        |exfalso ; now clear -H_false ]
    | H : ([0; 0; 3] = init) |- _ =>
        eapply always_state_elim in H_trans; destruct H_trans as [H_step1 H_always];
        rewrite zip_stream_eq_head in H_step1; simpl in H_step1;
        rewrite H_init in H_step1;
        destruct H_step1 as [a1 H_step1];
        apply allTransitions_spec' in H_step1;
        destruct H_step1 as [m1 [H_conf_init [H_succ_init H_forall_init]]]; 
  
        destruct s as [s_hd s_tl]; apply ev_t; apply ev_h;

        rewrite <- H in H_forall_init; cbn in H_forall_init; destruct H_forall_init as [H_m1 | H_false]; [ 
          rewrite <- H in H_succ_init; rewrite <- H_m1 in H_succ_init; simpl in H_succ_init; 
          unfold state2stream_formula; rewrite <- H_succ_init; now cbv
          | now clear -H_false]
    | H : ([-1; 1; 3] = init) |- _ =>
        eapply always_state_elim in H_trans; destruct H_trans as [H_step1 H_always];
        rewrite zip_stream_eq_head in H_step1; simpl in H_step1;
        rewrite H_init in H_step1;
        destruct H_step1 as [a1 H_step1];
        apply allTransitions_spec' in H_step1;
        destruct H_step1 as [m1 [H_conf_init [H_succ_init H_forall_init]]]; 
  
        destruct s as [s_hd s_tl]; apply ev_t; apply ev_h;
        
        rewrite <- H in H_forall_init; cbn in H_forall_init; destruct H_forall_init as [H_m1 | H_false]; [ 
          rewrite <- H in H_succ_init; rewrite <- H_m1 in H_succ_init; simpl in H_succ_init; 
          unfold state2stream_formula; rewrite <- H_succ_init; now cbv
          | now clear -H_false]
    | H : ([-1; 0; 4] = init) |- _ =>
        eapply always_state_elim in H_trans; destruct H_trans as [H_step1 H_always];
        rewrite zip_stream_eq_head in H_step1; simpl in H_step1;
        rewrite H_init in H_step1;
        destruct H_step1 as [a1 H_step1];
        apply allTransitions_spec' in H_step1;
        destruct H_step1 as [m1 [H_conf_init [H_succ_init H_forall_init]]]; 
  
        destruct s as [s_hd s_tl]; apply ev_t; apply ev_h;

        rewrite <- H in H_forall_init; cbn in H_forall_init; destruct H_forall_init as [H_m1 | H_false]; [ 
          rewrite <- H in H_succ_init; rewrite <- H_m1 in H_succ_init; simpl in H_succ_init; 
          unfold state2stream_formula; rewrite <- H_succ_init; now cbv
          | now clear -H_false]
    | H : ([-1; -1; 5] = init) |- _ => apply ev_h; now transitivity init
  end
|]); now clear -H_conf.
Qed.


Lemma strategyWinsOddRobots' : correctStrategyForOddNumberOfRobots 3 6 winningStrategy_k3_n6.
Proof.
unfold correctStrategyForOddNumberOfRobots.
intros s init H_conf H_nonL H_run.
destruct H_run as [H_init H_trans].
unfold isPeriodic in H_nonL.
destruct H_conf as [H_l | H].
{
  cbv in H_l. rewrite <- H_l in H_nonL. assert (Nat.Odd 3 -> exists (n : nat) (p : list Z), [1; 1; 1] = concat (repeat p n)).
  {
    intros H_odd. eexists 3%nat. now eexists [1].
  } 
  now apply H_nonL in H.
}
simpl in H.
eapply always_state_elim in H_trans. destruct H_trans as [H_step1 H_always].
rewrite zip_stream_eq_head in H_step1. simpl in H_step1. 
eapply always_state_elim in H_always. destruct H_always as [H_step2 H_always].
rewrite zip_stream_eq_tail in H_step2. rewrite zip_stream_eq_head in H_step2. simpl in H_step2.
rewrite H_init in H_step1.
destruct H_step1 as [a1 H_step1].
apply allTransitions_spec' in H_step1.
destruct H_step1 as [m1 [H_conf_init [H_succ_init H_forall_init]]]. 
destruct H_step2 as [a2 H_step2].
apply allTransitions_spec' in H_step2.
destruct H_step2 as [m2 [H_conf_succ [H_succ_succ H_forall_succ]]].

destruct s as [s_hd s_tl]. apply ev_t. destruct s_tl as [s_tl_hd s_tl_tl]. apply ev_t. apply ev_h.

destruct H.
{
  rewrite <- H in H_forall_init. cbn in H_forall_init. destruct H_forall_init as [H_m1 | H_false].
  {
    rewrite <- H_succ_init in H_conf_succ. rewrite <- H in H_conf_succ. rewrite <- H_m1 in H_conf_succ. cbv in H_conf_succ.
    repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])). 
    destruct H_conf_succ as [H_false | H_conf_succ]. 
    {
      unfold state2stream_formula.
    simpl in H_succ_succ. simpl in H_forall_succ. simpl in H_succ_init. 
    rewrite <- H_succ_init in H_forall_succ. rewrite <- H_m1 in H_forall_succ. rewrite <- H in H_forall_succ. cbv in H_forall_succ.
    destruct H_forall_succ as [H_m2 | H_f].
    {
      rewrite <- H_m2 in H_succ_succ. rewrite <- H_succ_succ. rewrite <- H_succ_init. rewrite <- H_m1. rewrite <- H. now cbv.
    }
    now clear -H_f.
    }
    repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); exfalso ; now clear -H_conf_succ. 
  }
  exfalso ; now clear -H_false.
}
repeat (try(destruct H; [ 
  rewrite <- H in H_forall_init; cbn in H_forall_init; destruct H_forall_init as [H_m1 | H_false]; [
    rewrite <- H_succ_init in H_conf_succ; rewrite <- H in H_conf_succ; rewrite <- H_m1 in H_conf_succ; cbv in H_conf_succ;
    repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); 
    destruct H_conf_succ as [H_false | H_conf_succ]; [ 
      unfold state2stream_formula; simpl in H_succ_succ; simpl in H_forall_succ; simpl in H_succ_init; 
      rewrite <- H_succ_init in H_forall_succ; rewrite <- H_m1 in H_forall_succ; rewrite <- H in H_forall_succ; cbv in H_forall_succ;
      destruct H_forall_succ as [H_m2 | H_f]; [
        rewrite <- H_m2 in H_succ_succ; rewrite <- H_succ_succ; rewrite <- H_succ_init; rewrite <- H_m1; rewrite <- H; now cbv
        | now clear -H_f ]
      | repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); exfalso ; now clear -H_conf_succ ]
  |exfalso ; now clear -H_false ] 
  |])); now clear -H.
Qed.




Lemma strategyWins' : correctStrategy' 3 6 winningStrategy_k3_n6.
Proof.
unfold correctStrategy'.
intros s init H_conf H_nonL H_run.
destruct H_run as [H_init H_trans].
apply nonLosing_spec in H_nonL; [| easy].
destruct H_nonL as [H_i | H_s].
{ 
  apply ev_h. now transitivity init.
}
(*
destruct H_s as [H_lv | H_s].
{
  destruct H_conf as [H_l | H].
  {
    cbn in H_l. destruct H_lv as [H_lv  H_s]. destruct H_s.
  {
    rewrite <- H_l in H. cbn in H. now clear -H.
  }
  rewrite <- H_l in H. cbn in H. destruct H as [H1 H2]. clear -H1. now apply Zeven_equiv in H1.
  }
  simpl in H.
  destruct H_lv as [H_false H_l].
  repeat (try (destruct H; [ rewrite <- H in H_false; clear -H_false; now cbv in H_false|])).
  destruct H as [H_g | H_f].
  {
    apply ev_h.  now transitivity init.
  }
  now clear -H_f.
}
*)
destruct H_conf as [H_l | H].
{
  cbn in H_l. rewrite <- H_l in H_s. clear -H_s. destruct H_s. destruct H0.
  {
    cbv in H. cbv in H0.
  }
}
simpl in H.
eapply always_state_elim in H_trans. destruct H_trans as [H_step1 H_always].
rewrite zip_stream_eq_head in H_step1. simpl in H_step1. 
eapply always_state_elim in H_always. destruct H_always as [H_step2 H_always].
rewrite zip_stream_eq_tail in H_step2. rewrite zip_stream_eq_head in H_step2. simpl in H_step2.
rewrite H_init in H_step1.
destruct H_step1 as [a1 H_step1].
apply allTransitions_spec' in H_step1.
destruct H_step1 as [m1 [H_conf_init [H_succ_init H_forall_init]]]. 
destruct H_step2 as [a2 H_step2].
apply allTransitions_spec' in H_step2.
destruct H_step2 as [m2 [H_conf_succ [H_succ_succ H_forall_succ]]].

destruct s as [s_hd s_tl]. apply ev_t. destruct s_tl as [s_tl_hd s_tl_tl]. apply ev_t. apply ev_h.

destruct H.
{
  rewrite <- H in H_forall_init. cbn in H_forall_init. destruct H_forall_init as [H_m1 | H_false].
  {
    rewrite <- H_succ_init in H_conf_succ. rewrite <- H in H_conf_succ. rewrite <- H_m1 in H_conf_succ. cbv in H_conf_succ.
    repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])). 
    destruct H_conf_succ as [H_false | H_conf_succ]. 
    {
      unfold state2stream_formula.
    simpl in H_succ_succ. simpl in H_forall_succ. simpl in H_succ_init. 
    rewrite <- H_succ_init in H_forall_succ. rewrite <- H_m1 in H_forall_succ. rewrite <- H in H_forall_succ. cbv in H_forall_succ.
    destruct H_forall_succ as [H_m2 | H_f].
    {
      rewrite <- H_m2 in H_succ_succ. rewrite <- H_succ_succ. rewrite <- H_succ_init. rewrite <- H_m1. rewrite <- H. now cbv.
    }
    now clear -H_f.
    }
    repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); exfalso ; now clear -H_conf_succ. 
  }
  exfalso ; now clear -H_false.
}
repeat (try(destruct H; [ 
  rewrite <- H in H_forall_init; cbn in H_forall_init; destruct H_forall_init as [H_m1 | H_false]; [
    rewrite <- H_succ_init in H_conf_succ; rewrite <- H in H_conf_succ; rewrite <- H_m1 in H_conf_succ; cbv in H_conf_succ;
    repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); 
    destruct H_conf_succ as [H_false | H_conf_succ]; [ 
      unfold state2stream_formula; simpl in H_succ_succ; simpl in H_forall_succ; simpl in H_succ_init; 
      rewrite <- H_succ_init in H_forall_succ; rewrite <- H_m1 in H_forall_succ; rewrite <- H in H_forall_succ; cbv in H_forall_succ;
      destruct H_forall_succ as [H_m2 | H_f]; [
        rewrite <- H_m2 in H_succ_succ; rewrite <- H_succ_succ; rewrite <- H_succ_init; rewrite <- H_m1; rewrite <- H; now cbv
        | now clear -H_f ]
      | repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); exfalso ; now clear -H_conf_succ ]
  |exfalso ; now clear -H_false ] 
  |])); now clear -H.
Qed.

Lemma rw_strategyWins : correctStrategy' 3 6 rw_winningStrategy_k3_n6.
Proof.
unfold correctStrategy'.
intros s init H_conf H_nonL H_run.
destruct H_run as [H_init H_trans].
apply nonLosing_spec in H_nonL; [| easy].
destruct H_nonL as [H_i | H_s].
{ 
  apply ev_h. now transitivity init.
}
(*
destruct H_s as [H_lv | H_s].
{
  destruct H_conf as [H_l | H].
  {
    cbn in H_l. destruct H_lv as [H_lv  H_s]. destruct H_s.
  {
    rewrite <- H_l in H. cbn in H. now clear -H.
  }
  rewrite <- H_l in H. cbn in H. destruct H as [H1 H2]. clear -H1. now apply Zeven_equiv in H1.
  }
  simpl in H.
  destruct H_lv as [H_false H_l].
  repeat (try (destruct H; [ rewrite <- H in H_false; clear -H_false; now cbv in H_false|])).
  destruct H as [H_g | H_f].
  {
    apply ev_h.  now transitivity init.
  }
  now clear -H_f.
}
*)
destruct H_conf as [H_l | H].
{
  cbn in H_l. rewrite <- H_l in H_s. clear -H_s. now cbv in H_s.
}
simpl in H.
eapply always_state_elim in H_trans. destruct H_trans as [H_step1 H_always].
rewrite zip_stream_eq_head in H_step1. simpl in H_step1. 
eapply always_state_elim in H_always. destruct H_always as [H_step2 H_always].
rewrite zip_stream_eq_tail in H_step2. rewrite zip_stream_eq_head in H_step2. simpl in H_step2.
rewrite H_init in H_step1.
destruct H_step1 as [a1 H_step1].
apply allTransitions_spec' in H_step1.
destruct H_step1 as [m1 [H_conf_init [H_succ_init H_forall_init]]]. 
destruct H_step2 as [a2 H_step2].
apply allTransitions_spec' in H_step2.
destruct H_step2 as [m2 [H_conf_succ [H_succ_succ H_forall_succ]]].

destruct s as [s_hd s_tl]. apply ev_t. destruct s_tl as [s_tl_hd s_tl_tl]. apply ev_t. apply ev_h.

destruct H.
{
  rewrite <- H in H_forall_init. cbn in H_forall_init. destruct H_forall_init as [H_m1 | H_false].
  {
    rewrite <- H_succ_init in H_conf_succ. rewrite <- H in H_conf_succ. rewrite <- H_m1 in H_conf_succ. cbv in H_conf_succ.
    repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])). 
    destruct H_conf_succ as [H_false | H_conf_succ]. 
    {
      unfold state2stream_formula.
    simpl in H_succ_succ. simpl in H_forall_succ. simpl in H_succ_init. 
    rewrite <- H_succ_init in H_forall_succ. rewrite <- H_m1 in H_forall_succ. rewrite <- H in H_forall_succ. cbv in H_forall_succ.
    destruct H_forall_succ as [H_m2 | H_f].
    {
      rewrite <- H_m2 in H_succ_succ. rewrite <- H_succ_succ. rewrite <- H_succ_init. rewrite <- H_m1. rewrite <- H. now cbv.
    }
    now clear -H_f.
    }
    repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); exfalso ; now clear -H_conf_succ. 
  }
  exfalso ; now clear -H_false.
}
repeat (try(destruct H; [ 
  rewrite <- H in H_forall_init; cbn in H_forall_init; destruct H_forall_init as [H_m1 | H_false]; [
    rewrite <- H_succ_init in H_conf_succ; rewrite <- H in H_conf_succ; rewrite <- H_m1 in H_conf_succ; cbv in H_conf_succ;
    repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); 
    destruct H_conf_succ as [H_false | H_conf_succ]; [ 
      unfold state2stream_formula; simpl in H_succ_succ; simpl in H_forall_succ; simpl in H_succ_init; 
      rewrite <- H_succ_init in H_forall_succ; rewrite <- H_m1 in H_forall_succ; rewrite <- H in H_forall_succ; cbv in H_forall_succ;
      destruct H_forall_succ as [H_m2 | H_f]; [
        rewrite <- H_m2 in H_succ_succ; rewrite <- H_succ_succ; rewrite <- H_succ_init; rewrite <- H_m1; rewrite <- H; now cbv
        | now clear -H_f ]
      | repeat (try (destruct H_conf_succ as [H_false | H_conf_succ]; [exfalso ; now clear -H_false | ])); exfalso ; now clear -H_conf_succ ]
  |exfalso ; now clear -H_false ] 
  |])); now clear -H.
Qed.



