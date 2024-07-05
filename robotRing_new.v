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

Lemma not_eventually_always_not {A : Set} : forall s : stream A, forall P : stream_formula A, (not (ltl.eventually P s)) <-> (always (fun x => not (P x)) s).
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

Lemma concat_repeat_nil {A : Type} : forall (n : nat), (@nil A) = concat (repeat [] n).
intros n. 
induction n. 
- now cbv.
- now cbn.
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

Lemma fold_right_eq {A B : Type} (f : B -> A -> A) i : forall l1 l2, l1 = l2 -> fold_right f i l1 = fold_right f i l2.
Proof.
intros l1 l2 E.
now rewrite E.
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

CoFixpoint zip_stream {A : Set} (s1 s2 : stream A) : stream (A * A) :=
  match s1, s2 with
    | cons_str h1 t1, cons_str h2 t2 => cons_str (h1, h2) (zip_stream t1 t2)
  end.

Lemma zip_stream_eq_head : forall {A : Set} (s s' : stream A), head_str (zip_stream s s') = (head_str s, head_str s').
Proof.
intros A s s'. destruct s. destruct s'. reflexivity.
Qed.
  
Lemma zip_stream_eq_tail : forall {A : Set} (s s' : stream A), tl_str (zip_stream s s') = zip_stream (tl_str s) (tl_str s').
Proof.
intros A s s'. destruct s. destruct s'. cbn. reflexivity.
Qed.

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

Context (winningRegion : list (list Z)).

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

Definition rotations (l : configuration) : list (configuration) := 
    map (fun (x : nat) => Nat.iter x rotate l) (seq 0 (length l)).

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

Definition gatheredConfig : configuration := (repeat (-1) (Nat.pred k)) ++ [Z.of_nat (Nat.pred n)].

Definition dec_listZ : forall x y : list Z, {x = y} + {x <> y}.
Proof.
repeat decide equality.
Defined.

Definition allTransitions : list (configuration * configuration) :=
  flat_map 
  (fun c => map (fun s => (c, s)) (map (successor c) (opponentChoices (map strategy (views c)))))
  configuration_quotient.


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


Lemma allTransitions_spec c1 c2 : In (c1, c2) allTransitions -> exists ms, In c1 configuration_quotient /\ successor c1 ms = c2 /\ In ms (opponentChoices (map strategy (views c1))).
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


(*
respectsTransitions corresponds to ltl.run, but does not allow a none_step.
*)
Definition respectsTransitions (s : stream configuration) (c : configuration) := ((head_str s) = c) /\ 
  always (state2stream_formula (fun p => step allTransitionsLabeled (fst p) (snd p))) (zip_stream s (tl_str s)).

Definition winningStrategy := forall (c : configuration), 
In c configuration_quotient -> In c winningRegion -> 
forall (s : stream configuration), respectsTransitions s c -> ltl.eventually (state2stream_formula (fun c => c = gatheredConfig)) s.

Definition winningStrategy_notLosing := forall (c : configuration), 
In c configuration_quotient -> not (In c winningRegion) -> 
not (forall (s : stream configuration), respectsTransitions s c -> ltl.eventually (state2stream_formula (fun c => c = gatheredConfig)) s).

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

Lemma test: winningStrategy 3 6 rw_winningStrategy_k3_n6 [[1; 1; 1]; [0; 1; 2]; [-1; 2; 2]; [0; 0; 3]; [
  -1; 1; 3]; [-1; 0; 4]; [-1; -1; 5]].
Proof.
intros c Hcq Hc.
repeat destruct Hc as [Hc | Hc]; try easy; rewrite <- Hc in Hcq.

