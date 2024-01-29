Require Export ltl.

Check infinitely_often.
Check (state_formula nat).

Definition gathered : state_formula bool := fun b =>
  match b with
    | true => True
    | false => False
  end.


Require Import List.
Import ListNotations.

Definition A_trans' : relation bool :=
    fun x y => In (x, y) [(true, true); (false, true); (false, false)].

  

Definition andrej_trans (n : nat) : relation bool :=
    match n with
      | 0 => (fun x y => 
        match x, y with
          | true, true => True
          | _, _ => False
        end)
      | 1 => (fun x y => 
        match x, y with
          | false, true => True
          | _, _ => False
        end)
      | 2 => (fun x y => 
        match x, y with
          | false, false => True
          | _, _ => False
        end)
      | _ => (fun x y => False)
    end.

Definition init0 (b : bool) : Prop :=
    match b with
      | true => True
      | false => False
    end.

Definition init1 (b : bool) : Prop :=
    match b with
      | true => False
      | false => True
    end.
    
Lemma test : forall (s : stream bool), run init0 andrej_trans s -> eventually (state2stream_formula gathered) s.
Proof.
intros s H.
elim H; clear H. 
intros H_init H_trans. 
apply ev_h.
unfold state2stream_formula. 
destruct s. simpl. simpl in H_init. destruct b. 
- trivial.
- trivial.
Qed.

CoFixpoint false_stream : stream bool := cons_str false false_stream.


Lemma def_eq_stream {A : Set} : forall s : stream A, s = cons_str (head_str s) (tl_str s).
Proof. 
intros s. destruct s. simpl. reflexivity.
Qed.


Lemma test' : not (forall (s : stream bool), run init1 andrej_trans s -> eventually (state2stream_formula gathered) s).
Proof.
intros H.
specialize (H false_stream). assert (H' : run init1 andrej_trans false_stream).
{
    constructor.
    - easy.
    - unfold trace. clear H. cofix coH. rewrite (def_eq_stream false_stream).
    constructor.
    + simpl. constructor.
    + assumption.
}
specialize (H H'). clear H'.
enough (forall s, (eventually (state2stream_formula gathered) s) -> s = false_stream -> False).
{
    eapply H0. eassumption. reflexivity.
}
clear H. 
intros s H.
induction H.
- intros E. subst str. contradiction.
- Check f_equal. intros E%(f_equal (@tl_str bool)). apply IHeventually. apply E.
Qed.



