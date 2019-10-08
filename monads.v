Definition id {A: Type} (a: A) : A := a.

Lemma id_step :
  forall {A: Type} (a: A), id a = a.
Proof.
reflexivity.
Qed.

Definition equiv {A B: Type} (f g: A -> B) : Prop :=
  forall (a: A), f a = g a.

Notation "f ~~ g" := (equiv f g)
                     (at level 100, right associativity).

Definition compose {A B C: Type} (f: A -> B) (g: B -> C) : A -> C :=
  fun (a: A) => g (f a).

Lemma compose_step :
  forall {A B C: Type} (f: A -> B) (g: B -> C) (a: A),
    (compose f g) a = g (f a).
Proof.
reflexivity.
Qed.

Notation "f ;; g" := (compose f g)
                    (at level 80, right associativity).

Lemma compose_id_l :
  forall {A B: Type} (f: A -> B),
    (@id A);; f ~~ f.
Proof.
intros A B f a.
rewrite -> compose_step.
rewrite -> id_step.
reflexivity.
Qed.

Lemma compose_id_r :
  forall {A B: Type} (f: A -> B),
    f;; (@id B) ~~ f.
Proof.
intros A B F a.
rewrite -> compose_step.
rewrite -> id_step.
reflexivity.
Qed.

Lemma compose_assoc :
  forall {A B C D: Type} (f: A -> B) (g: B -> C) (h: C -> D),
    (f;; g);; h ~~ f;; (g;; h).
Proof.
intros A B C D f g h a.
repeat rewrite -> compose_step.
reflexivity.
Qed.

Record Functor : Type := mkFunctor {
  FObj : Type -> Type;
  FMorph : forall {A B: Type} (f: A -> B), FObj A -> FObj B;
  FId : forall (A: Type), FMorph (@id A) ~~ @id (FObj A);
  FCompose : forall (A B C: Type) (f: A -> B) (g: B -> C),
               FMorph (f;; g) ~~ (FMorph f);; (FMorph g)
}.

Inductive list (A: Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A}.

Fixpoint map {A B: Type} (f: A -> B) (l: list A) : list B :=
  match l with
  | nil => nil
  | cons a t => cons (f a) (map f t)
  end.

Lemma map_id :
  forall (A: Type), map (@id A) ~~ @id (list A).
Proof.
intros A a.
induction a as [| first rest IH].
 + rewrite -> id_step.
   reflexivity.
 + rewrite -> id_step.
   simpl.
   rewrite -> IH.
   repeat rewrite -> id_step.
   reflexivity.
Qed.

Lemma map_compose :
  forall {A B C: Type} (f: A -> B) (g: B -> C),
    map (f;; g) ~~ (map f);; (map g).
Proof.
intros.
intros a.
induction a as [| first rest IH].
+ reflexivity.
+ simpl.
  repeat rewrite -> IH.
  reflexivity.
Qed.

Definition ListF : Functor := {|
  FObj := list;
  FMorph := @map;
  FId := map_id;
  FCompose := @map_compose
|}.

Record Monad: Type :=
mkMonad
  {
    M: Functor;
    Eta(A: Type): A -> M.(FObj)(A);
    Mu(A: Type): M.(FObj)(M.(FObj)(A)) -> M.(FObj)(A)
  }.

Fixpoint reverse_accum {A: Type} (xs: list A) (acc: list A): list A :=
match xs with
| nil => acc
| cons first rest => reverse_accum rest (cons first acc)
end.

Definition reverse {A: Type} (xs: list A) := reverse_accum xs nil.

Fixpoint reversed_concat {A: Type} (xs ys: list A): list A :=
match xs with
| nil => ys
| cons first_x rest_x => reversed_concat rest_x (cons first_x ys)
end.

Definition concat {A: Type} (xs ys: list A): list A := reversed_concat (reverse xs) ys.

Compute concat (cons 1 nil) (cons 2 (cons 3 nil)).

Fixpoint flatten_accum {A: Type} (xs: list (list A)) (acc: list A): list A :=
match xs with
| nil => acc
| cons xs_first xs_rest => flatten_accum xs_rest (concat acc xs_first)
end.

Definition flatten {A: Type} (xs: list (list A)): list A := flatten_accum xs nil.


Definition ListM: Monad := {|
  M := ListF;
  Eta(A: Type)(a: A) := cons a nil;
  Mu(A: Type)(xs: list(list(A))) := flatten xs;
|}.

Print ListM.