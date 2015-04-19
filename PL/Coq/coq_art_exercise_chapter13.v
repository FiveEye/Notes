Require Import Arith ZArith.

Section section_for_chapter_13.

CoInductive Stream (A:Set) : Set :=
  Cons : A -> Stream A -> Stream A.

CoFixpoint list_n (x : nat) : Stream nat := Cons nat 1 (list_n 1).

CoFixpoint check (s : Stream nat) : Stream nat :=
  match s with
  | Cons a s' => 
    match a with
    | O => Cons nat O (check s')
    | _ => Cons nat 1 (check s')
    end
  end.

Check list_n 1.

End section_for_chapter_13.