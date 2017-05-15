module Bug626

(* Works *)
val lemma: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [smt_pat (x + y);smt_pat (y + x)]
let lemma x y = ()

val lemma2: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [smt_pat_or [
      [smt_pat (x + y)]];
   smt_pat_or [
       [smt_pat (y + x)]]]
(* Fails *)
(* let lemma2 x y = () *)

(* Works *)
val lemma3: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [smt_pat_or [
      [smt_pat (x + y);
       smt_pat (y + x)]]]
let lemma3 x y = ()

val lemma4: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [smt_pat_or [
      [smt_pat (x + y);
       smt_pat (y + x)]];
   smt_pat (x + y)]
(* Fails *)
(* let lemma4 x y = () *)

(* Works *)
val lemma5: x:int -> y:int -> Lemma
  (requires (True))
  (ensures  (True))
  [smt_pat [smt_pat_or [
      [smt_pat (x + y);
       smt_pat (y + x)]]];
   smt_pat [smt_pat (x + y)]]
let lemma5 x y = ()
