module Hacl.Spec.Bignum.Fsquare

open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Arith

let len = 5

// Really an uint64
type limb = nat
let v i = i

type seqelem = s:Seq.seq limb{Seq.length s = len}

let limb_size = 51

val seval : seqelem -> GTot nat
let seval s = pow2 (limb_size * 4) * v (Seq.index s 4)
            + pow2 (limb_size * 3) * v (Seq.index s 3)
            + pow2 (limb_size * 2) * v (Seq.index s 2)
            + pow2 (limb_size * 1) * v (Seq.index s 1)
            + pow2 (limb_size * 0) * v (Seq.index s 0)

#reset-options "--z3rlimit 6" // --initial_fuel 4 --max_fuel 4 --initial_ifuel 4 --max_ifuel 4"

(* private let lemma_mul_2 a b c d : Lemma ( (a+b+c+d)*(a+b+c+d) == *)
(*     a * a + a * b + a * c + a * d *)
(*   + b * a + b * b + b * c + b * d *)
(*   + c * a + c * b + c * c + c * d *)
(*   + d * a + d * b + d * c + d * d *)
(*   ) = *)
(*   assert_by_tactic (prune "";; addns "Prims";;smt) *)
(*           ( (a+b+c+d)*(a+b+c+d) == *)
(*     a * a + a * b + a * c + a * d *)
(*   + b * a + b * b + b * c + b * d *)
(*   + c * a + c * b + c * c + c * d *)
(*   + d * a + d * b + d * c + d * d *)
(*   ) *)

private let lemma_mul_5 a b c d e : Lemma ( (a+b+c+d+e)*(a+b+c+d+e) =
  a * a + a * b + a * c + a * d + a * e
  + b * a + b * b + b * c + b * d + b * e
  + c * a + c * b + c * c + c * d + c * e
  + d * a + d * b + d * c + d * d + d * e
  + e * a + e * b + e * c + e * d + e * e) =
  assert_by_tactic (prune "";; addns "Prims";; smt ())

          ( (a+b+c+d+e)*(a+b+c+d+e) ==
                                            a * a + a * b + a * c + a * d + a * e
                                          + b * a + b * b + b * c + b * d + b * e
                                          + c * a + c * b + c * c + c * d + c * e
                                          + d * a + d * b + d * c + d * d + d * e
                                          + e * a + e * b + e * c + e * d + e * e)

  (*

#reset-options "--max_fuel 1 --max_ifuel 0"

val lemma_fsquare_spec_2_1: s:seqelem -> Lemma
  (let r0 = v (Seq.index s 0) in
  let r1 = v (Seq.index s 1) in
  let r2 = v (Seq.index s 2) in
  let r3 = v (Seq.index s 3) in
  let r4 = v (Seq.index s 4) in
  (seval s * seval s =
  r0 * r0 + r0 * (pow2 51 * r1) + r0 * (pow2 102 * r2) + r0 * (pow2 153 * r3) + r0 * (pow2 204 * r4)
  + (pow2 51 * r1) * r0 + (pow2 51 * r1) * (pow2 51 * r1) + (pow2 51 * r1) * (pow2 102 * r2) + (pow2 51 * r1) * (pow2 153 * r3) + (pow2 51 * r1) * (pow2 204 * r4)
  + (pow2 102 * r2) * r0 + (pow2 102 * r2) * (pow2 51 * r1) + (pow2 102 * r2) * (pow2 102 * r2) + (pow2 102 * r2) * (pow2 153 * r3) + (pow2 102 * r2) * (pow2 204 * r4)
  + (pow2 153 * r3) * r0 + (pow2 153 * r3) * (pow2 51 * r1) + (pow2 153 * r3) * (pow2 102 * r2) + (pow2 153 * r3) * (pow2 153 * r3) + (pow2 153 * r3) * (pow2 204 * r4)
  + (pow2 204 * r4) * r0 + (pow2 204 * r4) * (pow2 51 * r1) + (pow2 204 * r4) * (pow2 102 * r2) + (pow2 204 * r4) * (pow2 153 * r3) + (pow2 204 * r4) * (pow2 204 * r4)))
let lemma_fsquare_spec_2_1 s =
    (* let r0 = v (Seq.index s 0) in *)
    (* let r1 = v (Seq.index s 1) in *)
    (* let r2 = v (Seq.index s 2) in *)
    (* let r3 = v (Seq.index s 3) in *)
    (* let r4 = v (Seq.index s 4) in *)
    (* lemma_mul_5 r0 (pow2 51 * r1) (pow2 102 * r2) (pow2 153 * r3) (pow2 204 * r4) *)

    let r0 = v (Seq.index s 0) * pow2 (limb_size * 0) in
    let r1 = v (Seq.index s 1) * pow2 (limb_size * 1) in
    let r2 = v (Seq.index s 2) * pow2 (limb_size * 2) in
    let r3 = v (Seq.index s 3) * pow2 (limb_size * 3) in
    let r4 = v (Seq.index s 4) * pow2 (limb_size * 4) in
    lemma_mul_5 r0 r1 r2 r3 r4
    
    (* assert_by_tactic split_arith *)
    (* (let r0 = v (Seq.index s 0) in *)
    (*   let r1 = v (Seq.index s 1) in *)
    (*   let r2 = v (Seq.index s 2) in *)
    (*   let r3 = v (Seq.index s 3) in *)
    (*   let r4 = v (Seq.index s 4) in *)
    (*   (seval s * seval s = *)
    (*   r0 * r0 + r0 * (pow2 51 * r1) + r0 * (pow2 102 * r2) + r0 * (pow2 153 * r3) + r0 * (pow2 204 * r4) *)
    (*   + (pow2 51 * r1) * r0 + (pow2 51 * r1) * (pow2 51 * r1) + (pow2 51 * r1) * (pow2 102 * r2) + (pow2 51 * r1) * (pow2 153 * r3) + (pow2 51 * r1) * (pow2 204 * r4) *)
    (*   + (pow2 102 * r2) * r0 + (pow2 102 * r2) * (pow2 51 * r1) + (pow2 102 * r2) * (pow2 102 * r2) + (pow2 102 * r2) * (pow2 153 * r3) + (pow2 102 * r2) * (pow2 204 * r4) *)
    (*   + (pow2 153 * r3) * r0 + (pow2 153 * r3) * (pow2 51 * r1) + (pow2 153 * r3) * (pow2 102 * r2) + (pow2 153 * r3) * (pow2 153 * r3) + (pow2 153 * r3) * (pow2 204 * r4) *)
    (*   + (pow2 204 * r4) * r0 + (pow2 204 * r4) * (pow2 51 * r1) + (pow2 204 * r4) * (pow2 102 * r2) + (pow2 204 * r4) * (pow2 153 * r3) + (pow2 204 * r4) * (pow2 204 * r4))) *)
