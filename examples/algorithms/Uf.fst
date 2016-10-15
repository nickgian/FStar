module Uf

open FStar.Heap
open FStar.List.Tot
open FStar.Squash
open FStar.Classical
open FStar.Ghost
open FStar.ST
open FStar.TSet


type uf (a : Type) : Type = { content:a ; parent:ref (option (uf a)) }

noeq type reachable (#a:eqtype) (h:heap) (x:uf a) : uf a -> Type =
| Immediately : y:(uf a){sel h y.parent = Some x} -> reachable h x y
| Later : y:(uf a) -> reachable h x y -> z:(uf a){sel h z.parent = Some y} -> reachable h x z

(*
val give_witness : #p:Type -> p -> Pure unit (requires True) (ensures (fun _ -> p))
let give_witness #p x = give_proof (return_squash x)

val intro_impl : #p:Type -> #q:Type -> f:(p -> Tot q) -> Tot (p ==> q)
let intro_impl #p #q f =
  let g : p -> GTot q = f in
  return_squash g

val intro_forall : #a:Type -> #p:(a -> Type) -> $f:(x:a -> Tot (p x)) -> Tot (forall x. p x)
let intro_forall #a #p f =
  let g : x:a -> GTot (p x) = f in
  return_squash g

val give_proof0 : #p:Type0 -> p -> Pure unit (requires True) (ensures (fun _ -> p))
let give_proof0 #p _ = ()
*)

noeq type funcaccessible (#a:Type0) (f: a -> GTot (option a)) (u : a) : Type0 =
| FAcc : next:(match f u with | Some v -> funcaccessible f v | None -> unit) -> funcaccessible f u


let ufh a h = x:(uf a){Heap.contains h x.parent}
let state_true (h:heap) = True

let reach (a:eqtype) h (u : uf a) : GTot (option (uf a)) = sel h u.parent

assume val recall_step : #a:eqtype -> h:heap -> z:uf a -> y:uf a -> Lemma (requires (sel h z.parent = Some y)) (ensures (Heap.contains h y.parent))


let rec recall_reachable (#a:eqtype) (h:heap) (u1:uf a) (u2:uf a) (w:reachable h u1 u2) : Lemma (requires (Heap.contains h u2.parent)) (ensures (Heap.contains h u1.parent)) (decreases w) =
  match w with
  | Immediately z -> recall_step h z u1
  | Later y w0 z -> recall_step h z y ; recall_reachable h u1 y w0


let rec pullback_reachable (#a:eqtype) (h0:heap) (h1:heap) (u1:uf a) (u2: uf a) (w:reachable h1 u1 u2) : Pure (reachable h0 u1 u2) (requires (modifies_none h0 h1 /\ Heap.contains h0 u2.parent)) (ensures (fun _ -> True)) (decreases w) =
  match w with
  | Immediately z -> Immediately z
  | Later y w0 z -> recall_step h0 z y ; Later y (pullback_reachable h0 h1 u1 y w0) z


let rec pushforward_reachable (#a:eqtype) (h0:heap) (h1:heap) (u1:uf a) (u2: uf a) (w:reachable h0 u1 u2) : Pure (reachable h1 u1 u2) (requires (modifies_none h0 h1 /\ Heap.contains h0 u2.parent)) (ensures (fun _ -> True)) (decreases w) =
    match w with
    | Immediately z -> Immediately z
    | Later y w0 z -> recall_step h0 z y ; Later y (pushforward_reachable h0 h1 u1 y w0) z

//assume val recall_reachable : #a:eqtype -> h:heap -> u1:(uf a) -> u2:(uf a) -> Lemma (Heap.contains h u1.parent /\ reachable h u2 u1 ==> Heap.contains h u2.parent)
//assume val pullback_reachable : #a:eqtype -> h0:heap -> h1:heap -> u1:(uf a) -> u2:(uf a) -> reachable h1 u1 u2 -> Pure (reachable h0 u1 u2) (requires (modifies_none h0 h1 /\ Heap.contains h0 u2.parent)) (ensures (fun _ -> True))


let uf_invariant (a:eqtype) (h:heap) : Type0 = (forall (u0:ufh a h). funcaccessible (reach a h) u0) ///\ (forall (u0: ufh a h) (u1: ufh a h). u0.parent = u1.parent ==> u0 = u1) // * (u1: uf a -> reachable h u1 u0 -> Lemma (u1.parent <> u0.parent)))
let uf_invariant_fun (#a:eqtype) (h:heap) : Tot Type0 = (u0:ufh a h) -> GTot (funcaccessible (reach a h) u0)

let maintain_uf_invariant (a:eqtype) (h0:heap) (h1:heap) ($f : uf_invariant_fun h0 -> GTot (uf_invariant_fun h1)) : Lemma (requires (uf_invariant a h0)) (ensures (uf_invariant a h1)) =
  give_proof #(uf_invariant a h1) (map_squash (get_proof (uf_invariant a h0)) (fun (sq_uf_inv0 : squash (uf_invariant_fun h0)) -> map_squash sq_uf_inv0 f))

assume val uf_invariant_termination : (a:eqtype) -> (h:heap) -> (u:ufh a h) -> (p:ufh a h) -> Lemma (requires (uf_invariant a h /\ sel h u.parent = Some p)) (ensures (p << u))

//let typeof (a:Type) ($f : a) = f


//assume val axiom1_dep2 : #a:Type -> #b:(a->Type) -> #c:(x:a -> y:b x -> Type) -> f:(x:a -> y:b x -> Tot (c x y)) -> x:a -> y: b x -> Lemma (f x y << f)

//let pullback_contains (#a:Type) (h0:heap) (h1:heap) (x:ref a) (r0:ref a) : Lemma (requires (exists v. h1 == upd h0 r0 v /\ Heap.contains h1 x /\ x <> r0)) (ensures (Heap.contains h0 x)) = ()

(* Without invariants :
   let make_uf (#a:eqtype) (x:a) : St (uf a) =
     { content = x ; parent = alloc None }
*)


let make_uf (#a:eqtype) (x:a) : ST (uf a) (requires (uf_invariant a)) (ensures (fun h0 x h1 -> modifies_none h0 h1 /\ uf_invariant a h1)) =
  let h0 = get () in
  let res : uf a = { content = x ; parent = alloc None } in
  let h1 = get () in
  let uf_inv1 (uf_inv0:uf_invariant_fun h0) (u: ufh a h1) : GTot (funcaccessible (reach a h1) u) =
    let rec pushforward_accessible (u:ufh a h1) (acc0 : funcaccessible (reach a h0) u) : GTot (funcaccessible (reach a h1) u) (decreases acc0) =
      match reach a h1 u with | None -> FAcc () | Some v -> recall_step h1 u v ; FAcc (pushforward_accessible v acc0.next)
    in if u.parent = res.parent then FAcc () else let u : uf a = u in pushforward_accessible u (uf_inv0 u)
  in maintain_uf_invariant a h0 h1 uf_inv1 ;
  res



(*
let intro_forall_impl (#a:Type) (#b:a -> Type0) (#c:a -> Type0) ($f:x:a -> b x -> Lemma (c x)) : Lemma (forall (x:a). b x ==> c x) =
  let f0 (x:a) (y:b x) : GTot (squash (c x)) = f x y ; get_proof (c x) in
  let f1 (x:a) : GTot (squash (squash (b x -> GTot (c x)))) = return_squash (squash_double_arrow (return_squash (f0 x))) in
  let f2 : squash (x:a -> GTot (squash (b x -> GTot (c x)))) = squash_double_arrow (return_squash f1) in
  let f3 : squash (x:a -> GTot (b x ==> c x)) = f2 in
  let res : (forall (x:a). b x ==> c x) = f3 in
  give_witness res
  *)

(*
let rec collect_above (#a:eqtype) (h:heap) (u : ufh a h) : Ghost (set aref) (requires (uf_invariant a h)) (ensures (fun s -> forall v. (sel h v.parent <> None /\ (v = u \/ reachable h v u)) <==> mem (Ref v.parent) s)) (decreases u) =
  match sel h u.parent with
    | None ->
      let f (v:uf a) : GTot ((reachable h v u) ==> False) = impl_intro_gtot (let g (w:reachable h v u) : GTot False = match w with in g) in
      give_witness (forall_intro_gtot f) ;
      assert (forall v. ~(reachable h v u)) ;
      empty
    | Some p ->
      let f (v:uf a) (w:reachable h v u): Lemma (v.parent = p.parent \/ reachable h v p) = match w with | Immediately _ -> () | Later _ w0 _ -> give_witness w0 in
      forall_intro (let g (v:uf a) : Lemma (reachable h v u ==> v.parent = p.parent \/ reachable h v p) = impl_intro (f v) in g) ;
      assert(forall (v:uf a). (reachable h v u ==> (v.parent = p.parent \/ reachable h v p)))  ;
      recall_step h u p ; uf_invariant_termination a h u p ; admit () ; singleton (Ref u.parent) `union` collect_above h p
*)


let distinct_cell_lemma (#a:eqtype) (h:heap) (r1:ref a) (r2: ref a) : Lemma (sel h r1 <> sel h r2 ==> r1 <> r2) = ()

(* Without invariants :

  let rec root (u:uf a) : St (uf a) =
    match !u.parent with
    | none -> u
    | some p ->
      let r = root p in
      u.parent := r 
      r
*)

let rec root (#a:eqtype) (u:uf a) : ST (uf a) (requires (uf_invariant a)) (ensures (fun h0 r h1 -> (* Heap.contains h0 u.parent /\ uf_invariant a h0 /\ modifies (collect_above h0 u) h0 h1 /\*) uf_invariant a h1 /\ (r = u \/ reachable h0 r u) /\ sel h0 r.parent = None /\ sel h1 r.parent = None)) (decreases u) (* WARNING : check the decrease clause by hand for now *) =
  match !u.parent with
  | None -> admit () ; u
  | Some p ->
    let h0 = get () in
    recall u.parent ;
    recall p.parent ;
    uf_invariant_termination a h0 u p ;
    assert ( p << u ) ;
    let r = root p in
    let h1 = get () in
    assert (sel h0 u.parent = Some p) ;
    distinct_cell_lemma h0 r.parent u.parent ;
    assert (r.parent <> u.parent) ;
    recall u.parent ;
    u.parent := Some r ;
    let h2 = get () in
    assert (forall (u0 : ufh a h2). Heap.contains h1 u0.parent);
    assert (forall (u0 : ufh a h2). u0.parent <> u.parent ==> reach a h2 u0 = reach a h1 u0);
    let uf_inv2 (uf_inv1: uf_invariant_fun h1) (u1:ufh a h2) : GTot (funcaccessible (reach a h2) u1) =
      let rec pushforward (u0:ufh a h1) (w : funcaccessible (reach a h1) u0) : GTot (funcaccessible (reach a h2) u0) (decreases w) =
        if u0.parent = u.parent
        then ( match reach a h2 u0 with | Some r0 -> let wr0 : funcaccessible (reach a h2) r0 = match reach a h2 r0 with | None -> FAcc () in FAcc wr0 ) (* TODO : Something's wrong here FAcc (FAcc ()) should be enough  *)
        else match reach a h2 u0 with | None -> FAcc () | Some v -> recall_step h1 u0 v ; FAcc (pushforward v w.next)
      in let u1 : uf a = u1 in pushforward u1 (uf_inv1 u1)
    in maintain_uf_invariant a h1 h2 uf_inv2 ;
    assert (uf_invariant a h2) ;
    if p = r then give_witness #(reachable h0 r u) (Immediately u) else give_proof (map_squash (get_proof (reachable h0 r p)) (fun w -> Later p w u)) ;
    assert (reachable h0 r u) ;
    //admit () ;
    (*let sqw0 : squash (reachable h0 r u) =
      let res = if r = p then return_squash (Immediately p u) else map_squash (get_proof (reachable h0 r p)) (fun w -> Later r p w u) in
      admit () ; res
    in
    give_proof (bind_squash sqw0 (fun w0 -> bind_squash (get_proof (uf_invariant a h0)) (fun uf_inv0 -> (snd (uf_inv0 u)) r w0 ; get_proof (r.parent <> u.parent)))) ;
    assert (u.parent <> r.parent) ;
    assert (u <> r) ;
    assert (sel h1 r.parent = None) ;
    let aux (uf_inv: uf_invariant a h1) : GTot (squash (uf_invariant a h2)) =
      let wf (u1:ufh a h2) : GTot (funcaccessible (reach a h2) u1) =
        let root_accessible : funcaccessible (reach a h2) r = FAcc () in
        let u_accessible : funcaccessible (reach a h2) u = FAcc (root_accessible) in
        let rec pushforward (u0:uf a) (w : funcaccessible (reach a h1) u0) : GTot (funcaccessible (reach a h2) u0) (decreases w) =
          if u0 = u then u_accessible else match reach a h2 u0 with | None -> FAcc () | Some v -> FAcc (pushforward w.next)
        in
        pushforward u1 (fst (uf_inv u1))
      in
      let antialiasing (u1:ufh a h2) (u0:uf a) (w:reachable h2 u0 u1) : Lemma (u1.parent <> u0.parent) = admit ()
      (* idea : transform a "reachable h2 u0 u1" to a "rechable h0 u0 u1" by using the existing "reachable h0 r u0" whenever we stumble on a element in "collect_above h0 u (...)" *)
      (* then apply the uf_invariant for h0 to this rechability proof *)
      in
      return_squash begin fun u0 -> (wf u0, antialiasing u0) end
    in
    give_proof (bind_squash (get_proof (uf_invariant a h1)) aux) ;
   assert (uf_invariant a h2) ;
  assert (sel h2 r.parent = None) ;*)
    r


(* Without invariants :

   let rec uf_equiv (#a:eqtype) (u1:uf a) (u2:uf a) : St bool = root u1 = root u2

*)



let rec uf_equiv (#a:eqtype) (u1:uf a) (u2:uf a) : ST bool (requires (uf_invariant a)) (ensures (fun h0 _ h1 -> modifies ((collect_above h0 u1 (admit ())) `union` (collect_above h0 u2 (admit ()))) h0 h1 /\ uf_invariant a h1)) =
  let h0 = get () in
  let r1 = root u1 in
  let h1 = get () in
  let r2 = root u2 in
  let h2 = get () in
  admit () ;
  r1 = r2






  let rec collect_all_above (#a:eqtype) (h:heap) (u : uf a) (w:funcaccessible (reach a h) u) : Ghost (set aref) (requires True) (ensures (fun s -> forall v. (v.parent = u.parent \/ reachable h v u) <==> mem (Ref v.parent) s)) (decreases w) =
    match sel h u.parent with
      | None -> let f (v:uf a) : Tot ((reachable h v u) ==> False) = intro_impl (fun w -> match w with) in give_witness (intro_forall f) ; assert (forall v. ~(reachable h v u)) ; singleton (Ref u.parent)
      | Some p ->
        let f (v:uf a) (w:reachable h v u): Lemma (v.parent = p.parent \/ reachable h v p) = match w with | Immediately _ _ -> () | Later _ _ w0 _ -> give_witness w0 in
        intro_forall_impl f ; assert(forall (v:uf a). (reachable h v u ==> (v.parent = p.parent \/ reachable h v p)))  ;
        recall_step h u p ; admit () ; singleton (Ref u.parent) `union` collect_above h p w.next


 (* Without invariants :

    let rec uf_merge (#a:eqtype) (u1:uf a) (u2:uf a) : St unit =
    let r1 = root u1 in
    let r2 = root u2 in
    if r1 = r2 then () else r1.parent := Some r2

 *)


 let rec uf_merge (#a:eqtype) (u1:uf a) (u2:uf a) : ST unit (requires (uf_invariant a)) (ensures (fun h0 _ h1 -> modifies ((collect_all_above h0 u1 (admit ())) `union` (collect_above h0 u2 (admit ()))) h0 h1 /\ uf_invariant a h1)) =
  let r1 = root u1 in
  let r2 = root u2 in
  admit () ;
  if r1 = r2 then () else r1.parent := Some r2
