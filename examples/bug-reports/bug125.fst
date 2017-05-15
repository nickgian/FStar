module Bug125smt_pat

val test: a:int -> Lemma (* ( requires (True) ) *)
                         (ensures ( a * a >= 0 ))
                         [smt_pat ( a * a ) ]
let test a = ()
