(set-option :print-success false)
(set-option :produce-proofs false)
(set-option :interpolant-check-mode true)
(set-option :produce-interpolants true)
(set-option :print-terms-cse false)

(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sl/rec_insert.spl:23:12-31:A precondition for this call of rec_insert might not hold
  tests/spl/sl/rec_insert.spl:10:11-48:Related location: This is the precondition that might not hold
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun elt$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst$0 () Loc)
(declare-fun n1_2$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun nondet_1$0 () Bool)
(declare-fun sk_?X_18$0 () SetLoc)
(declare-fun sk_?X_19$0 () SetLoc)
(declare-fun sk_?X_20$0 () SetLoc)
(declare-fun sk_?X_21$0 () SetLoc)
(declare-fun sk_?X_22$0 () SetLoc)
(declare-fun sk_?X_23$0 () SetLoc)
(declare-fun sk_?X_24$0 () SetLoc)
(declare-fun sk_?X_25$0 () SetLoc)
(declare-fun sk_?e_2$0 () Loc)
(declare-fun sk_FP$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 elt$0 ?y ?y)) (= elt$0 ?y)
            (Btwn$0 next$0 elt$0 (read$0 next$0 elt$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 lst$0 ?y ?y)) (= lst$0 ?y)
            (Btwn$0 next$0 lst$0 (read$0 next$0 lst$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 elt$0) elt$0))
            (not (Btwn$0 next$0 elt$0 ?y ?y)) (= elt$0 ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 lst$0) lst$0))
            (not (Btwn$0 next$0 lst$0 ?y ?y)) (= lst$0 ?y))) :named P5))

(assert (! (Btwn$0 next$0 elt$0 (read$0 next$0 elt$0) (read$0 next$0 elt$0)) :named P6))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P7))

(assert (! (Btwn$0 next$0 lst$0 (read$0 next$0 lst$0) (read$0 next$0 lst$0)) :named P8))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P9))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_21$0 sk_?X_19$0))
                 (or (in$0 x sk_?X_21$0) (in$0 x sk_?X_19$0)))
            (and (not (in$0 x sk_?X_21$0)) (not (in$0 x sk_?X_19$0))
                 (not (in$0 x (union$0 sk_?X_21$0 sk_?X_19$0)))))) :named P10))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P11))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_25$0 sk_?X_19$0))
                 (or (in$0 x sk_?X_25$0) (in$0 x sk_?X_19$0)))
            (and (not (in$0 x sk_?X_25$0)) (not (in$0 x sk_?X_19$0))
                 (not (in$0 x (union$0 sk_?X_25$0 sk_?X_19$0)))))) :named P12))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_21$0) (in$0 x sk_?X_19$0)
                 (in$0 x (intersection$0 sk_?X_21$0 sk_?X_19$0)))
            (and (or (not (in$0 x sk_?X_21$0)) (not (in$0 x sk_?X_19$0)))
                 (not (in$0 x (intersection$0 sk_?X_21$0 sk_?X_19$0)))))) :named P13))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_25$0) (in$0 x sk_?X_19$0)
                 (in$0 x (intersection$0 sk_?X_25$0 sk_?X_19$0)))
            (and (or (not (in$0 x sk_?X_25$0)) (not (in$0 x sk_?X_19$0)))
                 (not (in$0 x (intersection$0 sk_?X_25$0 sk_?X_19$0)))))) :named P14))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P15))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P16))

(assert (! (= (read$0 next$0 null$0) null$0) :named P17))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P18))

(assert (! (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_21$0 next$0 lst$0 null$0))) :named P19))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P20))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P21))

(assert (! (= emptyset$0 emptyset$0) :named P22))

(assert (! (= sk_?X_18$0 (union$0 sk_?X_21$0 sk_?X_19$0)) :named P23))

(assert (! (= sk_?X_19$0 sk_?X_20$0) :named P24))

(assert (! (= sk_?X_21$0 (lseg_domain$0 next$0 lst$0 null$0)) :named P25))

(assert (! (lseg_struct$0 sk_?X_21$0 next$0 lst$0 null$0) :named P26))

(assert (! (= sk_?X_23$0 sk_?X_24$0) :named P27))

(assert (! (= sk_?X_25$0 (lseg_domain$0 next$0 n1_2$0 null$0)) :named P28))

(assert (! (or (in$0 sk_?e_2$0 (intersection$0 sk_?X_25$0 sk_?X_23$0))
    (and (in$0 sk_?e_2$0 sk_FP$0) (not (in$0 sk_?e_2$0 FP$0)))
    (not (= (read$0 next$0 elt$0) null$0))
    (not (Btwn$0 next$0 n1_2$0 null$0 null$0))) :named P29))

(assert (! (not (in$0 null$0 Alloc$0)) :named P30))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0)))))) :named P31))

(assert (! (or (Btwn$0 next$0 n1_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_25$0 next$0 n1_2$0 null$0))) :named P32))

(assert (! (= n1_2$0 (read$0 next$0 lst$0)) :named P33))

(assert (! (= (read$0 next$0 elt$0) null$0) :named P34))

(assert (! (= emptyset$0 (intersection$0 sk_?X_21$0 sk_?X_19$0)) :named P35))

(assert (! (= sk_?X_18$0 FP$0) :named P36))

(assert (! (= sk_?X_20$0 (setenum$0 elt$0)) :named P37))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P38))

(assert (! (= sk_?X_22$0 (union$0 sk_?X_25$0 sk_?X_23$0)) :named P39))

(assert (! (= sk_?X_24$0 (setenum$0 elt$0)) :named P40))

(assert (! (= sk_FP$0 sk_?X_22$0) :named P41))

(assert (! (not (= lst$0 null$0)) :named P42))

(assert (! (not nondet_1$0) :named P43))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 n1_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 n1_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 n1_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 n1_2$0 null$0)))))) :named P44))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P45))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P46))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P47))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P48))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P49))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P50))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P51))

(check-sat)

(get-interpolants (and P22 P0 P21 P6 P3 P14 P28 P12 P51 P1 P25 P7 P17 P50 P39 P30 P8 P45 P46 P43 P20 P48 P36 P35 P18 P24) (and P26 P19 P47 P40 P5 P10 P34 P16 P44 P15 P29 P13 P9 P31 P42 P23 P33 P41 P2 P27 P11 P32 P4 P38 P37 P49))

(exit)