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
  tests/spl/sl/rec_filter.spl:24:11-25:A precondition for this call of rec_filter might not hold
  tests/spl/sl/rec_filter.spl:10:11-24:Related location: This is the precondition that might not hold
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
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_1$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun n1_2$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun nondet_1$0 () Bool)
(declare-fun sk_?X_14$0 () SetLoc)
(declare-fun sk_?X_15$0 () SetLoc)
(declare-fun sk_?e_3$0 () Loc)
(declare-fun sk_FP_1$0 () SetLoc)
(declare-fun x$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 x$0 ?y ?y)) (= x$0 ?y)
            (Btwn$0 next$0 x$0 (read$0 next$0 x$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 x$0) x$0)) (not (Btwn$0 next$0 x$0 ?y ?y))
            (= x$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P4))

(assert (! (Btwn$0 next$0 x$0 (read$0 next$0 x$0) (read$0 next$0 x$0)) :named P5))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P6))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P7))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0)
                 (in$0 x (setminus$0 Alloc$0 (setenum$0 x$0)))
                 (not (in$0 x (setenum$0 x$0))))
            (and (or (in$0 x (setenum$0 x$0)) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 (setenum$0 x$0))))))) :named P8))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 (setenum$0 x$0)))
                 (not (in$0 x (setenum$0 x$0))))
            (and (or (in$0 x (setenum$0 x$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 (setenum$0 x$0))))))) :named P9))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P10))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P11))

(assert (! (= (read$0 next$0 null$0) null$0) :named P12))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P13))

(assert (! (or (Btwn$0 next$0 x$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_14$0 next$0 x$0 null$0))) :named P14))

(assert (! (= FP_1$0 (setminus$0 FP$0 (setenum$0 x$0))) :named P15))

(assert (! (= n1_2$0 (read$0 next$0 x$0)) :named P16))

(assert (! (= sk_?X_14$0 FP$0) :named P17))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P18))

(assert (! (= sk_?X_15$0 (lseg_domain$0 next$0 n1_2$0 null$0)) :named P19))

(assert (! (or (and (in$0 sk_?e_3$0 sk_FP_1$0) (not (in$0 sk_?e_3$0 FP_1$0)))
    (not (Btwn$0 next$0 n1_2$0 null$0 null$0))) :named P20))

(assert (! (not (in$0 null$0 Alloc$0)) :named P21))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 n1_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 n1_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 n1_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 n1_2$0 null$0)))))) :named P22))

(assert (! (or (Btwn$0 next$0 n1_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_15$0 next$0 n1_2$0 null$0))) :named P23))

(assert (! (= Alloc_1$0 (setminus$0 Alloc$0 (setenum$0 x$0))) :named P24))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P25))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P26))

(assert (! (= sk_?X_14$0 (lseg_domain$0 next$0 x$0 null$0)) :named P27))

(assert (! (lseg_struct$0 sk_?X_14$0 next$0 x$0 null$0) :named P28))

(assert (! (= sk_FP_1$0 sk_?X_15$0) :named P29))

(assert (! (not (= x$0 null$0)) :named P30))

(assert (! (not nondet_1$0) :named P31))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 x$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 x$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 x$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 x$0 null$0)))))) :named P32))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P33))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P34))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P35))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P36))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P37))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P38))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P39))

(check-sat)

(get-interpolants (and P35 P15 P1 P10 P14 P18 P23 P21 P4 P24 P8 P2 P7 P22 P34 P3 P26 P32 P13 P12) (and P38 P11 P6 P17 P31 P25 P30 P16 P39 P36 P5 P27 P19 P29 P0 P33 P20 P9 P37 P28))

(exit)