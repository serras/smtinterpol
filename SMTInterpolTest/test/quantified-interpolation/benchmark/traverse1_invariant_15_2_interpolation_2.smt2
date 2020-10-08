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
  tests/spl/sl/sl_traverse.spl:15:2:An invariant might not hold before entering a loop in procedure traverse1
  tests/spl/sl/sl_traverse.spl:16:14:Related location: This is the loop invariant that might not hold initially
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
(declare-fun curr_3$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun sk_?X$0 () SetLoc)
(declare-fun sk_?X_1$0 () SetLoc)
(declare-fun sk_?X_2$0 () SetLoc)
(declare-fun sk_?X_3$0 () SetLoc)
(declare-fun sk_?e$0 () Loc)
(declare-fun sk_FP$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P1))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P2))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P3))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P4))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_3$0 FP$0))
                 (or (in$0 x sk_?X_3$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_3$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_3$0 FP$0)))))) :named P5))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_3$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 sk_?X_3$0 FP$0)))
            (and (or (not (in$0 x sk_?X_3$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 sk_?X_3$0 FP$0)))))) :named P6))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P7))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P8))

(assert (! (= (read$0 next$0 null$0) null$0) :named P9))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P10))

(assert (! (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X$0 next$0 lst$0 null$0))) :named P11))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P12))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P13))

(assert (! (= sk_?X$0 (lseg_domain$0 next$0 lst$0 null$0)) :named P14))

(assert (! (lseg_struct$0 sk_?X$0 next$0 lst$0 null$0) :named P15))

(assert (! (= sk_?X_2$0 (lseg_domain$0 next$0 curr_3$0 null$0)) :named P16))

(assert (! (= sk_FP$0 sk_?X_1$0) :named P17))

(assert (! (not (in$0 null$0 Alloc$0)) :named P18))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0)))))) :named P19))

(assert (! (or (Btwn$0 next$0 curr_3$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_2$0 next$0 curr_3$0 null$0))) :named P20))

(assert (! (or (Btwn$0 next$0 lst$0 curr_3$0 curr_3$0)
    (not (lseg_struct$0 sk_?X_3$0 next$0 lst$0 curr_3$0))) :named P21))

(assert (! (= curr_3$0 lst$0) :named P22))

(assert (! (= sk_?X$0 FP$0) :named P23))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P24))

(assert (! (= sk_?X_1$0 (union$0 sk_?X_3$0 sk_?X_2$0)) :named P25))

(assert (! (= sk_?X_3$0 (lseg_domain$0 next$0 lst$0 curr_3$0)) :named P26))

(assert (! (or (in$0 sk_?e$0 (intersection$0 sk_?X_3$0 sk_?X_2$0))
    (and (in$0 sk_?e$0 sk_FP$0) (not (in$0 sk_?e$0 FP$0)))
    (not (Btwn$0 next$0 curr_3$0 null$0 null$0))
    (not (Btwn$0 next$0 lst$0 curr_3$0 curr_3$0))) :named P27))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_3$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_3$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_3$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_3$0 null$0)))))) :named P28))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 curr_3$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 curr_3$0))
                 (not (= l1 curr_3$0)))
            (and (or (= l1 curr_3$0) (not (Btwn$0 next$0 lst$0 l1 curr_3$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 curr_3$0)))))) :named P29))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P30))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P31))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P32))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P33))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P34))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P35))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P36))

(check-sat)

(get-interpolants (and P14 P34 P8 P22 P12 P21 P7 P18 P36 P20 P0 P16 P23 P17 P35 P3 P4 P10 P9) (and P31 P15 P28 P19 P24 P25 P29 P33 P2 P32 P30 P6 P13 P5 P1 P27 P11 P26))

(exit)