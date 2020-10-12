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
  tests/spl/sl/sl_dispose.spl:20:3-4:An invariant might not be maintained by a loop in procedure dispose
  tests/spl/sl/sl_dispose.spl:14:14-29:Related location: This is the loop invariant that might not be maintained
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
(declare-fun Alloc_2$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_3$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun curr_2$0 () Loc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst_2$0 () Loc)
(declare-fun lst_3$0 () Loc)
(declare-fun lst_init$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun sk_?X_7$0 () SetLoc)
(declare-fun sk_?X_8$0 () SetLoc)
(declare-fun sk_?e_2$0 () Loc)
(declare-fun sk_FP_1$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 lst_2$0 ?y ?y)) (= lst_2$0 ?y)
            (Btwn$0 next$0 lst_2$0 (read$0 next$0 lst_2$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 lst_2$0) lst_2$0))
            (not (Btwn$0 next$0 lst_2$0 ?y ?y)) (= lst_2$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P4))

(assert (! (Btwn$0 next$0 lst_2$0 (read$0 next$0 lst_2$0) (read$0 next$0 lst_2$0)) :named P5))

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
                 (in$0 x (setminus$0 Alloc$0 (setenum$0 curr_4$0)))
                 (not (in$0 x (setenum$0 curr_4$0))))
            (and (or (in$0 x (setenum$0 curr_4$0)) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 (setenum$0 curr_4$0))))))) :named P8))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0)
                 (in$0 x (setminus$0 FP$0 (setenum$0 curr_4$0)))
                 (not (in$0 x (setenum$0 curr_4$0))))
            (and (or (in$0 x (setenum$0 curr_4$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 (setenum$0 curr_4$0))))))) :named P9))

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

(assert (! (or (Btwn$0 next$0 lst_init$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_7$0 next$0 lst_init$0 null$0))) :named P14))

(assert (! (= FP_3$0 (setminus$0 FP$0 (setenum$0 curr_4$0))) :named P15))

(assert (! (= curr_2$0 curr_init$0) :named P16))

(assert (! (= lst_2$0 lst_init$0) :named P17))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P18))

(assert (! (= sk_?X_7$0 (lseg_domain$0 next$0 lst_init$0 null$0)) :named P19))

(assert (! (lseg_struct$0 sk_?X_7$0 next$0 lst_init$0 null$0) :named P20))

(assert (! (= sk_FP_1$0 sk_?X_8$0) :named P21))

(assert (! (not (= lst_2$0 null$0)) :named P22))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst_3$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst_3$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst_3$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst_3$0 null$0)))))) :named P23))

(assert (! (or (Btwn$0 next$0 lst_3$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_8$0 next$0 lst_3$0 null$0))) :named P24))

(assert (! (= Alloc_2$0 (setminus$0 Alloc$0 (setenum$0 curr_4$0))) :named P25))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P26))

(assert (! (= curr_4$0 lst_2$0) :named P27))

(assert (! (= lst_3$0 (read$0 next$0 lst_2$0)) :named P28))

(assert (! (= sk_?X_7$0 FP$0) :named P29))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P30))

(assert (! (= sk_?X_8$0 (lseg_domain$0 next$0 lst_3$0 null$0)) :named P31))

(assert (! (or (and (in$0 sk_?e_2$0 sk_FP_1$0) (not (in$0 sk_?e_2$0 FP_3$0)))
    (not (Btwn$0 next$0 lst_3$0 null$0 null$0))) :named P32))

(assert (! (not (in$0 null$0 Alloc$0)) :named P33))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst_init$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst_init$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 lst_init$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst_init$0 null$0)))))) :named P34))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P35))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P36))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P37))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P38))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P39))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P40))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P41))

(check-sat)

(get-interpolants (and P0 P14 P23 P21 P9 P19 P39 P36 P35 P24 P41 P15 P1 P32 P10 P17 P37 P13 P38 P18 P34) (and P28 P6 P20 P31 P4 P8 P25 P22 P33 P2 P12 P11 P5 P16 P29 P27 P7 P40 P26 P30 P3))

(exit)