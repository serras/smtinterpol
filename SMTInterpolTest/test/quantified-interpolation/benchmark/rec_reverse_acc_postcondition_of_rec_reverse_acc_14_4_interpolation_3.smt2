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
  tests/spl/sl/rec_reverse.spl:14:4-15:A postcondition of procedure rec_reverse_acc might not hold at this return point
  tests/spl/sl/rec_reverse.spl:11:10-25:Related location: This is the postcondition that might not hold
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
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun FP_Caller_final_4$0 () SetLoc)
(declare-fun curr$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun res_6$0 () Loc)
(declare-fun rev$0 () Loc)
(declare-fun sk_?X_16$0 () SetLoc)
(declare-fun sk_?X_17$0 () SetLoc)
(declare-fun sk_?X_18$0 () SetLoc)
(declare-fun sk_?X_19$0 () SetLoc)
(declare-fun sk_?e_2$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr$0 ?y ?y)) (= curr$0 ?y)
            (Btwn$0 next$0 curr$0 (read$0 next$0 curr$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr$0) curr$0))
            (not (Btwn$0 next$0 curr$0 ?y ?y)) (= curr$0 ?y))) :named P1))

(assert (! (Btwn$0 next$0 curr$0 (read$0 next$0 curr$0) (read$0 next$0 curr$0)) :named P2))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P3))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_18$0 sk_?X_17$0))
                 (or (in$0 x sk_?X_18$0) (in$0 x sk_?X_17$0)))
            (and (not (in$0 x sk_?X_18$0)) (not (in$0 x sk_?X_17$0))
                 (not (in$0 x (union$0 sk_?X_18$0 sk_?X_17$0)))))) :named P4))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P5))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_2$0 FP$0))
                 (or (in$0 x FP_Caller_2$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_Caller_2$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_Caller_2$0 FP$0)))))) :named P6))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P7))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_18$0) (in$0 x sk_?X_17$0)
                 (in$0 x (intersection$0 sk_?X_18$0 sk_?X_17$0)))
            (and (or (not (in$0 x sk_?X_18$0)) (not (in$0 x sk_?X_17$0)))
                 (not (in$0 x (intersection$0 sk_?X_18$0 sk_?X_17$0)))))) :named P8))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 Alloc$0 FP$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP$0)))))) :named P9))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P10))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P11))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P12))

(assert (! (= (read$0 next$0 null$0) null$0) :named P13))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P14))

(assert (! (or (Btwn$0 next$0 curr$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_17$0 next$0 curr$0 null$0))) :named P15))

(assert (! (or (Btwn$0 next$0 rev$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_18$0 next$0 rev$0 null$0))) :named P16))

(assert (! (= FP_Caller_final_4$0 (union$0 FP_Caller_2$0 FP$0)) :named P17))

(assert (! (= res_6$0 rev$0) :named P18))

(assert (! (= emptyset$0 (intersection$0 sk_?X_18$0 sk_?X_17$0)) :named P19))

(assert (! (= sk_?X_16$0 FP$0) :named P20))

(assert (! (= sk_?X_18$0 (lseg_domain$0 next$0 rev$0 null$0)) :named P21))

(assert (! (lseg_struct$0 sk_?X_17$0 next$0 curr$0 null$0) :named P22))

(assert (! (= sk_?X_19$0
  (union$0 (intersection$0 Alloc$0 FP$0) (setminus$0 Alloc$0 Alloc$0))) :named P23))

(assert (! (not (in$0 null$0 Alloc$0)) :named P24))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 res_6$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 res_6$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 res_6$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 res_6$0 null$0)))))) :named P25))

(assert (! (or (Btwn$0 next$0 res_6$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_19$0 next$0 res_6$0 null$0))) :named P26))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P27))

(assert (! (= curr$0 null$0) :named P28))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P29))

(assert (! (= sk_?X_16$0 (union$0 sk_?X_18$0 sk_?X_17$0)) :named P30))

(assert (! (= sk_?X_17$0 (lseg_domain$0 next$0 curr$0 null$0)) :named P31))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P32))

(assert (! (lseg_struct$0 sk_?X_18$0 next$0 rev$0 null$0) :named P33))

(assert (! (or
    (and (in$0 sk_?e_2$0 (lseg_domain$0 next$0 res_6$0 null$0))
         (not (in$0 sk_?e_2$0 sk_?X_19$0)))
    (and (in$0 sk_?e_2$0 sk_?X_19$0)
         (not (in$0 sk_?e_2$0 (lseg_domain$0 next$0 res_6$0 null$0))))
    (not (Btwn$0 next$0 res_6$0 null$0 null$0))) :named P34))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr$0 null$0)))))) :named P35))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 rev$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 rev$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 rev$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 rev$0 null$0)))))) :named P36))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P37))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P38))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P39))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P40))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P41))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P42))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P43))

(check-sat)

(get-interpolants (and P4 P24 P6 P28 P34 P0 P43 P2 P1 P19 P37 P29 P7 P42 P20 P8 P17 P38 P9 P10 P35 P18) (and P40 P31 P30 P21 P25 P11 P13 P32 P16 P23 P26 P15 P5 P14 P3 P36 P39 P22 P12 P27 P41 P33))

(exit)