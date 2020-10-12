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
  tests/spl/union_find.spl:20:4-18:Possible heap access through null or dangling reference
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Frame$0 (SetLoc SetLoc FldLoc FldLoc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Axiom$0 () Bool)
(declare-fun Axiom_1$0 () Bool)
(declare-fun Axiom_2$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_3$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun X$0 () SetLoc)
(declare-fun X_27$0 () SetLoc)
(declare-fun lseg_set_X$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_struct$0 (SetLoc FldLoc Loc Loc SetLoc) Bool)
(declare-fun n_5$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_2$0 () FldLoc)
(declare-fun res_4$0 () Loc)
(declare-fun root_x$0 () Loc)
(declare-fun sk_?X_14$0 () SetLoc)
(declare-fun sk_?X_15$0 () SetLoc)
(declare-fun sk_?X_16$0 () SetLoc)
(declare-fun sk_?X_17$0 () SetLoc)
(declare-fun sk_?X_18$0 () SetLoc)
(declare-fun sk_?X_19$0 () SetLoc)
(declare-fun sk_?X_20$0 () SetLoc)
(declare-fun sk_?X_21$0 () SetLoc)
(declare-fun sk_?X_22$0 () SetLoc)
(declare-fun sk_?X_23$0 () SetLoc)
(declare-fun sk_?X_24$0 () SetLoc)
(declare-fun sk_?X_25$0 () SetLoc)
(declare-fun sk_?X_26$0 () SetLoc)
(declare-fun sk_?X_27$0 () SetLoc)
(declare-fun x$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 res_4$0 ?y ?y)) (= res_4$0 ?y)
            (Btwn$0 next$0 res_4$0 (read$0 next$0 res_4$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 x$0 ?y ?y)) (= x$0 ?y)
            (Btwn$0 next$0 x$0 (read$0 next$0 x$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 res_4$0 ?y ?y)) (= res_4$0 ?y)
            (Btwn$0 next_2$0 res_4$0 (read$0 next_2$0 res_4$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_2$0 null$0 (read$0 next_2$0 null$0) ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 x$0 ?y ?y)) (= x$0 ?y)
            (Btwn$0 next_2$0 x$0 (read$0 next_2$0 x$0) ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 res_4$0) res_4$0))
            (not (Btwn$0 next$0 res_4$0 ?y ?y)) (= res_4$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P7))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 x$0) x$0)) (not (Btwn$0 next$0 x$0 ?y ?y))
            (= x$0 ?y))) :named P8))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 res_4$0) res_4$0))
            (not (Btwn$0 next_2$0 res_4$0 ?y ?y)) (= res_4$0 ?y))) :named P9))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 null$0) null$0))
            (not (Btwn$0 next_2$0 null$0 ?y ?y)) (= null$0 ?y))) :named P10))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 x$0) x$0))
            (not (Btwn$0 next_2$0 x$0 ?y ?y)) (= x$0 ?y))) :named P11))

(assert (! (Btwn$0 next$0 res_4$0 (read$0 next$0 res_4$0) (read$0 next$0 res_4$0)) :named P12))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P13))

(assert (! (Btwn$0 next$0 x$0 (read$0 next$0 x$0) (read$0 next$0 x$0)) :named P14))

(assert (! (Btwn$0 next_2$0 res_4$0 (read$0 next_2$0 res_4$0) (read$0 next_2$0 res_4$0)) :named P15))

(assert (! (Btwn$0 next_2$0 null$0 (read$0 next_2$0 null$0) (read$0 next_2$0 null$0)) :named P16))

(assert (! (Btwn$0 next_2$0 x$0 (read$0 next_2$0 x$0) (read$0 next_2$0 x$0)) :named P17))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 next$0 res_4$0) (read$0 next_2$0 res_4$0))
        (not (in$0 res_4$0 (setminus$0 Alloc$0 FP_2$0))))) :named P18))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 next$0 null$0) (read$0 next_2$0 null$0))
        (not (in$0 null$0 (setminus$0 Alloc$0 FP_2$0))))) :named P19))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 next$0 x$0) (read$0 next_2$0 x$0))
        (not (in$0 x$0 (setminus$0 Alloc$0 FP_2$0))))) :named P20))

(assert (! (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_2$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_2$0 null$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 null$0 ?y
                           (ep$0 next$0 FP_2$0 null$0))
                         (and (Btwn$0 next$0 null$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 null$0
                                     (ep$0 next$0 FP_2$0 null$0)
                                     (ep$0 next$0 FP_2$0 null$0))))))))) :named P21))

(assert (! (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 n_5$0 ?z ?y)
                     (Btwn$0 next_2$0 n_5$0 ?z ?y))
                (and (not (Btwn$0 next$0 n_5$0 ?z ?y))
                     (not (Btwn$0 next_2$0 n_5$0 ?z ?y)))
                (not
                     (or (Btwn$0 next$0 n_5$0 ?y (ep$0 next$0 FP_2$0 n_5$0))
                         (and (Btwn$0 next$0 n_5$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 n_5$0
                                     (ep$0 next$0 FP_2$0 n_5$0)
                                     (ep$0 next$0 FP_2$0 n_5$0))))))))) :named P22))

(assert (! (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or (and (Btwn$0 next$0 x$0 ?z ?y) (Btwn$0 next_2$0 x$0 ?z ?y))
                (and (not (Btwn$0 next$0 x$0 ?z ?y))
                     (not (Btwn$0 next_2$0 x$0 ?z ?y)))
                (not
                     (or (Btwn$0 next$0 x$0 ?y (ep$0 next$0 FP_2$0 x$0))
                         (and (Btwn$0 next$0 x$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 x$0
                                     (ep$0 next$0 FP_2$0 x$0)
                                     (ep$0 next$0 FP_2$0 x$0))))))))) :named P23))

(assert (! (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 null$0 FP_2$0)
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_2$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_2$0 null$0 ?z ?y)))
                (not (= null$0 (ep$0 next$0 FP_2$0 null$0)))))) :named P24))

(assert (! (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 n_5$0 FP_2$0)
                (and (Btwn$0 next$0 n_5$0 ?z ?y)
                     (Btwn$0 next_2$0 n_5$0 ?z ?y))
                (and (not (Btwn$0 next$0 n_5$0 ?z ?y))
                     (not (Btwn$0 next_2$0 n_5$0 ?z ?y)))
                (not (= n_5$0 (ep$0 next$0 FP_2$0 n_5$0)))))) :named P25))

(assert (! (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 x$0 FP_2$0)
                (and (Btwn$0 next$0 x$0 ?z ?y) (Btwn$0 next_2$0 x$0 ?z ?y))
                (and (not (Btwn$0 next$0 x$0 ?z ?y))
                     (not (Btwn$0 next_2$0 x$0 ?z ?y)))
                (not (= x$0 (ep$0 next$0 FP_2$0 x$0)))))) :named P26))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_24$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y sk_?X_24$0)))) :named P27))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 n_5$0 (ep$0 next$0 sk_?X_24$0 n_5$0) ?y)
            (not (Btwn$0 next$0 n_5$0 ?y ?y)) (not (in$0 ?y sk_?X_24$0)))) :named P28))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 x$0 (ep$0 next$0 sk_?X_24$0 x$0) ?y)
            (not (Btwn$0 next$0 x$0 ?y ?y)) (not (in$0 ?y sk_?X_24$0)))) :named P29))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_24$0 null$0) sk_?X_24$0)
    (= null$0 (ep$0 next$0 sk_?X_24$0 null$0))) :named P30))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_24$0 n_5$0) sk_?X_24$0)
    (= n_5$0 (ep$0 next$0 sk_?X_24$0 n_5$0))) :named P31))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_24$0 x$0) sk_?X_24$0)
    (= x$0 (ep$0 next$0 sk_?X_24$0 x$0))) :named P32))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_24$0 null$0)
  (ep$0 next$0 sk_?X_24$0 null$0)) :named P33))

(assert (! (Btwn$0 next$0 n_5$0 (ep$0 next$0 sk_?X_24$0 n_5$0)
  (ep$0 next$0 sk_?X_24$0 n_5$0)) :named P34))

(assert (! (Btwn$0 next$0 x$0 (ep$0 next$0 sk_?X_24$0 x$0) (ep$0 next$0 sk_?X_24$0 x$0)) :named P35))

(assert (! (or (= (read$0 next_2$0 res_4$0) root_x$0) (not (in$0 res_4$0 X_27$0))) :named P36))

(assert (! (or (= (read$0 next_2$0 null$0) root_x$0) (not (in$0 null$0 X_27$0))) :named P37))

(assert (! (or (= (read$0 next_2$0 x$0) root_x$0) (not (in$0 x$0 X_27$0))) :named P38))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P39))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_3$0 Alloc$0))
                 (or (in$0 x FP_3$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_3$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_3$0 Alloc$0)))))) :named P40))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_24$0 FP$0))
                 (or (in$0 x sk_?X_24$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_24$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_24$0 FP$0)))))) :named P41))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_23$0 sk_?X_15$0))
                 (or (in$0 x sk_?X_23$0) (in$0 x sk_?X_15$0)))
            (and (not (in$0 x sk_?X_23$0)) (not (in$0 x sk_?X_15$0))
                 (not (in$0 x (union$0 sk_?X_23$0 sk_?X_15$0)))))) :named P42))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_2$0) sk_?X_19$0))
                 (or (in$0 x (setminus$0 FP$0 FP_2$0)) (in$0 x sk_?X_19$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_2$0)))
                 (not (in$0 x sk_?X_19$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_2$0) sk_?X_19$0)))))) :named P43))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P44))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_14$0 sk_?X_15$0))
                 (or (in$0 x sk_?X_14$0) (in$0 x sk_?X_15$0)))
            (and (not (in$0 x sk_?X_14$0)) (not (in$0 x sk_?X_15$0))
                 (not (in$0 x (union$0 sk_?X_14$0 sk_?X_15$0)))))) :named P45))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_2$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_2$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_2$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_2$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P46))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_27$0 sk_?X_15$0))
                 (or (in$0 x sk_?X_27$0) (in$0 x sk_?X_15$0)))
            (and (not (in$0 x sk_?X_27$0)) (not (in$0 x sk_?X_15$0))
                 (not (in$0 x (union$0 sk_?X_27$0 sk_?X_15$0)))))) :named P47))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_27$0) (in$0 x sk_?X_15$0)
                 (in$0 x (intersection$0 sk_?X_27$0 sk_?X_15$0)))
            (and (or (not (in$0 x sk_?X_27$0)) (not (in$0 x sk_?X_15$0)))
                 (not (in$0 x (intersection$0 sk_?X_27$0 sk_?X_15$0)))))) :named P48))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_23$0) (in$0 x sk_?X_15$0)
                 (in$0 x (intersection$0 sk_?X_23$0 sk_?X_15$0)))
            (and (or (not (in$0 x sk_?X_23$0)) (not (in$0 x sk_?X_15$0)))
                 (not (in$0 x (intersection$0 sk_?X_23$0 sk_?X_15$0)))))) :named P49))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_14$0) (in$0 x sk_?X_15$0)
                 (in$0 x (intersection$0 sk_?X_14$0 sk_?X_15$0)))
            (and (or (not (in$0 x sk_?X_14$0)) (not (in$0 x sk_?X_15$0)))
                 (not (in$0 x (intersection$0 sk_?X_14$0 sk_?X_15$0)))))) :named P50))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_24$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_24$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_24$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_24$0)))))) :named P51))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P52))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 sk_?X_24$0))
                 (not (in$0 x sk_?X_24$0)))
            (and (or (in$0 x sk_?X_24$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 sk_?X_24$0)))))) :named P53))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 sk_?X_24$0))
                 (not (in$0 x sk_?X_24$0)))
            (and (or (in$0 x sk_?X_24$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 sk_?X_24$0)))))) :named P54))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P55))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P56))

(assert (! (= (read$0 next$0 null$0) null$0) :named P57))

(assert (! (= (read$0 next_2$0 null$0) null$0) :named P58))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P59))

(assert (! (or (Btwn$0 next$0 n_5$0 root_x$0 root_x$0)
    (not (lseg_set_struct$0 sk_?X_27$0 next$0 n_5$0 root_x$0 X_27$0))) :named P60))

(assert (! (= FP_3$0
  (union$0 (setminus$0 FP$0 FP_2$0)
    (union$0 (intersection$0 Alloc$0 FP_2$0) (setminus$0 Alloc$0 Alloc$0)))) :named P61))

(assert (! (= n_5$0 (read$0 next$0 x$0)) :named P62))

(assert (! (= Alloc$0 (union$0 FP_3$0 Alloc$0)) :named P63))

(assert (! (= (read$0 next$0 root_x$0) null$0) :named P64))

(assert (! (= emptyset$0 (intersection$0 sk_?X_23$0 sk_?X_21$0)) :named P65))

(assert (! (= sk_?X_20$0 (union$0 sk_?X_23$0 sk_?X_21$0)) :named P66))

(assert (! (= sk_?X_21$0 sk_?X_22$0) :named P67))

(assert (! (= sk_?X_23$0 (lseg_set_domain$0 next$0 x$0 root_x$0)) :named P68))

(assert (! (lseg_set_struct$0 sk_?X_23$0 next$0 x$0 root_x$0 X$0) :named P69))

(assert (! (= emptyset$0 emptyset$0) :named P70))

(assert (! (= X_27$0 (lseg_set_X$0 next$0 n_5$0 root_x$0)) :named P71))

(assert (! (= sk_?X_24$0 FP_2$0) :named P72))

(assert (! (= sk_?X_26$0 (setenum$0 root_x$0)) :named P73))

(assert (! (= FP$0 (union$0 FP_2$0 FP$0)) :named P74))

(assert (! (= (read$0 next_2$0 root_x$0) null$0) :named P75))

(assert (! (= emptyset$0 (intersection$0 sk_?X_14$0 sk_?X_16$0)) :named P76))

(assert (! (= sk_?X_14$0 X_27$0) :named P77))

(assert (! (= sk_?X_16$0 sk_?X_15$0) :named P78))

(assert (! (= sk_?X_18$0 sk_?X_17$0) :named P79))

(assert (! (= sk_?X_19$0 sk_?X_18$0) :named P80))

(assert (! (not (= n_5$0 null$0)) :named P81))

(assert (! (not (in$0 null$0 Alloc$0)) :named P82))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 n_5$0 l1 root_x$0)
                 (in$0 l1 (lseg_set_X$0 next$0 n_5$0 root_x$0))
                 (not (= l1 root_x$0)))
            (and (or (= l1 root_x$0) (not (Btwn$0 next$0 n_5$0 l1 root_x$0)))
                 (not (in$0 l1 (lseg_set_X$0 next$0 n_5$0 root_x$0)))))) :named P83))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 x$0 l1 root_x$0)
                 (in$0 l1 (lseg_set_X$0 next$0 x$0 root_x$0))
                 (not (= l1 root_x$0)))
            (and (or (= l1 root_x$0) (not (Btwn$0 next$0 x$0 l1 root_x$0)))
                 (not (in$0 l1 (lseg_set_X$0 next$0 x$0 root_x$0)))))) :named P84))

(assert (! (or (and Axiom_2$0 Axiom_1$0 Axiom$0)
    (not (Frame$0 FP_2$0 Alloc$0 next$0 next_2$0))) :named P85))

(assert (! (or (Btwn$0 next$0 x$0 root_x$0 root_x$0)
    (not (lseg_set_struct$0 sk_?X_23$0 next$0 x$0 root_x$0 X$0))) :named P86))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P87))

(assert (! (Frame$0 FP_2$0 Alloc$0 next$0 next_2$0) :named P88))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P89))

(assert (! (= emptyset$0 emptyset$0) :named P90))

(assert (! (= X$0 (lseg_set_X$0 next$0 x$0 root_x$0)) :named P91))

(assert (! (= sk_?X_20$0 FP$0) :named P92))

(assert (! (= sk_?X_22$0 (setenum$0 root_x$0)) :named P93))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P94))

(assert (! (= (read$0 next$0 root_x$0) null$0) :named P95))

(assert (! (= emptyset$0 (intersection$0 sk_?X_27$0 sk_?X_25$0)) :named P96))

(assert (! (= sk_?X_24$0 (union$0 sk_?X_27$0 sk_?X_25$0)) :named P97))

(assert (! (= sk_?X_25$0 sk_?X_26$0) :named P98))

(assert (! (= sk_?X_27$0 (lseg_set_domain$0 next$0 n_5$0 root_x$0)) :named P99))

(assert (! (lseg_set_struct$0 sk_?X_27$0 next$0 n_5$0 root_x$0 X_27$0) :named P100))

(assert (! (= emptyset$0 emptyset$0) :named P101))

(assert (! (= res_4$0 root_x$0) :named P102))

(assert (! (= sk_?X_15$0 (setenum$0 root_x$0)) :named P103))

(assert (! (= sk_?X_17$0 (union$0 sk_?X_14$0 sk_?X_16$0)) :named P104))

(assert (! (= sk_?X_19$0
  (union$0 (intersection$0 Alloc$0 FP_2$0) (setminus$0 Alloc$0 Alloc$0))) :named P105))

(assert (! (not (in$0 null$0 Alloc$0)) :named P106))

(assert (! (not (in$0 x$0 FP_3$0)) :named P107))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 n_5$0 l1 root_x$0)
                 (in$0 l1 (lseg_set_domain$0 next$0 n_5$0 root_x$0))
                 (not (= l1 root_x$0)))
            (and (or (= l1 root_x$0) (not (Btwn$0 next$0 n_5$0 l1 root_x$0)))
                 (not (in$0 l1 (lseg_set_domain$0 next$0 n_5$0 root_x$0)))))) :named P108))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 x$0 l1 root_x$0)
                 (in$0 l1 (lseg_set_domain$0 next$0 x$0 root_x$0))
                 (not (= l1 root_x$0)))
            (and (or (= l1 root_x$0) (not (Btwn$0 next$0 x$0 l1 root_x$0)))
                 (not (in$0 l1 (lseg_set_domain$0 next$0 x$0 root_x$0)))))) :named P109))

(assert (! (forall ((?x Loc)) (Btwn$0 next_2$0 ?x ?x ?x)) :named P110))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P111))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_2$0 ?x ?y ?x)) (= ?x ?y))) :named P112))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P113))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?y)) (not (Btwn$0 next_2$0 ?x ?z ?z))
            (Btwn$0 next_2$0 ?x ?y ?z) (Btwn$0 next_2$0 ?x ?z ?y))) :named P114))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P115))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z))
            (and (Btwn$0 next_2$0 ?x ?y ?y) (Btwn$0 next_2$0 ?y ?z ?z)))) :named P116))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P117))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?y)) (not (Btwn$0 next_2$0 ?y ?z ?z))
            (Btwn$0 next_2$0 ?x ?z ?z))) :named P118))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P119))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z)) (not (Btwn$0 next_2$0 ?y ?u ?z))
            (and (Btwn$0 next_2$0 ?x ?y ?u) (Btwn$0 next_2$0 ?x ?u ?z)))) :named P120))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P121))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z)) (not (Btwn$0 next_2$0 ?x ?u ?y))
            (and (Btwn$0 next_2$0 ?x ?u ?z) (Btwn$0 next_2$0 ?u ?y ?z)))) :named P122))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P123))

(check-sat)

(get-interpolants (and P28 P73 P24 P115 P91 P90 P86 P64 P30 P71 P95 P106 P109 P19 P62 P32 P52 P4 P13 P118 P33 P104 P80 P101 P34 P123 P18 P103 P111 P75 P83 P40 P56 P39 P116 P55 P77 P120 P113 P93 P70 P5 P68 P15 P78 P17 P26 P9 P46 P25 P6 P14 P53 P12 P114 P20 P41 P10 P43 P0 P81 P50) (and P92 P16 P87 P3 P122 P2 P107 P1 P8 P100 P63 P102 P22 P59 P96 P21 P38 P97 P54 P44 P35 P121 P69 P82 P105 P57 P112 P79 P23 P74 P76 P66 P48 P65 P31 P88 P99 P37 P11 P61 P119 P89 P47 P27 P7 P36 P98 P94 P45 P58 P72 P117 P51 P110 P29 P67 P49 P85 P60 P108 P84 P42))

(exit)