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
  tests/spl/sl/rec_copy.spl:53:2-34:A postcondition of procedure rec_copy might not hold at this return point
  tests/spl/sl/rec_copy.spl:51:10-45:Related location: This is the postcondition that might not hold
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
(declare-fun Alloc_1$0 () SetLoc)
(declare-fun Axiom$0 () Bool)
(declare-fun Axiom_1$0 () Bool)
(declare-fun Axiom_2$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun FP_Caller_final_1$0 () SetLoc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_1$0 () FldLoc)
(declare-fun res_4$0 () Loc)
(declare-fun res_5$0 () Loc)
(declare-fun sk_?X_4$0 () SetLoc)
(declare-fun sk_?X_5$0 () SetLoc)
(declare-fun sk_?X_6$0 () SetLoc)
(declare-fun sk_?X_7$0 () SetLoc)
(declare-fun sk_?X_8$0 () SetLoc)
(declare-fun sk_?X_9$0 () SetLoc)
(declare-fun sk_?X_10$0 () SetLoc)
(declare-fun sk_?X_11$0 () SetLoc)
(declare-fun sk_?X_12$0 () SetLoc)
(declare-fun sk_?X_13$0 () SetLoc)
(declare-fun sk_?e_1$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_1$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_1$0 null$0 (read$0 next_1$0 null$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_1$0 null$0) null$0))
            (not (Btwn$0 next_1$0 null$0 ?y ?y)) (= null$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P4))

(assert (! (Btwn$0 next_1$0 null$0 (read$0 next_1$0 null$0) (read$0 next_1$0 null$0)) :named P5))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 next$0 null$0) (read$0 next_1$0 null$0))
        (not (in$0 null$0 (setminus$0 Alloc$0 FP_1$0))))) :named P6))

(assert (! (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_1$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_1$0 null$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 null$0 ?y
                           (ep$0 next$0 FP_1$0 null$0))
                         (and (Btwn$0 next$0 null$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 null$0
                                     (ep$0 next$0 FP_1$0 null$0)
                                     (ep$0 next$0 FP_1$0 null$0))))))))) :named P7))

(assert (! (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 lst$0 ?z ?y)
                     (Btwn$0 next_1$0 lst$0 ?z ?y))
                (and (not (Btwn$0 next$0 lst$0 ?z ?y))
                     (not (Btwn$0 next_1$0 lst$0 ?z ?y)))
                (not
                     (or (Btwn$0 next$0 lst$0 ?y (ep$0 next$0 FP_1$0 lst$0))
                         (and (Btwn$0 next$0 lst$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 lst$0
                                     (ep$0 next$0 FP_1$0 lst$0)
                                     (ep$0 next$0 FP_1$0 lst$0))))))))) :named P8))

(assert (! (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 res_5$0 ?z ?y)
                     (Btwn$0 next_1$0 res_5$0 ?z ?y))
                (and (not (Btwn$0 next$0 res_5$0 ?z ?y))
                     (not (Btwn$0 next_1$0 res_5$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 res_5$0 ?y
                           (ep$0 next$0 FP_1$0 res_5$0))
                         (and (Btwn$0 next$0 res_5$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 res_5$0
                                     (ep$0 next$0 FP_1$0 res_5$0)
                                     (ep$0 next$0 FP_1$0 res_5$0))))))))) :named P9))

(assert (! (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 sk_?e_1$0 ?z ?y)
                     (Btwn$0 next_1$0 sk_?e_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_?e_1$0 ?z ?y))
                     (not (Btwn$0 next_1$0 sk_?e_1$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 sk_?e_1$0 ?y
                           (ep$0 next$0 FP_1$0 sk_?e_1$0))
                         (and (Btwn$0 next$0 sk_?e_1$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 sk_?e_1$0
                                     (ep$0 next$0 FP_1$0 sk_?e_1$0)
                                     (ep$0 next$0 FP_1$0 sk_?e_1$0))))))))) :named P10))

(assert (! (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 null$0 FP_1$0)
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_1$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_1$0 null$0 ?z ?y)))
                (not (= null$0 (ep$0 next$0 FP_1$0 null$0)))))) :named P11))

(assert (! (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 lst$0 FP_1$0)
                (and (Btwn$0 next$0 lst$0 ?z ?y)
                     (Btwn$0 next_1$0 lst$0 ?z ?y))
                (and (not (Btwn$0 next$0 lst$0 ?z ?y))
                     (not (Btwn$0 next_1$0 lst$0 ?z ?y)))
                (not (= lst$0 (ep$0 next$0 FP_1$0 lst$0)))))) :named P12))

(assert (! (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 res_5$0 FP_1$0)
                (and (Btwn$0 next$0 res_5$0 ?z ?y)
                     (Btwn$0 next_1$0 res_5$0 ?z ?y))
                (and (not (Btwn$0 next$0 res_5$0 ?z ?y))
                     (not (Btwn$0 next_1$0 res_5$0 ?z ?y)))
                (not (= res_5$0 (ep$0 next$0 FP_1$0 res_5$0)))))) :named P13))

(assert (! (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 sk_?e_1$0 FP_1$0)
                (and (Btwn$0 next$0 sk_?e_1$0 ?z ?y)
                     (Btwn$0 next_1$0 sk_?e_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_?e_1$0 ?z ?y))
                     (not (Btwn$0 next_1$0 sk_?e_1$0 ?z ?y)))
                (not (= sk_?e_1$0 (ep$0 next$0 FP_1$0 sk_?e_1$0)))))) :named P14))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 FP_1$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P15))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 lst$0 (ep$0 next$0 FP_1$0 lst$0) ?y)
            (not (Btwn$0 next$0 lst$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P16))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 res_5$0 (ep$0 next$0 FP_1$0 res_5$0) ?y)
            (not (Btwn$0 next$0 res_5$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P17))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_?e_1$0 (ep$0 next$0 FP_1$0 sk_?e_1$0) ?y)
            (not (Btwn$0 next$0 sk_?e_1$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P18))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 null$0) FP_1$0)
    (= null$0 (ep$0 next$0 FP_1$0 null$0))) :named P19))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 lst$0) FP_1$0)
    (= lst$0 (ep$0 next$0 FP_1$0 lst$0))) :named P20))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 res_5$0) FP_1$0)
    (= res_5$0 (ep$0 next$0 FP_1$0 res_5$0))) :named P21))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 sk_?e_1$0) FP_1$0)
    (= sk_?e_1$0 (ep$0 next$0 FP_1$0 sk_?e_1$0))) :named P22))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 FP_1$0 null$0)
  (ep$0 next$0 FP_1$0 null$0)) :named P23))

(assert (! (Btwn$0 next$0 lst$0 (ep$0 next$0 FP_1$0 lst$0) (ep$0 next$0 FP_1$0 lst$0)) :named P24))

(assert (! (Btwn$0 next$0 res_5$0 (ep$0 next$0 FP_1$0 res_5$0)
  (ep$0 next$0 FP_1$0 res_5$0)) :named P25))

(assert (! (Btwn$0 next$0 sk_?e_1$0 (ep$0 next$0 FP_1$0 sk_?e_1$0)
  (ep$0 next$0 FP_1$0 sk_?e_1$0)) :named P26))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc_1$0 FP$0)
                     (setminus$0 Alloc_1$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc_1$0 FP$0))
                     (in$0 x (setminus$0 Alloc_1$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc_1$0 FP$0)))
                 (not (in$0 x (setminus$0 Alloc_1$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc_1$0 FP$0)
                          (setminus$0 Alloc_1$0 Alloc$0))))))) :named P27))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P28))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc_1$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc_1$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc_1$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc_1$0)))))) :named P29))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_1$0 FP$0))
                 (or (in$0 x FP_1$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_1$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_1$0 FP$0)))))) :named P30))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_9$0 FP$0))
                 (or (in$0 x sk_?X_9$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_9$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_9$0 FP$0)))))) :named P31))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_6$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_6$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_6$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_6$0)))))) :named P32))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P33))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_1$0 FP_2$0))
                 (or (in$0 x FP_Caller_1$0) (in$0 x FP_2$0)))
            (and (not (in$0 x FP_Caller_1$0)) (not (in$0 x FP_2$0))
                 (not (in$0 x (union$0 FP_Caller_1$0 FP_2$0)))))) :named P34))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_12$0 sk_?X_11$0))
                 (or (in$0 x sk_?X_12$0) (in$0 x sk_?X_11$0)))
            (and (not (in$0 x sk_?X_12$0)) (not (in$0 x sk_?X_11$0))
                 (not (in$0 x (union$0 sk_?X_12$0 sk_?X_11$0)))))) :named P35))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc_1$0 FP_1$0)
                     (setminus$0 Alloc_1$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc_1$0 FP_1$0))
                     (in$0 x (setminus$0 Alloc_1$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc_1$0 FP_1$0)))
                 (not (in$0 x (setminus$0 Alloc_1$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc_1$0 FP_1$0)
                          (setminus$0 Alloc_1$0 Alloc$0))))))) :named P36))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_11$0 sk_?X_12$0))
                 (or (in$0 x sk_?X_11$0) (in$0 x sk_?X_12$0)))
            (and (not (in$0 x sk_?X_11$0)) (not (in$0 x sk_?X_12$0))
                 (not (in$0 x (union$0 sk_?X_11$0 sk_?X_12$0)))))) :named P37))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_12$0) (in$0 x sk_?X_11$0)
                 (in$0 x (intersection$0 sk_?X_12$0 sk_?X_11$0)))
            (and (or (not (in$0 x sk_?X_12$0)) (not (in$0 x sk_?X_11$0)))
                 (not (in$0 x (intersection$0 sk_?X_12$0 sk_?X_11$0)))))) :named P38))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_9$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 sk_?X_9$0 FP$0)))
            (and (or (not (in$0 x sk_?X_9$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 sk_?X_9$0 FP$0)))))) :named P39))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc_1$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 Alloc_1$0 FP$0)))
            (and (or (not (in$0 x Alloc_1$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 Alloc_1$0 FP$0)))))) :named P40))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc_1$0) (in$0 x FP_1$0)
                 (in$0 x (intersection$0 Alloc_1$0 FP_1$0)))
            (and (or (not (in$0 x Alloc_1$0)) (not (in$0 x FP_1$0)))
                 (not (in$0 x (intersection$0 Alloc_1$0 FP_1$0)))))) :named P41))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_11$0) (in$0 x sk_?X_12$0)
                 (in$0 x (intersection$0 sk_?X_11$0 sk_?X_12$0)))
            (and (or (not (in$0 x sk_?X_11$0)) (not (in$0 x sk_?X_12$0)))
                 (not (in$0 x (intersection$0 sk_?X_11$0 sk_?X_12$0)))))) :named P42))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 FP_1$0))
                 (not (in$0 x FP_1$0)))
            (and (or (in$0 x FP_1$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 FP_1$0)))))) :named P43))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc_1$0) (in$0 x (setminus$0 Alloc_1$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc_1$0)))
                 (not (in$0 x (setminus$0 Alloc_1$0 Alloc$0)))))) :named P44))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 FP_1$0))
                 (not (in$0 x FP_1$0)))
            (and (or (in$0 x FP_1$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 FP_1$0)))))) :named P45))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P46))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P47))

(assert (! (= (read$0 next$0 null$0) null$0) :named P48))

(assert (! (= (read$0 next_1$0 null$0) null$0) :named P49))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P50))

(assert (! (or (Btwn$0 next$0 null$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_9$0 next$0 null$0 null$0))) :named P51))

(assert (! (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_10$0 next$0 lst$0 null$0))) :named P52))

(assert (! (or (Btwn$0 next_1$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_11$0 next_1$0 lst$0 null$0))) :named P53))

(assert (! (or (Btwn$0 next_1$0 res_5$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_12$0 next_1$0 res_5$0 null$0))) :named P54))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P55))

(assert (! (= res_5$0 res_4$0) :named P56))

(assert (! (= Alloc_1$0 (union$0 FP_2$0 Alloc_1$0)) :named P57))

(assert (! (= emptyset$0 (intersection$0 sk_?X_4$0 sk_?X_5$0)) :named P58))

(assert (! (= sk_?X_5$0 (lseg_domain$0 next_1$0 lst$0 null$0)) :named P59))

(assert (! (= sk_?X_6$0 (union$0 sk_?X_4$0 sk_?X_5$0)) :named P60))

(assert (! (lseg_struct$0 sk_?X_5$0 next_1$0 lst$0 null$0) :named P61))

(assert (! (= sk_?X_7$0 (union$0 sk_?X_9$0 sk_?X_8$0)) :named P62))

(assert (! (= sk_?X_8$0 (lseg_domain$0 next$0 lst$0 null$0)) :named P63))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P64))

(assert (! (lseg_struct$0 sk_?X_9$0 next$0 null$0 null$0) :named P65))

(assert (! (= sk_?X_10$0 (lseg_domain$0 next$0 lst$0 null$0)) :named P66))

(assert (! (lseg_struct$0 sk_?X_10$0 next$0 lst$0 null$0) :named P67))

(assert (! (= sk_?X_12$0 (lseg_domain$0 next_1$0 res_5$0 null$0)) :named P68))

(assert (! (or (in$0 sk_?e_1$0 (intersection$0 sk_?X_11$0 sk_?X_12$0))
    (and
         (in$0 sk_?e_1$0
           (union$0 (intersection$0 Alloc_1$0 FP$0)
             (setminus$0 Alloc_1$0 Alloc$0)))
         (not (in$0 sk_?e_1$0 sk_?X_13$0)))
    (and (in$0 sk_?e_1$0 sk_?X_13$0)
         (not
              (in$0 sk_?e_1$0
                (union$0 (intersection$0 Alloc_1$0 FP$0)
                  (setminus$0 Alloc_1$0 Alloc$0)))))
    (not (Btwn$0 next_1$0 lst$0 null$0 null$0))
    (not (Btwn$0 next_1$0 res_5$0 null$0 null$0))) :named P69))

(assert (! (not (in$0 null$0 Alloc_1$0)) :named P70))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0)))))) :named P71))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_1$0 res_4$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_1$0 res_4$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_1$0 res_4$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_1$0 res_4$0 null$0)))))) :named P72))

(assert (! (or (and Axiom_2$0 Axiom_1$0 Axiom$0)
    (not (Frame$0 FP_1$0 Alloc$0 next$0 next_1$0))) :named P73))

(assert (! (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_8$0 next$0 lst$0 null$0))) :named P74))

(assert (! (or (Btwn$0 next_1$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_5$0 next_1$0 lst$0 null$0))) :named P75))

(assert (! (or (Btwn$0 next_1$0 res_4$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_4$0 next_1$0 res_4$0 null$0))) :named P76))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc_1$0 FP_1$0)
      (setminus$0 Alloc_1$0 Alloc$0)))) :named P77))

(assert (! (= FP_Caller_final_1$0 (union$0 FP_Caller_1$0 FP_2$0)) :named P78))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next_1$0) :named P79))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P80))

(assert (! (= sk_?X_4$0 (lseg_domain$0 next_1$0 res_4$0 null$0)) :named P81))

(assert (! (= sk_?X_6$0
  (union$0 (intersection$0 Alloc_1$0 FP_1$0) (setminus$0 Alloc_1$0 Alloc$0))) :named P82))

(assert (! (lseg_struct$0 sk_?X_4$0 next_1$0 res_4$0 null$0) :named P83))

(assert (! (= emptyset$0 (intersection$0 sk_?X_9$0 sk_?X_8$0)) :named P84))

(assert (! (= sk_?X_7$0 FP_1$0) :named P85))

(assert (! (= sk_?X_9$0 (lseg_domain$0 next$0 null$0 null$0)) :named P86))

(assert (! (lseg_struct$0 sk_?X_8$0 next$0 lst$0 null$0) :named P87))

(assert (! (= sk_?X_10$0 FP$0) :named P88))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P89))

(assert (! (= sk_?X_11$0 (lseg_domain$0 next_1$0 lst$0 null$0)) :named P90))

(assert (! (= sk_?X_13$0 (union$0 sk_?X_11$0 sk_?X_12$0)) :named P91))

(assert (! (not (in$0 null$0 Alloc$0)) :named P92))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 null$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 null$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 null$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 null$0 null$0)))))) :named P93))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_1$0 lst$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_1$0 lst$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_1$0 lst$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_1$0 lst$0 null$0)))))) :named P94))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_1$0 res_5$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_1$0 res_5$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_1$0 res_5$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_1$0 res_5$0 null$0)))))) :named P95))

(assert (! (forall ((?x Loc)) (Btwn$0 next_1$0 ?x ?x ?x)) :named P96))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P97))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_1$0 ?x ?y ?x)) (= ?x ?y))) :named P98))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P99))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?y)) (not (Btwn$0 next_1$0 ?x ?z ?z))
            (Btwn$0 next_1$0 ?x ?y ?z) (Btwn$0 next_1$0 ?x ?z ?y))) :named P100))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P101))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z))
            (and (Btwn$0 next_1$0 ?x ?y ?y) (Btwn$0 next_1$0 ?y ?z ?z)))) :named P102))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P103))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?y)) (not (Btwn$0 next_1$0 ?y ?z ?z))
            (Btwn$0 next_1$0 ?x ?z ?z))) :named P104))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P105))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z)) (not (Btwn$0 next_1$0 ?y ?u ?z))
            (and (Btwn$0 next_1$0 ?x ?y ?u) (Btwn$0 next_1$0 ?x ?u ?z)))) :named P106))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P107))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z)) (not (Btwn$0 next_1$0 ?x ?u ?y))
            (and (Btwn$0 next_1$0 ?x ?u ?z) (Btwn$0 next_1$0 ?u ?y ?z)))) :named P108))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P109))

(check-sat)

(get-interpolants (and P41 P83 P86 P95 P31 P18 P10 P40 P38 P68 P101 P35 P29 P36 P25 P58 P42 P46 P19 P60 P73 P99 P9 P94 P85 P93 P66 P57 P11 P89 P3 P72 P53 P49 P26 P62 P37 P21 P74 P107 P16 P79 P67 P45 P1 P102 P92 P90 P17 P5 P109 P23 P24 P30 P7) (and P2 P77 P34 P104 P105 P55 P54 P51 P8 P4 P44 P87 P48 P22 P64 P91 P78 P59 P75 P69 P81 P63 P103 P15 P0 P97 P32 P108 P27 P100 P52 P14 P12 P84 P6 P20 P106 P98 P47 P39 P88 P65 P33 P96 P28 P71 P82 P43 P61 P70 P56 P80 P50 P76 P13))

(exit)