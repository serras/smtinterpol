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
  tests/spl/sl/rec_copy.spl:29:2-37:A postcondition of procedure rec_reverse might not hold at this return point
  tests/spl/sl/rec_copy.spl:27:10-25:Related location: This is the postcondition that might not hold
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
(declare-fun Axiom_9$0 () Bool)
(declare-fun Axiom_10$0 () Bool)
(declare-fun Axiom_11$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_8$0 () SetLoc)
(declare-fun FP_9$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_3$0 () SetLoc)
(declare-fun FP_Caller_final_6$0 () SetLoc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst_1$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_5$0 () FldLoc)
(declare-fun res_10$0 () Loc)
(declare-fun res_11$0 () Loc)
(declare-fun sk_?X_76$0 () SetLoc)
(declare-fun sk_?X_77$0 () SetLoc)
(declare-fun sk_?X_78$0 () SetLoc)
(declare-fun sk_?X_79$0 () SetLoc)
(declare-fun sk_?X_80$0 () SetLoc)
(declare-fun sk_?X_81$0 () SetLoc)
(declare-fun sk_?e_7$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_5$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_5$0 null$0 (read$0 next_5$0 null$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_5$0 null$0) null$0))
            (not (Btwn$0 next_5$0 null$0 ?y ?y)) (= null$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P4))

(assert (! (Btwn$0 next_5$0 null$0 (read$0 next_5$0 null$0) (read$0 next_5$0 null$0)) :named P5))

(assert (! (or (not Axiom_11$0)
    (or (= (read$0 next$0 null$0) (read$0 next_5$0 null$0))
        (not (in$0 null$0 (setminus$0 Alloc$0 FP_8$0))))) :named P6))

(assert (! (or (not Axiom_10$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_5$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_5$0 null$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 null$0 ?y
                           (ep$0 next$0 FP_8$0 null$0))
                         (and (Btwn$0 next$0 null$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 null$0
                                     (ep$0 next$0 FP_8$0 null$0)
                                     (ep$0 next$0 FP_8$0 null$0))))))))) :named P7))

(assert (! (or (not Axiom_10$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 lst_1$0 ?z ?y)
                     (Btwn$0 next_5$0 lst_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 lst_1$0 ?z ?y))
                     (not (Btwn$0 next_5$0 lst_1$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 lst_1$0 ?y
                           (ep$0 next$0 FP_8$0 lst_1$0))
                         (and (Btwn$0 next$0 lst_1$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 lst_1$0
                                     (ep$0 next$0 FP_8$0 lst_1$0)
                                     (ep$0 next$0 FP_8$0 lst_1$0))))))))) :named P8))

(assert (! (or (not Axiom_10$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 res_11$0 ?z ?y)
                     (Btwn$0 next_5$0 res_11$0 ?z ?y))
                (and (not (Btwn$0 next$0 res_11$0 ?z ?y))
                     (not (Btwn$0 next_5$0 res_11$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 res_11$0 ?y
                           (ep$0 next$0 FP_8$0 res_11$0))
                         (and (Btwn$0 next$0 res_11$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 res_11$0
                                     (ep$0 next$0 FP_8$0 res_11$0)
                                     (ep$0 next$0 FP_8$0 res_11$0))))))))) :named P9))

(assert (! (or (not Axiom_10$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 sk_?e_7$0 ?z ?y)
                     (Btwn$0 next_5$0 sk_?e_7$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_?e_7$0 ?z ?y))
                     (not (Btwn$0 next_5$0 sk_?e_7$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 sk_?e_7$0 ?y
                           (ep$0 next$0 FP_8$0 sk_?e_7$0))
                         (and (Btwn$0 next$0 sk_?e_7$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 sk_?e_7$0
                                     (ep$0 next$0 FP_8$0 sk_?e_7$0)
                                     (ep$0 next$0 FP_8$0 sk_?e_7$0))))))))) :named P10))

(assert (! (or (not Axiom_9$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 null$0 FP_8$0)
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_5$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_5$0 null$0 ?z ?y)))
                (not (= null$0 (ep$0 next$0 FP_8$0 null$0)))))) :named P11))

(assert (! (or (not Axiom_9$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 lst_1$0 FP_8$0)
                (and (Btwn$0 next$0 lst_1$0 ?z ?y)
                     (Btwn$0 next_5$0 lst_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 lst_1$0 ?z ?y))
                     (not (Btwn$0 next_5$0 lst_1$0 ?z ?y)))
                (not (= lst_1$0 (ep$0 next$0 FP_8$0 lst_1$0)))))) :named P12))

(assert (! (or (not Axiom_9$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 res_11$0 FP_8$0)
                (and (Btwn$0 next$0 res_11$0 ?z ?y)
                     (Btwn$0 next_5$0 res_11$0 ?z ?y))
                (and (not (Btwn$0 next$0 res_11$0 ?z ?y))
                     (not (Btwn$0 next_5$0 res_11$0 ?z ?y)))
                (not (= res_11$0 (ep$0 next$0 FP_8$0 res_11$0)))))) :named P13))

(assert (! (or (not Axiom_9$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 sk_?e_7$0 FP_8$0)
                (and (Btwn$0 next$0 sk_?e_7$0 ?z ?y)
                     (Btwn$0 next_5$0 sk_?e_7$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_?e_7$0 ?z ?y))
                     (not (Btwn$0 next_5$0 sk_?e_7$0 ?z ?y)))
                (not (= sk_?e_7$0 (ep$0 next$0 FP_8$0 sk_?e_7$0)))))) :named P14))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 FP_8$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y FP_8$0)))) :named P15))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 lst_1$0 (ep$0 next$0 FP_8$0 lst_1$0) ?y)
            (not (Btwn$0 next$0 lst_1$0 ?y ?y)) (not (in$0 ?y FP_8$0)))) :named P16))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 res_11$0 (ep$0 next$0 FP_8$0 res_11$0) ?y)
            (not (Btwn$0 next$0 res_11$0 ?y ?y)) (not (in$0 ?y FP_8$0)))) :named P17))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_?e_7$0 (ep$0 next$0 FP_8$0 sk_?e_7$0) ?y)
            (not (Btwn$0 next$0 sk_?e_7$0 ?y ?y)) (not (in$0 ?y FP_8$0)))) :named P18))

(assert (! (or (in$0 (ep$0 next$0 FP_8$0 null$0) FP_8$0)
    (= null$0 (ep$0 next$0 FP_8$0 null$0))) :named P19))

(assert (! (or (in$0 (ep$0 next$0 FP_8$0 lst_1$0) FP_8$0)
    (= lst_1$0 (ep$0 next$0 FP_8$0 lst_1$0))) :named P20))

(assert (! (or (in$0 (ep$0 next$0 FP_8$0 res_11$0) FP_8$0)
    (= res_11$0 (ep$0 next$0 FP_8$0 res_11$0))) :named P21))

(assert (! (or (in$0 (ep$0 next$0 FP_8$0 sk_?e_7$0) FP_8$0)
    (= sk_?e_7$0 (ep$0 next$0 FP_8$0 sk_?e_7$0))) :named P22))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 FP_8$0 null$0)
  (ep$0 next$0 FP_8$0 null$0)) :named P23))

(assert (! (Btwn$0 next$0 lst_1$0 (ep$0 next$0 FP_8$0 lst_1$0)
  (ep$0 next$0 FP_8$0 lst_1$0)) :named P24))

(assert (! (Btwn$0 next$0 res_11$0 (ep$0 next$0 FP_8$0 res_11$0)
  (ep$0 next$0 FP_8$0 res_11$0)) :named P25))

(assert (! (Btwn$0 next$0 sk_?e_7$0 (ep$0 next$0 FP_8$0 sk_?e_7$0)
  (ep$0 next$0 FP_8$0 sk_?e_7$0)) :named P26))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P27))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_9$0 Alloc$0))
                 (or (in$0 x FP_9$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_9$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_9$0 Alloc$0)))))) :named P28))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_8$0 FP$0))
                 (or (in$0 x FP_8$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_8$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_8$0 FP$0)))))) :named P29))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 sk_?X_78$0))
                 (or (in$0 x FP$0) (in$0 x sk_?X_78$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x sk_?X_78$0))
                 (not (in$0 x (union$0 FP$0 sk_?X_78$0)))))) :named P30))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_8$0) sk_?X_76$0))
                 (or (in$0 x (setminus$0 FP$0 FP_8$0)) (in$0 x sk_?X_76$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_8$0)))
                 (not (in$0 x sk_?X_76$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_8$0) sk_?X_76$0)))))) :named P31))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P32))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_3$0 FP_9$0))
                 (or (in$0 x FP_Caller_3$0) (in$0 x FP_9$0)))
            (and (not (in$0 x FP_Caller_3$0)) (not (in$0 x FP_9$0))
                 (not (in$0 x (union$0 FP_Caller_3$0 FP_9$0)))))) :named P33))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_8$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_8$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_8$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_8$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P34))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P35))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x sk_?X_78$0)
                 (in$0 x (intersection$0 FP$0 sk_?X_78$0)))
            (and (or (not (in$0 x FP$0)) (not (in$0 x sk_?X_78$0)))
                 (not (in$0 x (intersection$0 FP$0 sk_?X_78$0)))))) :named P36))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 Alloc$0 FP$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP$0)))))) :named P37))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_8$0)
                 (in$0 x (intersection$0 Alloc$0 FP_8$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_8$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_8$0)))))) :named P38))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P39))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 FP_8$0))
                 (not (in$0 x FP_8$0)))
            (and (or (in$0 x FP_8$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 FP_8$0)))))) :named P40))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 FP_8$0))
                 (not (in$0 x FP_8$0)))
            (and (or (in$0 x FP_8$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 FP_8$0)))))) :named P41))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P42))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P43))

(assert (! (= (read$0 next$0 null$0) null$0) :named P44))

(assert (! (= (read$0 next_5$0 null$0) null$0) :named P45))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P46))

(assert (! (or (Btwn$0 next$0 lst_1$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_79$0 next$0 lst_1$0 null$0))) :named P47))

(assert (! (or (Btwn$0 next_5$0 res_10$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_76$0 next_5$0 res_10$0 null$0))) :named P48))

(assert (! (= FP_9$0
  (union$0 (setminus$0 FP$0 FP_8$0)
    (union$0 (intersection$0 Alloc$0 FP_8$0) (setminus$0 Alloc$0 Alloc$0)))) :named P49))

(assert (! (= FP_Caller_final_6$0 (union$0 FP_Caller_3$0 FP_9$0)) :named P50))

(assert (! (Frame$0 FP_8$0 Alloc$0 next$0 next_5$0) :named P51))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P52))

(assert (! (= sk_?X_77$0 (union$0 sk_?X_79$0 sk_?X_78$0)) :named P53))

(assert (! (= sk_?X_78$0 (lseg_domain$0 next$0 null$0 null$0)) :named P54))

(assert (! (= FP$0 (union$0 FP_8$0 FP$0)) :named P55))

(assert (! (lseg_struct$0 sk_?X_79$0 next$0 lst_1$0 null$0) :named P56))

(assert (! (= sk_?X_76$0 (lseg_domain$0 next_5$0 res_10$0 null$0)) :named P57))

(assert (! (= sk_?X_80$0 FP$0) :named P58))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P59))

(assert (! (= sk_?X_81$0
  (union$0 (intersection$0 Alloc$0 FP$0) (setminus$0 Alloc$0 Alloc$0))) :named P60))

(assert (! (not (in$0 null$0 Alloc$0)) :named P61))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 null$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 null$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 null$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 null$0 null$0)))))) :named P62))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_5$0 res_10$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_5$0 res_10$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next_5$0 res_10$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_5$0 res_10$0 null$0)))))) :named P63))

(assert (! (or (and Axiom_11$0 Axiom_10$0 Axiom_9$0)
    (not (Frame$0 FP_8$0 Alloc$0 next$0 next_5$0))) :named P64))

(assert (! (or (Btwn$0 next$0 null$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_78$0 next$0 null$0 null$0))) :named P65))

(assert (! (or (Btwn$0 next$0 lst_1$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_80$0 next$0 lst_1$0 null$0))) :named P66))

(assert (! (or (Btwn$0 next_5$0 res_11$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_81$0 next_5$0 res_11$0 null$0))) :named P67))

(assert (! (= FP_Caller_3$0 (setminus$0 FP_Caller$0 FP$0)) :named P68))

(assert (! (= res_11$0 res_10$0) :named P69))

(assert (! (= Alloc$0 (union$0 FP_9$0 Alloc$0)) :named P70))

(assert (! (= emptyset$0 (intersection$0 sk_?X_79$0 sk_?X_78$0)) :named P71))

(assert (! (= sk_?X_77$0 FP_8$0) :named P72))

(assert (! (= sk_?X_79$0 (lseg_domain$0 next$0 lst_1$0 null$0)) :named P73))

(assert (! (lseg_struct$0 sk_?X_78$0 next$0 null$0 null$0) :named P74))

(assert (! (= sk_?X_76$0
  (union$0 (intersection$0 Alloc$0 FP_8$0) (setminus$0 Alloc$0 Alloc$0))) :named P75))

(assert (! (lseg_struct$0 sk_?X_76$0 next_5$0 res_10$0 null$0) :named P76))

(assert (! (= sk_?X_80$0 (lseg_domain$0 next$0 lst_1$0 null$0)) :named P77))

(assert (! (lseg_struct$0 sk_?X_80$0 next$0 lst_1$0 null$0) :named P78))

(assert (! (or
    (and (in$0 sk_?e_7$0 (lseg_domain$0 next_5$0 res_11$0 null$0))
         (not (in$0 sk_?e_7$0 sk_?X_81$0)))
    (and (in$0 sk_?e_7$0 sk_?X_81$0)
         (not (in$0 sk_?e_7$0 (lseg_domain$0 next_5$0 res_11$0 null$0))))
    (not (Btwn$0 next_5$0 res_11$0 null$0 null$0))) :named P79))

(assert (! (not (in$0 null$0 Alloc$0)) :named P80))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst_1$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst_1$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst_1$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst_1$0 null$0)))))) :named P81))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_5$0 res_11$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_5$0 res_11$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next_5$0 res_11$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_5$0 res_11$0 null$0)))))) :named P82))

(assert (! (forall ((?x Loc)) (Btwn$0 next_5$0 ?x ?x ?x)) :named P83))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P84))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_5$0 ?x ?y ?x)) (= ?x ?y))) :named P85))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P86))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?y)) (not (Btwn$0 next_5$0 ?x ?z ?z))
            (Btwn$0 next_5$0 ?x ?y ?z) (Btwn$0 next_5$0 ?x ?z ?y))) :named P87))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P88))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?z))
            (and (Btwn$0 next_5$0 ?x ?y ?y) (Btwn$0 next_5$0 ?y ?z ?z)))) :named P89))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P90))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?y)) (not (Btwn$0 next_5$0 ?y ?z ?z))
            (Btwn$0 next_5$0 ?x ?z ?z))) :named P91))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P92))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?z)) (not (Btwn$0 next_5$0 ?y ?u ?z))
            (and (Btwn$0 next_5$0 ?x ?y ?u) (Btwn$0 next_5$0 ?x ?u ?z)))) :named P93))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P94))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?z)) (not (Btwn$0 next_5$0 ?x ?u ?y))
            (and (Btwn$0 next_5$0 ?x ?u ?z) (Btwn$0 next_5$0 ?u ?y ?z)))) :named P95))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P96))

(check-sat)

(get-interpolants (and P47 P2 P48 P7 P54 P52 P73 P89 P59 P81 P74 P29 P28 P32 P55 P19 P49 P18 P60 P72 P26 P0 P3 P6 P88 P16 P33 P9 P25 P42 P51 P46 P93 P62 P5 P23 P53 P13 P90 P56 P57 P20 P94 P39 P91 P80 P36 P17 P67) (and P11 P83 P85 P27 P22 P31 P4 P43 P87 P50 P35 P78 P38 P58 P61 P75 P64 P14 P77 P69 P41 P65 P76 P40 P95 P30 P21 P92 P66 P82 P8 P68 P12 P79 P37 P96 P70 P63 P34 P15 P24 P10 P84 P44 P86 P1 P71 P45))

(exit)