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
  tests/spl/sl/rec_reverse.spl:27:2-36:A postcondition of procedure rec_reverse might not hold at this return point
  tests/spl/sl/rec_reverse.spl:25:10-25:Related location: This is the postcondition that might not hold
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
(declare-fun res_2$0 () Loc)
(declare-fun res_3$0 () Loc)
(declare-fun sk_?X_4$0 () SetLoc)
(declare-fun sk_?X_5$0 () SetLoc)
(declare-fun sk_?X_6$0 () SetLoc)
(declare-fun sk_?X_7$0 () SetLoc)
(declare-fun sk_?X_8$0 () SetLoc)
(declare-fun sk_?X_9$0 () SetLoc)
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
                (and (Btwn$0 next$0 res_3$0 ?z ?y)
                     (Btwn$0 next_1$0 res_3$0 ?z ?y))
                (and (not (Btwn$0 next$0 res_3$0 ?z ?y))
                     (not (Btwn$0 next_1$0 res_3$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 res_3$0 ?y
                           (ep$0 next$0 FP_1$0 res_3$0))
                         (and (Btwn$0 next$0 res_3$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 res_3$0
                                     (ep$0 next$0 FP_1$0 res_3$0)
                                     (ep$0 next$0 FP_1$0 res_3$0))))))))) :named P9))

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
            (or (in$0 res_3$0 FP_1$0)
                (and (Btwn$0 next$0 res_3$0 ?z ?y)
                     (Btwn$0 next_1$0 res_3$0 ?z ?y))
                (and (not (Btwn$0 next$0 res_3$0 ?z ?y))
                     (not (Btwn$0 next_1$0 res_3$0 ?z ?y)))
                (not (= res_3$0 (ep$0 next$0 FP_1$0 res_3$0)))))) :named P13))

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
        (or (Btwn$0 next$0 res_3$0 (ep$0 next$0 FP_1$0 res_3$0) ?y)
            (not (Btwn$0 next$0 res_3$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P17))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_?e_1$0 (ep$0 next$0 FP_1$0 sk_?e_1$0) ?y)
            (not (Btwn$0 next$0 sk_?e_1$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P18))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 null$0) FP_1$0)
    (= null$0 (ep$0 next$0 FP_1$0 null$0))) :named P19))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 lst$0) FP_1$0)
    (= lst$0 (ep$0 next$0 FP_1$0 lst$0))) :named P20))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 res_3$0) FP_1$0)
    (= res_3$0 (ep$0 next$0 FP_1$0 res_3$0))) :named P21))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 sk_?e_1$0) FP_1$0)
    (= sk_?e_1$0 (ep$0 next$0 FP_1$0 sk_?e_1$0))) :named P22))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 FP_1$0 null$0)
  (ep$0 next$0 FP_1$0 null$0)) :named P23))

(assert (! (Btwn$0 next$0 lst$0 (ep$0 next$0 FP_1$0 lst$0) (ep$0 next$0 FP_1$0 lst$0)) :named P24))

(assert (! (Btwn$0 next$0 res_3$0 (ep$0 next$0 FP_1$0 res_3$0)
  (ep$0 next$0 FP_1$0 res_3$0)) :named P25))

(assert (! (Btwn$0 next$0 sk_?e_1$0 (ep$0 next$0 FP_1$0 sk_?e_1$0)
  (ep$0 next$0 FP_1$0 sk_?e_1$0)) :named P26))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P27))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))) :named P28))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_1$0 FP$0))
                 (or (in$0 x FP_1$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_1$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_1$0 FP$0)))))) :named P29))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_7$0 FP$0))
                 (or (in$0 x sk_?X_7$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_7$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_7$0 FP$0)))))) :named P30))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_4$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_4$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_4$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_4$0)))))) :named P31))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P32))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_1$0 FP_2$0))
                 (or (in$0 x FP_Caller_1$0) (in$0 x FP_2$0)))
            (and (not (in$0 x FP_Caller_1$0)) (not (in$0 x FP_2$0))
                 (not (in$0 x (union$0 FP_Caller_1$0 FP_2$0)))))) :named P33))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_1$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_1$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_1$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_1$0)
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
            (and (in$0 x sk_?X_7$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 sk_?X_7$0 FP$0)))
            (and (or (not (in$0 x sk_?X_7$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 sk_?X_7$0 FP$0)))))) :named P36))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 Alloc$0 FP$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP$0)))))) :named P37))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_1$0)
                 (in$0 x (intersection$0 Alloc$0 FP_1$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_1$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_1$0)))))) :named P38))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P39))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 FP_1$0))
                 (not (in$0 x FP_1$0)))
            (and (or (in$0 x FP_1$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 FP_1$0)))))) :named P40))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 FP_1$0))
                 (not (in$0 x FP_1$0)))
            (and (or (in$0 x FP_1$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 FP_1$0)))))) :named P41))

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

(assert (! (= (read$0 next_1$0 null$0) null$0) :named P45))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P46))

(assert (! (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_6$0 next$0 lst$0 null$0))) :named P47))

(assert (! (or (Btwn$0 next_1$0 res_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_4$0 next_1$0 res_2$0 null$0))) :named P48))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P49))

(assert (! (= FP_Caller_final_1$0 (union$0 FP_Caller_1$0 FP_2$0)) :named P50))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next_1$0) :named P51))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P52))

(assert (! (= sk_?X_5$0 (union$0 sk_?X_7$0 sk_?X_6$0)) :named P53))

(assert (! (= sk_?X_6$0 (lseg_domain$0 next$0 lst$0 null$0)) :named P54))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P55))

(assert (! (lseg_struct$0 sk_?X_7$0 next$0 null$0 null$0) :named P56))

(assert (! (= sk_?X_4$0 (lseg_domain$0 next_1$0 res_2$0 null$0)) :named P57))

(assert (! (= sk_?X_8$0 FP$0) :named P58))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P59))

(assert (! (= sk_?X_9$0
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
            (and (Btwn$0 next_1$0 res_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_1$0 res_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_1$0 res_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_1$0 res_2$0 null$0)))))) :named P63))

(assert (! (or (and Axiom_2$0 Axiom_1$0 Axiom$0)
    (not (Frame$0 FP_1$0 Alloc$0 next$0 next_1$0))) :named P64))

(assert (! (or (Btwn$0 next$0 null$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_7$0 next$0 null$0 null$0))) :named P65))

(assert (! (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_8$0 next$0 lst$0 null$0))) :named P66))

(assert (! (or (Btwn$0 next_1$0 res_3$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_9$0 next_1$0 res_3$0 null$0))) :named P67))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P68))

(assert (! (= res_3$0 res_2$0) :named P69))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P70))

(assert (! (= emptyset$0 (intersection$0 sk_?X_7$0 sk_?X_6$0)) :named P71))

(assert (! (= sk_?X_5$0 FP_1$0) :named P72))

(assert (! (= sk_?X_7$0 (lseg_domain$0 next$0 null$0 null$0)) :named P73))

(assert (! (lseg_struct$0 sk_?X_6$0 next$0 lst$0 null$0) :named P74))

(assert (! (= sk_?X_4$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P75))

(assert (! (lseg_struct$0 sk_?X_4$0 next_1$0 res_2$0 null$0) :named P76))

(assert (! (= sk_?X_8$0 (lseg_domain$0 next$0 lst$0 null$0)) :named P77))

(assert (! (lseg_struct$0 sk_?X_8$0 next$0 lst$0 null$0) :named P78))

(assert (! (or
    (and (in$0 sk_?e_1$0 (lseg_domain$0 next_1$0 res_3$0 null$0))
         (not (in$0 sk_?e_1$0 sk_?X_9$0)))
    (and (in$0 sk_?e_1$0 sk_?X_9$0)
         (not (in$0 sk_?e_1$0 (lseg_domain$0 next_1$0 res_3$0 null$0))))
    (not (Btwn$0 next_1$0 res_3$0 null$0 null$0))) :named P79))

(assert (! (not (in$0 null$0 Alloc$0)) :named P80))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0)))))) :named P81))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_1$0 res_3$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_1$0 res_3$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_1$0 res_3$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_1$0 res_3$0 null$0)))))) :named P82))

(assert (! (forall ((?x Loc)) (Btwn$0 next_1$0 ?x ?x ?x)) :named P83))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P84))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_1$0 ?x ?y ?x)) (= ?x ?y))) :named P85))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P86))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?y)) (not (Btwn$0 next_1$0 ?x ?z ?z))
            (Btwn$0 next_1$0 ?x ?y ?z) (Btwn$0 next_1$0 ?x ?z ?y))) :named P87))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P88))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z))
            (and (Btwn$0 next_1$0 ?x ?y ?y) (Btwn$0 next_1$0 ?y ?z ?z)))) :named P89))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P90))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?y)) (not (Btwn$0 next_1$0 ?y ?z ?z))
            (Btwn$0 next_1$0 ?x ?z ?z))) :named P91))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P92))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z)) (not (Btwn$0 next_1$0 ?y ?u ?z))
            (and (Btwn$0 next_1$0 ?x ?y ?u) (Btwn$0 next_1$0 ?x ?u ?z)))) :named P93))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P94))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z)) (not (Btwn$0 next_1$0 ?x ?u ?y))
            (and (Btwn$0 next_1$0 ?x ?u ?z) (Btwn$0 next_1$0 ?u ?y ?z)))) :named P95))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P96))

(check-sat)

(get-interpolants (and P93 P75 P56 P23 P32 P62 P96 P81 P74 P12 P95 P33 P9 P46 P8 P54 P38 P14 P63 P39 P77 P51 P34 P3 P70 P47 P68 P89 P26 P67 P53 P43 P60 P15 P90 P6 P49 P86 P50 P59 P91 P94 P19 P24 P61 P66 P57 P10 P1) (and P2 P71 P4 P25 P92 P5 P28 P18 P35 P80 P11 P78 P48 P85 P55 P22 P76 P88 P20 P7 P29 P73 P0 P79 P13 P36 P87 P44 P41 P37 P65 P17 P30 P31 P16 P42 P84 P83 P40 P64 P52 P45 P72 P69 P82 P58 P21 P27))

(exit)