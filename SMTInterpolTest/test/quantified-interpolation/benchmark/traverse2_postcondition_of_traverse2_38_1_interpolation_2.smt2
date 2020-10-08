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
  tests/spl/sl/sl_traverse.spl:38:1-2:A postcondition of procedure traverse2 might not hold at this return point
  tests/spl/sl/sl_traverse.spl:25:10-25:Related location: This is the postcondition that might not hold
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
(declare-fun FP$0 () SetLoc)
(declare-fun FP_5$0 () SetLoc)
(declare-fun FP_6$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_3$0 () SetLoc)
(declare-fun FP_Caller_final_3$0 () SetLoc)
(declare-fun curr_8$0 () Loc)
(declare-fun curr_9$0 () Loc)
(declare-fun curr_10$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst_1$0 () Loc)
(declare-fun lst_5$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun sk_?X_25$0 () SetLoc)
(declare-fun sk_?X_26$0 () SetLoc)
(declare-fun sk_?X_27$0 () SetLoc)
(declare-fun sk_?X_28$0 () SetLoc)
(declare-fun sk_?X_29$0 () SetLoc)
(declare-fun sk_?X_30$0 () SetLoc)
(declare-fun sk_?X_31$0 () SetLoc)
(declare-fun sk_?X_32$0 () SetLoc)
(declare-fun sk_?e_4$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_10$0 ?y ?y)) (= curr_10$0 ?y)
            (Btwn$0 next$0 curr_10$0 (read$0 next$0 curr_10$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_10$0) curr_10$0))
            (not (Btwn$0 next$0 curr_10$0 ?y ?y)) (= curr_10$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P4))

(assert (! (Btwn$0 next$0 curr_10$0 (read$0 next$0 curr_10$0) (read$0 next$0 curr_10$0)) :named P5))

(assert (! (or (in$0 (ep$0 next$0 FP_5$0 null$0) FP_5$0)
    (= null$0 (ep$0 next$0 FP_5$0 null$0))) :named P6))

(assert (! (or (in$0 (ep$0 next$0 FP_5$0 curr_9$0) FP_5$0)
    (= curr_9$0 (ep$0 next$0 FP_5$0 curr_9$0))) :named P7))

(assert (! (or (in$0 (ep$0 next$0 FP_5$0 curr_10$0) FP_5$0)
    (= curr_10$0 (ep$0 next$0 FP_5$0 curr_10$0))) :named P8))

(assert (! (or (in$0 (ep$0 next$0 FP_5$0 lst_1$0) FP_5$0)
    (= lst_1$0 (ep$0 next$0 FP_5$0 lst_1$0))) :named P9))

(assert (! (or (in$0 (ep$0 next$0 FP_5$0 lst_5$0) FP_5$0)
    (= lst_5$0 (ep$0 next$0 FP_5$0 lst_5$0))) :named P10))

(assert (! (or (in$0 (ep$0 next$0 FP_5$0 sk_?e_4$0) FP_5$0)
    (= sk_?e_4$0 (ep$0 next$0 FP_5$0 sk_?e_4$0))) :named P11))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 FP_5$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y FP_5$0)))) :named P12))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_9$0 (ep$0 next$0 FP_5$0 curr_9$0) ?y)
            (not (Btwn$0 next$0 curr_9$0 ?y ?y)) (not (in$0 ?y FP_5$0)))) :named P13))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_10$0 (ep$0 next$0 FP_5$0 curr_10$0) ?y)
            (not (Btwn$0 next$0 curr_10$0 ?y ?y)) (not (in$0 ?y FP_5$0)))) :named P14))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 lst_1$0 (ep$0 next$0 FP_5$0 lst_1$0) ?y)
            (not (Btwn$0 next$0 lst_1$0 ?y ?y)) (not (in$0 ?y FP_5$0)))) :named P15))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 lst_5$0 (ep$0 next$0 FP_5$0 lst_5$0) ?y)
            (not (Btwn$0 next$0 lst_5$0 ?y ?y)) (not (in$0 ?y FP_5$0)))) :named P16))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_?e_4$0 (ep$0 next$0 FP_5$0 sk_?e_4$0) ?y)
            (not (Btwn$0 next$0 sk_?e_4$0 ?y ?y)) (not (in$0 ?y FP_5$0)))) :named P17))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 FP_5$0 null$0)
  (ep$0 next$0 FP_5$0 null$0)) :named P18))

(assert (! (Btwn$0 next$0 curr_9$0 (ep$0 next$0 FP_5$0 curr_9$0)
  (ep$0 next$0 FP_5$0 curr_9$0)) :named P19))

(assert (! (Btwn$0 next$0 curr_10$0 (ep$0 next$0 FP_5$0 curr_10$0)
  (ep$0 next$0 FP_5$0 curr_10$0)) :named P20))

(assert (! (Btwn$0 next$0 lst_1$0 (ep$0 next$0 FP_5$0 lst_1$0)
  (ep$0 next$0 FP_5$0 lst_1$0)) :named P21))

(assert (! (Btwn$0 next$0 lst_5$0 (ep$0 next$0 FP_5$0 lst_5$0)
  (ep$0 next$0 FP_5$0 lst_5$0)) :named P22))

(assert (! (Btwn$0 next$0 sk_?e_4$0 (ep$0 next$0 FP_5$0 sk_?e_4$0)
  (ep$0 next$0 FP_5$0 sk_?e_4$0)) :named P23))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_5$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_5$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_5$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_5$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P24))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (setminus$0 FP$0 FP_5$0)
                     (union$0 (intersection$0 Alloc$0 FP_5$0)
                       (setminus$0 Alloc$0 Alloc$0))))
                 (or (in$0 x (setminus$0 FP$0 FP_5$0))
                     (in$0 x
                       (union$0 (intersection$0 Alloc$0 FP_5$0)
                         (setminus$0 Alloc$0 Alloc$0)))))
            (and (not (in$0 x (setminus$0 FP$0 FP_5$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_5$0)
                          (setminus$0 Alloc$0 Alloc$0))))
                 (not
                      (in$0 x
                        (union$0 (setminus$0 FP$0 FP_5$0)
                          (union$0 (intersection$0 Alloc$0 FP_5$0)
                            (setminus$0 Alloc$0 Alloc$0)))))))) :named P25))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_5$0 FP$0))
                 (or (in$0 x FP_5$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_5$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_5$0 FP$0)))))) :named P26))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_6$0 Alloc$0))
                 (or (in$0 x FP_6$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_6$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_6$0 Alloc$0)))))) :named P27))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_27$0 sk_?X_28$0))
                 (or (in$0 x sk_?X_27$0) (in$0 x sk_?X_28$0)))
            (and (not (in$0 x sk_?X_27$0)) (not (in$0 x sk_?X_28$0))
                 (not (in$0 x (union$0 sk_?X_27$0 sk_?X_28$0)))))) :named P28))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_32$0 sk_?X_31$0))
                 (or (in$0 x sk_?X_32$0) (in$0 x sk_?X_31$0)))
            (and (not (in$0 x sk_?X_32$0)) (not (in$0 x sk_?X_31$0))
                 (not (in$0 x (union$0 sk_?X_32$0 sk_?X_31$0)))))) :named P29))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P30))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P31))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_3$0 FP_6$0))
                 (or (in$0 x FP_Caller_3$0) (in$0 x FP_6$0)))
            (and (not (in$0 x FP_Caller_3$0)) (not (in$0 x FP_6$0))
                 (not (in$0 x (union$0 FP_Caller_3$0 FP_6$0)))))) :named P32))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P33))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 Alloc$0 FP$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP$0)))))) :named P34))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_5$0)
                 (in$0 x (intersection$0 Alloc$0 FP_5$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_5$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_5$0)))))) :named P35))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_27$0) (in$0 x sk_?X_28$0)
                 (in$0 x (intersection$0 sk_?X_27$0 sk_?X_28$0)))
            (and (or (not (in$0 x sk_?X_27$0)) (not (in$0 x sk_?X_28$0)))
                 (not (in$0 x (intersection$0 sk_?X_27$0 sk_?X_28$0)))))) :named P36))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_32$0) (in$0 x sk_?X_31$0)
                 (in$0 x (intersection$0 sk_?X_32$0 sk_?X_31$0)))
            (and (or (not (in$0 x sk_?X_32$0)) (not (in$0 x sk_?X_31$0)))
                 (not (in$0 x (intersection$0 sk_?X_32$0 sk_?X_31$0)))))) :named P37))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P38))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 FP_5$0))
                 (not (in$0 x FP_5$0)))
            (and (or (in$0 x FP_5$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 FP_5$0)))))) :named P39))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P40))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P41))

(assert (! (= (read$0 next$0 null$0) null$0) :named P42))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P43))

(assert (! (or (Btwn$0 next$0 curr_9$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_31$0 next$0 curr_9$0 null$0))) :named P44))

(assert (! (or (Btwn$0 next$0 lst_1$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_25$0 next$0 lst_1$0 null$0))) :named P45))

(assert (! (or (Btwn$0 next$0 lst_1$0 curr_9$0 curr_9$0)
    (not (lseg_struct$0 sk_?X_32$0 next$0 lst_1$0 curr_9$0))) :named P46))

(assert (! (or
    (and (= (read$0 next$0 curr_10$0) null$0)
         (= FP_6$0
           (union$0 (setminus$0 FP$0 FP_5$0)
             (union$0 (intersection$0 Alloc$0 FP_5$0)
               (setminus$0 Alloc$0 Alloc$0))))
         (= curr_9$0 lst_1$0) (= lst_5$0 lst_1$0)
         (Frame$0 FP_5$0 Alloc$0 next$0 next$0)
         (= Alloc$0 (union$0 FP_6$0 Alloc$0))
         (and (= emptyset$0 (intersection$0 sk_?X_27$0 sk_?X_28$0))
              (= sk_?X_27$0 (lseg_domain$0 next$0 lst_5$0 curr_10$0))
              (= sk_?X_28$0 (lseg_domain$0 next$0 curr_10$0 null$0))
              (= sk_?X_29$0
                (union$0 (intersection$0 Alloc$0 FP_5$0)
                  (setminus$0 Alloc$0 Alloc$0)))
              (= sk_?X_29$0 (union$0 sk_?X_27$0 sk_?X_28$0))
              (lseg_struct$0 sk_?X_27$0 next$0 lst_5$0 curr_10$0)
              (lseg_struct$0 sk_?X_28$0 next$0 curr_10$0 null$0))
         (and (= emptyset$0 (intersection$0 sk_?X_32$0 sk_?X_31$0))
              (= sk_?X_30$0 (union$0 sk_?X_32$0 sk_?X_31$0))
              (= sk_?X_30$0 FP_5$0)
              (= sk_?X_31$0 (lseg_domain$0 next$0 curr_9$0 null$0))
              (= sk_?X_32$0 (lseg_domain$0 next$0 lst_1$0 curr_9$0))
              (= FP$0 (union$0 FP_5$0 FP$0))
              (lseg_struct$0 sk_?X_31$0 next$0 curr_9$0 null$0)
              (lseg_struct$0 sk_?X_32$0 next$0 lst_1$0 curr_9$0))
         (not (= lst_1$0 null$0)) (not (in$0 null$0 Alloc$0)))
    (and (= FP_6$0 FP$0) (= curr_10$0 curr_8$0) (= lst_1$0 null$0)
         (= lst_5$0 lst_1$0))) :named P47))

(assert (! (= FP_Caller_final_3$0 (union$0 FP_Caller_3$0 FP_6$0)) :named P48))

(assert (! (= sk_?X_25$0 FP$0) :named P49))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P50))

(assert (! (= sk_?X_26$0
  (union$0 (intersection$0 Alloc$0 FP$0) (setminus$0 Alloc$0 Alloc$0))) :named P51))

(assert (! (not (in$0 null$0 Alloc$0)) :named P52))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_10$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_10$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_10$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_10$0 null$0)))))) :named P53))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst_1$0 l1 curr_9$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst_1$0 curr_9$0))
                 (not (= l1 curr_9$0)))
            (and
                 (or (= l1 curr_9$0)
                     (not (Btwn$0 next$0 lst_1$0 l1 curr_9$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst_1$0 curr_9$0)))))) :named P54))

(assert (! (or (Btwn$0 next$0 curr_10$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_28$0 next$0 curr_10$0 null$0))) :named P55))

(assert (! (or (Btwn$0 next$0 lst_1$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_26$0 next$0 lst_1$0 null$0))) :named P56))

(assert (! (or (Btwn$0 next$0 lst_5$0 curr_10$0 curr_10$0)
    (not (lseg_struct$0 sk_?X_27$0 next$0 lst_5$0 curr_10$0))) :named P57))

(assert (! (= FP_Caller_3$0 (setminus$0 FP_Caller$0 FP$0)) :named P58))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P59))

(assert (! (= sk_?X_25$0 (lseg_domain$0 next$0 lst_1$0 null$0)) :named P60))

(assert (! (lseg_struct$0 sk_?X_25$0 next$0 lst_1$0 null$0) :named P61))

(assert (! (or
    (and (in$0 sk_?e_4$0 (lseg_domain$0 next$0 lst_1$0 null$0))
         (not (in$0 sk_?e_4$0 sk_?X_26$0)))
    (and (in$0 sk_?e_4$0 sk_?X_26$0)
         (not (in$0 sk_?e_4$0 (lseg_domain$0 next$0 lst_1$0 null$0))))
    (not (Btwn$0 next$0 lst_1$0 null$0 null$0))) :named P62))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_9$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_9$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_9$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_9$0 null$0)))))) :named P63))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst_1$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst_1$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst_1$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst_1$0 null$0)))))) :named P64))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst_5$0 l1 curr_10$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst_5$0 curr_10$0))
                 (not (= l1 curr_10$0)))
            (and
                 (or (= l1 curr_10$0)
                     (not (Btwn$0 next$0 lst_5$0 l1 curr_10$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst_5$0 curr_10$0)))))) :named P65))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P66))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P67))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P68))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P69))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P70))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P71))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P72))

(check-sat)

(get-interpolants (and P60 P45 P23 P4 P40 P6 P41 P7 P36 P52 P72 P58 P26 P5 P56 P11 P33 P21 P22 P19 P9 P53 P54 P69 P68 P64 P0 P55 P18 P46 P61 P71 P66 P70 P31 P17 P8) (and P50 P48 P47 P51 P57 P29 P37 P10 P42 P44 P38 P20 P27 P62 P67 P49 P12 P39 P28 P35 P34 P3 P1 P15 P14 P13 P32 P30 P59 P65 P25 P2 P24 P63 P16 P43))

(exit)