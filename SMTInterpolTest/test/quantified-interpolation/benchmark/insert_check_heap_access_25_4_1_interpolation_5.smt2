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
  tests/spl/sl/sl_insert.spl:25:4-26:Possible heap access through null or dangling reference
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
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun curr_2$0 () Loc)
(declare-fun curr_3$0 () Loc)
(declare-fun elt$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst$0 () Loc)
(declare-fun lst_1$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun sk_?X_25$0 () SetLoc)
(declare-fun sk_?X_26$0 () SetLoc)
(declare-fun sk_?X_27$0 () SetLoc)
(declare-fun sk_?X_28$0 () SetLoc)
(declare-fun sk_?X_29$0 () SetLoc)
(declare-fun sk_?X_30$0 () SetLoc)
(declare-fun sk_?X_31$0 () SetLoc)
(declare-fun sk_?X_32$0 () SetLoc)
(declare-fun sk_?X_33$0 () SetLoc)
(declare-fun sk_?X_34$0 () SetLoc)
(declare-fun sk_?X_35$0 () SetLoc)
(declare-fun sk_?X_36$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 elt$0 ?y ?y)) (= elt$0 ?y)
            (Btwn$0 next$0 elt$0 (read$0 next$0 elt$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y)
            (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 elt$0) elt$0))
            (not (Btwn$0 next$0 elt$0 ?y ?y)) (= elt$0 ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_3$0) curr_3$0))
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y))) :named P5))

(assert (! (Btwn$0 next$0 elt$0 (read$0 next$0 elt$0) (read$0 next$0 elt$0)) :named P6))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P7))

(assert (! (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) (read$0 next$0 curr_3$0)) :named P8))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_29$0 null$0) sk_?X_29$0)
    (= null$0 (ep$0 next$0 sk_?X_29$0 null$0))) :named P9))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_29$0 lst_1$0) sk_?X_29$0)
    (= lst_1$0 (ep$0 next$0 sk_?X_29$0 lst_1$0))) :named P10))

(assert (! (or (in$0 (ep$0 next$0 sk_?X_29$0 curr_3$0) sk_?X_29$0)
    (= curr_3$0 (ep$0 next$0 sk_?X_29$0 curr_3$0))) :named P11))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_29$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y sk_?X_29$0)))) :named P12))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 lst_1$0 (ep$0 next$0 sk_?X_29$0 lst_1$0) ?y)
            (not (Btwn$0 next$0 lst_1$0 ?y ?y)) (not (in$0 ?y sk_?X_29$0)))) :named P13))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_29$0 curr_3$0) ?y)
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (not (in$0 ?y sk_?X_29$0)))) :named P14))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_29$0 null$0)
  (ep$0 next$0 sk_?X_29$0 null$0)) :named P15))

(assert (! (Btwn$0 next$0 lst_1$0 (ep$0 next$0 sk_?X_29$0 lst_1$0)
  (ep$0 next$0 sk_?X_29$0 lst_1$0)) :named P16))

(assert (! (Btwn$0 next$0 curr_3$0 (ep$0 next$0 sk_?X_29$0 curr_3$0)
  (ep$0 next$0 sk_?X_29$0 curr_3$0)) :named P17))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P18))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))) :named P19))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_36$0 sk_?X_35$0))
                 (or (in$0 x sk_?X_36$0) (in$0 x sk_?X_35$0)))
            (and (not (in$0 x sk_?X_36$0)) (not (in$0 x sk_?X_35$0))
                 (not (in$0 x (union$0 sk_?X_36$0 sk_?X_35$0)))))) :named P20))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_29$0 FP$0))
                 (or (in$0 x sk_?X_29$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_29$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_29$0 FP$0)))))) :named P21))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_28$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_28$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_28$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_28$0)))))) :named P22))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P23))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_26$0 sk_?X_27$0))
                 (or (in$0 x sk_?X_26$0) (in$0 x sk_?X_27$0)))
            (and (not (in$0 x sk_?X_26$0)) (not (in$0 x sk_?X_27$0))
                 (not (in$0 x (union$0 sk_?X_26$0 sk_?X_27$0)))))) :named P24))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P25))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_32$0 sk_?X_36$0))
                 (or (in$0 x sk_?X_32$0) (in$0 x sk_?X_36$0)))
            (and (not (in$0 x sk_?X_32$0)) (not (in$0 x sk_?X_36$0))
                 (not (in$0 x (union$0 sk_?X_32$0 sk_?X_36$0)))))) :named P26))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_36$0) (in$0 x sk_?X_35$0)
                 (in$0 x (intersection$0 sk_?X_36$0 sk_?X_35$0)))
            (and (or (not (in$0 x sk_?X_36$0)) (not (in$0 x sk_?X_35$0)))
                 (not (in$0 x (intersection$0 sk_?X_36$0 sk_?X_35$0)))))) :named P27))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_32$0) (in$0 x sk_?X_36$0)
                 (in$0 x (intersection$0 sk_?X_32$0 sk_?X_36$0)))
            (and (or (not (in$0 x sk_?X_32$0)) (not (in$0 x sk_?X_36$0)))
                 (not (in$0 x (intersection$0 sk_?X_32$0 sk_?X_36$0)))))) :named P28))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_26$0) (in$0 x sk_?X_27$0)
                 (in$0 x (intersection$0 sk_?X_26$0 sk_?X_27$0)))
            (and (or (not (in$0 x sk_?X_26$0)) (not (in$0 x sk_?X_27$0)))
                 (not (in$0 x (intersection$0 sk_?X_26$0 sk_?X_27$0)))))) :named P29))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_29$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_29$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_29$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_29$0)))))) :named P30))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P31))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 sk_?X_29$0))
                 (not (in$0 x sk_?X_29$0)))
            (and (or (in$0 x sk_?X_29$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 sk_?X_29$0)))))) :named P32))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P33))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P34))

(assert (! (= (read$0 next$0 null$0) null$0) :named P35))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P36))

(assert (! (or (Btwn$0 next$0 curr_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_30$0 next$0 curr_2$0 null$0))) :named P37))

(assert (! (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_36$0 next$0 lst$0 null$0))) :named P38))

(assert (! (or (Btwn$0 next$0 lst_1$0 curr_3$0 curr_3$0)
    (not (lseg_struct$0 sk_?X_25$0 next$0 lst_1$0 curr_3$0))) :named P39))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P40))

(assert (! (= lst_1$0 lst$0) :named P41))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P42))

(assert (! (= (read$0 next$0 elt$0) null$0) :named P43))

(assert (! (= emptyset$0 (intersection$0 sk_?X_36$0 sk_?X_34$0)) :named P44))

(assert (! (= sk_?X_33$0 FP$0) :named P45))

(assert (! (= sk_?X_35$0 (setenum$0 elt$0)) :named P46))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P47))

(assert (! (= emptyset$0 emptyset$0) :named P48))

(assert (! (= sk_?X_25$0 (lseg_domain$0 next$0 lst_1$0 curr_3$0)) :named P49))

(assert (! (= sk_?X_27$0 (lseg_domain$0 next$0 curr_3$0 null$0)) :named P50))

(assert (! (= sk_?X_28$0 (union$0 sk_?X_26$0 sk_?X_27$0)) :named P51))

(assert (! (lseg_struct$0 sk_?X_27$0 next$0 curr_3$0 null$0) :named P52))

(assert (! (= emptyset$0 emptyset$0) :named P53))

(assert (! (= sk_?X_29$0 (union$0 sk_?X_31$0 sk_?X_30$0)) :named P54))

(assert (! (= sk_?X_30$0 (lseg_domain$0 next$0 curr_2$0 null$0)) :named P55))

(assert (! (= sk_?X_32$0 (lseg_domain$0 next$0 lst$0 curr_2$0)) :named P56))

(assert (! (lseg_struct$0 sk_?X_30$0 next$0 curr_2$0 null$0) :named P57))

(assert (! (not (= curr_2$0 null$0)) :named P58))

(assert (! (not (in$0 null$0 Alloc$0)) :named P59))

(assert (! (not (in$0 curr_3$0 FP_2$0)) :named P60))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_3$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_3$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_3$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_3$0 null$0)))))) :named P61))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 curr_2$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 curr_2$0))
                 (not (= l1 curr_2$0)))
            (and (or (= l1 curr_2$0) (not (Btwn$0 next$0 lst$0 l1 curr_2$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 curr_2$0)))))) :named P62))

(assert (! (or (= (read$0 next$0 curr_3$0) null$0) (not nondet_2$0)) :named P63))

(assert (! (or (Btwn$0 next$0 curr_3$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_27$0 next$0 curr_3$0 null$0))) :named P64))

(assert (! (or (Btwn$0 next$0 lst$0 curr_2$0 curr_2$0)
    (not (lseg_struct$0 sk_?X_32$0 next$0 lst$0 curr_2$0))) :named P65))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P66))

(assert (! (= curr_2$0 lst$0) :named P67))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0) :named P68))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P69))

(assert (! (= emptyset$0 emptyset$0) :named P70))

(assert (! (= sk_?X_33$0 (union$0 sk_?X_36$0 sk_?X_34$0)) :named P71))

(assert (! (= sk_?X_34$0 sk_?X_35$0) :named P72))

(assert (! (= sk_?X_36$0 (lseg_domain$0 next$0 lst$0 null$0)) :named P73))

(assert (! (lseg_struct$0 sk_?X_36$0 next$0 lst$0 null$0) :named P74))

(assert (! (= emptyset$0 (intersection$0 sk_?X_26$0 sk_?X_27$0)) :named P75))

(assert (! (= sk_?X_26$0 sk_?X_25$0) :named P76))

(assert (! (= sk_?X_28$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P77))

(assert (! (lseg_struct$0 sk_?X_25$0 next$0 lst_1$0 curr_3$0) :named P78))

(assert (! (not (= curr_3$0 null$0)) :named P79))

(assert (! (= emptyset$0 (intersection$0 sk_?X_31$0 sk_?X_30$0)) :named P80))

(assert (! (= sk_?X_29$0 FP_1$0) :named P81))

(assert (! (= sk_?X_31$0 sk_?X_32$0) :named P82))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P83))

(assert (! (lseg_struct$0 sk_?X_32$0 next$0 lst$0 curr_2$0) :named P84))

(assert (! (not (= lst$0 null$0)) :named P85))

(assert (! (not (in$0 null$0 Alloc$0)) :named P86))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_2$0 null$0)))))) :named P87))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0)))))) :named P88))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst_1$0 l1 curr_3$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst_1$0 curr_3$0))
                 (not (= l1 curr_3$0)))
            (and
                 (or (= l1 curr_3$0)
                     (not (Btwn$0 next$0 lst_1$0 l1 curr_3$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst_1$0 curr_3$0)))))) :named P89))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P90))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P91))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P92))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P93))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P94))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P95))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P96))

(check-sat)

(get-interpolants (and P82 P81 P90 P38 P13 P60 P19 P78 P61 P76 P80 P77 P14 P51 P94 P20 P10 P42 P24 P9 P37 P44 P21 P57 P95 P27 P3 P96 P52 P22 P84 P47 P8 P39 P72 P18 P56 P65 P6 P68 P15 P45 P46 P17 P40 P73 P67 P36 P2) (and P62 P11 P26 P50 P25 P31 P32 P74 P16 P1 P70 P58 P12 P49 P75 P86 P64 P93 P89 P28 P48 P7 P34 P35 P85 P0 P43 P63 P71 P69 P88 P54 P29 P92 P83 P66 P23 P30 P41 P91 P79 P59 P5 P55 P33 P87 P4 P53))

(exit)