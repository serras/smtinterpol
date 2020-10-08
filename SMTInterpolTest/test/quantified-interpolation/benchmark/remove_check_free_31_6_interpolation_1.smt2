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
  tests/spl/sl/sl_remove.spl:31:6-16:This deallocation might be unsafe
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun write$0 (FldLoc Loc Loc) FldLoc)
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
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst$0 () Loc)
(declare-fun lst_1$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_1$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun sk_?X_34$0 () SetLoc)
(declare-fun sk_?X_35$0 () SetLoc)
(declare-fun sk_?X_36$0 () SetLoc)
(declare-fun sk_?X_37$0 () SetLoc)
(declare-fun sk_?X_38$0 () SetLoc)
(declare-fun sk_?X_39$0 () SetLoc)
(declare-fun sk_?X_40$0 () SetLoc)
(declare-fun sk_?X_41$0 () SetLoc)
(declare-fun sk_?X_42$0 () SetLoc)
(declare-fun tmp_2$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 tmp_2$0 ?y ?y)) (= tmp_2$0 ?y)
            (Btwn$0 next$0 tmp_2$0 (read$0 next$0 tmp_2$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y)
            (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 tmp_2$0) tmp_2$0))
            (not (Btwn$0 next$0 tmp_2$0 ?y ?y)) (= tmp_2$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_3$0) curr_3$0))
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y))) :named P5))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P6))

(assert (! (Btwn$0 next$0 tmp_2$0 (read$0 next$0 tmp_2$0) (read$0 next$0 tmp_2$0)) :named P7))

(assert (! (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) (read$0 next$0 curr_3$0)) :named P8))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 FP_1$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P9))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 lst_1$0 (ep$0 next$0 FP_1$0 lst_1$0) ?y)
            (not (Btwn$0 next$0 lst_1$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P10))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_3$0 (ep$0 next$0 FP_1$0 curr_3$0) ?y)
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P11))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 tmp_2$0 (ep$0 next$0 FP_1$0 tmp_2$0) ?y)
            (not (Btwn$0 next$0 tmp_2$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P12))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 null$0) FP_1$0)
    (= null$0 (ep$0 next$0 FP_1$0 null$0))) :named P13))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 lst_1$0) FP_1$0)
    (= lst_1$0 (ep$0 next$0 FP_1$0 lst_1$0))) :named P14))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 curr_3$0) FP_1$0)
    (= curr_3$0 (ep$0 next$0 FP_1$0 curr_3$0))) :named P15))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 tmp_2$0) FP_1$0)
    (= tmp_2$0 (ep$0 next$0 FP_1$0 tmp_2$0))) :named P16))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 FP_1$0 null$0)
  (ep$0 next$0 FP_1$0 null$0)) :named P17))

(assert (! (Btwn$0 next$0 lst_1$0 (ep$0 next$0 FP_1$0 lst_1$0)
  (ep$0 next$0 FP_1$0 lst_1$0)) :named P18))

(assert (! (Btwn$0 next$0 curr_3$0 (ep$0 next$0 FP_1$0 curr_3$0)
  (ep$0 next$0 FP_1$0 curr_3$0)) :named P19))

(assert (! (Btwn$0 next$0 tmp_2$0 (ep$0 next$0 FP_1$0 tmp_2$0)
  (ep$0 next$0 FP_1$0 tmp_2$0)) :named P20))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P21))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))) :named P22))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_1$0 FP$0))
                 (or (in$0 x FP_1$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_1$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_1$0 FP$0)))))) :named P23))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_41$0 FP$0))
                 (or (in$0 x sk_?X_41$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_41$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_41$0 FP$0)))))) :named P24))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_37$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_37$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_37$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_37$0)))))) :named P25))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P26))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_35$0 sk_?X_36$0))
                 (or (in$0 x sk_?X_35$0) (in$0 x sk_?X_36$0)))
            (and (not (in$0 x sk_?X_35$0)) (not (in$0 x sk_?X_36$0))
                 (not (in$0 x (union$0 sk_?X_35$0 sk_?X_36$0)))))) :named P27))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P28))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_41$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 sk_?X_41$0 FP$0)))
            (and (or (not (in$0 x sk_?X_41$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 sk_?X_41$0 FP$0)))))) :named P29))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_35$0) (in$0 x sk_?X_36$0)
                 (in$0 x (intersection$0 sk_?X_35$0 sk_?X_36$0)))
            (and (or (not (in$0 x sk_?X_35$0)) (not (in$0 x sk_?X_36$0)))
                 (not (in$0 x (intersection$0 sk_?X_35$0 sk_?X_36$0)))))) :named P30))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_1$0)
                 (in$0 x (intersection$0 Alloc$0 FP_1$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_1$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_1$0)))))) :named P31))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P32))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 FP_1$0))
                 (not (in$0 x FP_1$0)))
            (and (or (in$0 x FP_1$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 FP_1$0)))))) :named P33))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P34))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P35))

(assert (! (= (read$0 (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0)) curr_3$0)
  (read$0 next$0 tmp_2$0)) :named P36))

(assert (! (or (= null$0 curr_3$0)
    (= (read$0 next$0 null$0)
      (read$0 (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0)) null$0))) :named P37))

(assert (! (or (= tmp_2$0 curr_3$0)
    (= (read$0 next$0 tmp_2$0)
      (read$0 (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0)) tmp_2$0))) :named P38))

(assert (! (or (= curr_3$0 curr_3$0)
    (= (read$0 next$0 curr_3$0)
      (read$0 (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0)) curr_3$0))) :named P39))

(assert (! (= (read$0 next$0 null$0) null$0) :named P40))

(assert (! (= (read$0 next_1$0 null$0) null$0) :named P41))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P42))

(assert (! (or (Btwn$0 next$0 curr_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_39$0 next$0 curr_2$0 null$0))) :named P43))

(assert (! (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_42$0 next$0 lst$0 null$0))) :named P44))

(assert (! (or (Btwn$0 next$0 lst_1$0 curr_3$0 curr_3$0)
    (not (lseg_struct$0 sk_?X_34$0 next$0 lst_1$0 curr_3$0))) :named P45))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P46))

(assert (! (= lst_1$0 lst$0) :named P47))

(assert (! (= tmp_2$0 (read$0 next$0 curr_3$0)) :named P48))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P49))

(assert (! (= emptyset$0 emptyset$0) :named P50))

(assert (! (= sk_?X_34$0 (lseg_domain$0 next$0 lst_1$0 curr_3$0)) :named P51))

(assert (! (= sk_?X_36$0 (lseg_domain$0 next$0 curr_3$0 null$0)) :named P52))

(assert (! (= sk_?X_37$0 (union$0 sk_?X_35$0 sk_?X_36$0)) :named P53))

(assert (! (lseg_struct$0 sk_?X_36$0 next$0 curr_3$0 null$0) :named P54))

(assert (! (= emptyset$0 emptyset$0) :named P55))

(assert (! (= sk_?X_38$0 (union$0 sk_?X_40$0 sk_?X_39$0)) :named P56))

(assert (! (= sk_?X_39$0 (lseg_domain$0 next$0 curr_2$0 null$0)) :named P57))

(assert (! (= sk_?X_41$0 (lseg_domain$0 next$0 lst$0 curr_2$0)) :named P58))

(assert (! (lseg_struct$0 sk_?X_39$0 next$0 curr_2$0 null$0) :named P59))

(assert (! (not (= curr_2$0 null$0)) :named P60))

(assert (! (= sk_?X_42$0 (lseg_domain$0 next$0 lst$0 null$0)) :named P61))

(assert (! (lseg_struct$0 sk_?X_42$0 next$0 lst$0 null$0) :named P62))

(assert (! (not (= tmp_2$0 null$0)) :named P63))

(assert (! (not (in$0 null$0 Alloc$0)) :named P64))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_2$0 null$0)))))) :named P65))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0)))))) :named P66))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst_1$0 l1 curr_3$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst_1$0 curr_3$0))
                 (not (= l1 curr_3$0)))
            (and
                 (or (= l1 curr_3$0)
                     (not (Btwn$0 next$0 lst_1$0 l1 curr_3$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst_1$0 curr_3$0)))))) :named P67))

(assert (! (or (= (read$0 next$0 curr_3$0) null$0) (not nondet_2$0)) :named P68))

(assert (! (or (Btwn$0 next$0 curr_3$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_36$0 next$0 curr_3$0 null$0))) :named P69))

(assert (! (or (Btwn$0 next$0 lst$0 curr_2$0 curr_2$0)
    (not (lseg_struct$0 sk_?X_41$0 next$0 lst$0 curr_2$0))) :named P70))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P71))

(assert (! (= curr_2$0 lst$0) :named P72))

(assert (! (= next_1$0 (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0))) :named P73))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0) :named P74))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P75))

(assert (! (= emptyset$0 (intersection$0 sk_?X_35$0 sk_?X_36$0)) :named P76))

(assert (! (= sk_?X_35$0 sk_?X_34$0) :named P77))

(assert (! (= sk_?X_37$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P78))

(assert (! (lseg_struct$0 sk_?X_34$0 next$0 lst_1$0 curr_3$0) :named P79))

(assert (! (not (= curr_3$0 null$0)) :named P80))

(assert (! (= emptyset$0 (intersection$0 sk_?X_40$0 sk_?X_39$0)) :named P81))

(assert (! (= sk_?X_38$0 FP_1$0) :named P82))

(assert (! (= sk_?X_40$0 sk_?X_41$0) :named P83))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P84))

(assert (! (lseg_struct$0 sk_?X_41$0 next$0 lst$0 curr_2$0) :named P85))

(assert (! (= sk_?X_42$0 FP$0) :named P86))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P87))

(assert (! (not (= lst$0 null$0)) :named P88))

(assert (! (not (in$0 null$0 Alloc$0)) :named P89))

(assert (! (not (in$0 tmp_2$0 FP_2$0)) :named P90))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_3$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_3$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_3$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_3$0 null$0)))))) :named P91))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 curr_2$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 curr_2$0))
                 (not (= l1 curr_2$0)))
            (and (or (= l1 curr_2$0) (not (Btwn$0 next$0 lst$0 l1 curr_2$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 curr_2$0)))))) :named P92))

(assert (! (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or
                 (Btwn$0 (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0)) ?z
                   ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v curr_3$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z curr_3$0
                                               curr_3$0)))))
                          (and (not (= curr_3$0 ?v))
                               (or (Btwn$0 next$0 ?z curr_3$0 ?v)
                                   (and (Btwn$0 next$0 ?z curr_3$0 curr_3$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u curr_3$0)
                               (or
                                   (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?v
                                     curr_3$0)
                                   (and
                                        (Btwn$0 next$0
                                          (read$0 next$0 tmp_2$0) ?v ?v)
                                        (not
                                             (Btwn$0 next$0
                                               (read$0 next$0 tmp_2$0)
                                               curr_3$0 curr_3$0)))))
                          (and (not (= curr_3$0 ?v))
                               (or (Btwn$0 next$0 ?z curr_3$0 ?v)
                                   (and (Btwn$0 next$0 ?z curr_3$0 curr_3$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?u ?v)
                               (or
                                   (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?v
                                     curr_3$0)
                                   (and
                                        (Btwn$0 next$0
                                          (read$0 next$0 tmp_2$0) ?v ?v)
                                        (not
                                             (Btwn$0 next$0
                                               (read$0 next$0 tmp_2$0)
                                               curr_3$0 curr_3$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v curr_3$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z curr_3$0 curr_3$0)))))
                 (and (not (= curr_3$0 ?v))
                      (or (Btwn$0 next$0 ?z curr_3$0 ?v)
                          (and (Btwn$0 next$0 ?z curr_3$0 curr_3$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u curr_3$0)
                      (or (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?v curr_3$0)
                          (and (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?v ?v)
                               (not
                                    (Btwn$0 next$0 (read$0 next$0 tmp_2$0)
                                      curr_3$0 curr_3$0)))))
                 (and (not (= curr_3$0 ?v))
                      (or (Btwn$0 next$0 ?z curr_3$0 ?v)
                          (and (Btwn$0 next$0 ?z curr_3$0 curr_3$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?u ?v)
                      (or (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?v curr_3$0)
                          (and (Btwn$0 next$0 (read$0 next$0 tmp_2$0) ?v ?v)
                               (not
                                    (Btwn$0 next$0 (read$0 next$0 tmp_2$0)
                                      curr_3$0 curr_3$0)))))
                 (not
                      (Btwn$0
                        (write$0 next$0 curr_3$0 (read$0 next$0 tmp_2$0)) ?z
                        ?u ?v))))) :named P93))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P94))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P95))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P96))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P97))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P98))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P99))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P100))

(check-sat)

(get-interpolants (and P95 P4 P31 P66 P21 P58 P28 P100 P3 P56 P62 P13 P53 P9 P27 P7 P80 P26 P30 P82 P92 P10 P29 P59 P34 P67 P50 P75 P73 P15 P79 P84 P98 P11 P17 P24 P76 P99 P69 P42 P44 P63 P18 P83 P47 P0 P96 P41 P77 P68 P38) (and P20 P48 P32 P2 P35 P16 P89 P90 P25 P43 P5 P46 P6 P71 P85 P70 P60 P36 P8 P93 P94 P57 P52 P86 P97 P55 P61 P14 P19 P88 P78 P54 P64 P74 P91 P22 P81 P72 P51 P12 P23 P49 P45 P39 P33 P1 P87 P37 P65 P40))

(exit)