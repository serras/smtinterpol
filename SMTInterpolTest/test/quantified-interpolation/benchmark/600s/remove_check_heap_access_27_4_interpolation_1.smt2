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
  tests/spl/sl/sl_remove.spl:27:4-21:Possible heap access through null or dangling reference
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
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst$0 () Loc)
(declare-fun lst_1$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun sk_?X_7$0 () SetLoc)
(declare-fun sk_?X_8$0 () SetLoc)
(declare-fun sk_?X_9$0 () SetLoc)
(declare-fun sk_?X_10$0 () SetLoc)
(declare-fun sk_?X_11$0 () SetLoc)
(declare-fun sk_?X_12$0 () SetLoc)
(declare-fun sk_?X_13$0 () SetLoc)
(declare-fun sk_?X_14$0 () SetLoc)
(declare-fun sk_?X_15$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y)
            (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 curr_3$0) curr_3$0))
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (= curr_3$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P4))

(assert (! (Btwn$0 next$0 curr_3$0 (read$0 next$0 curr_3$0) (read$0 next$0 curr_3$0)) :named P5))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 null$0) FP_1$0)
    (= null$0 (ep$0 next$0 FP_1$0 null$0))) :named P6))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 lst_1$0) FP_1$0)
    (= lst_1$0 (ep$0 next$0 FP_1$0 lst_1$0))) :named P7))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 curr_3$0) FP_1$0)
    (= curr_3$0 (ep$0 next$0 FP_1$0 curr_3$0))) :named P8))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 FP_1$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P9))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 lst_1$0 (ep$0 next$0 FP_1$0 lst_1$0) ?y)
            (not (Btwn$0 next$0 lst_1$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P10))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_3$0 (ep$0 next$0 FP_1$0 curr_3$0) ?y)
            (not (Btwn$0 next$0 curr_3$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P11))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 FP_1$0 null$0)
  (ep$0 next$0 FP_1$0 null$0)) :named P12))

(assert (! (Btwn$0 next$0 lst_1$0 (ep$0 next$0 FP_1$0 lst_1$0)
  (ep$0 next$0 FP_1$0 lst_1$0)) :named P13))

(assert (! (Btwn$0 next$0 curr_3$0 (ep$0 next$0 FP_1$0 curr_3$0)
  (ep$0 next$0 FP_1$0 curr_3$0)) :named P14))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P15))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))) :named P16))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_1$0 FP$0))
                 (or (in$0 x FP_1$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_1$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_1$0 FP$0)))))) :named P17))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_14$0 FP$0))
                 (or (in$0 x sk_?X_14$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_14$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_14$0 FP$0)))))) :named P18))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_10$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_10$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_10$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_10$0)))))) :named P19))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P20))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_8$0 sk_?X_9$0))
                 (or (in$0 x sk_?X_8$0) (in$0 x sk_?X_9$0)))
            (and (not (in$0 x sk_?X_8$0)) (not (in$0 x sk_?X_9$0))
                 (not (in$0 x (union$0 sk_?X_8$0 sk_?X_9$0)))))) :named P21))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P22))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_14$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 sk_?X_14$0 FP$0)))
            (and (or (not (in$0 x sk_?X_14$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 sk_?X_14$0 FP$0)))))) :named P23))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_8$0) (in$0 x sk_?X_9$0)
                 (in$0 x (intersection$0 sk_?X_8$0 sk_?X_9$0)))
            (and (or (not (in$0 x sk_?X_8$0)) (not (in$0 x sk_?X_9$0)))
                 (not (in$0 x (intersection$0 sk_?X_8$0 sk_?X_9$0)))))) :named P24))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_1$0)
                 (in$0 x (intersection$0 Alloc$0 FP_1$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_1$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_1$0)))))) :named P25))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P26))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 FP_1$0))
                 (not (in$0 x FP_1$0)))
            (and (or (in$0 x FP_1$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 FP_1$0)))))) :named P27))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P28))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P29))

(assert (! (= (read$0 next$0 null$0) null$0) :named P30))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P31))

(assert (! (or (Btwn$0 next$0 curr_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_12$0 next$0 curr_2$0 null$0))) :named P32))

(assert (! (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_15$0 next$0 lst$0 null$0))) :named P33))

(assert (! (or (Btwn$0 next$0 lst_1$0 curr_3$0 curr_3$0)
    (not (lseg_struct$0 sk_?X_7$0 next$0 lst_1$0 curr_3$0))) :named P34))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P35))

(assert (! (= lst_1$0 lst$0) :named P36))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P37))

(assert (! (= emptyset$0 emptyset$0) :named P38))

(assert (! (= sk_?X_7$0 (lseg_domain$0 next$0 lst_1$0 curr_3$0)) :named P39))

(assert (! (= sk_?X_9$0 (lseg_domain$0 next$0 curr_3$0 null$0)) :named P40))

(assert (! (= sk_?X_10$0 (union$0 sk_?X_8$0 sk_?X_9$0)) :named P41))

(assert (! (lseg_struct$0 sk_?X_9$0 next$0 curr_3$0 null$0) :named P42))

(assert (! (= emptyset$0 emptyset$0) :named P43))

(assert (! (= sk_?X_11$0 (union$0 sk_?X_13$0 sk_?X_12$0)) :named P44))

(assert (! (= sk_?X_12$0 (lseg_domain$0 next$0 curr_2$0 null$0)) :named P45))

(assert (! (= sk_?X_14$0 (lseg_domain$0 next$0 lst$0 curr_2$0)) :named P46))

(assert (! (lseg_struct$0 sk_?X_12$0 next$0 curr_2$0 null$0) :named P47))

(assert (! (not (= curr_2$0 null$0)) :named P48))

(assert (! (= sk_?X_15$0 (lseg_domain$0 next$0 lst$0 null$0)) :named P49))

(assert (! (lseg_struct$0 sk_?X_15$0 next$0 lst$0 null$0) :named P50))

(assert (! (not (in$0 null$0 Alloc$0)) :named P51))

(assert (! (not (in$0 curr_3$0 FP_2$0)) :named P52))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_3$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_3$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_3$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_3$0 null$0)))))) :named P53))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 curr_2$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 curr_2$0))
                 (not (= l1 curr_2$0)))
            (and (or (= l1 curr_2$0) (not (Btwn$0 next$0 lst$0 l1 curr_2$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 curr_2$0)))))) :named P54))

(assert (! (or (= (read$0 next$0 curr_3$0) null$0) (not nondet_2$0)) :named P55))

(assert (! (or (Btwn$0 next$0 curr_3$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_9$0 next$0 curr_3$0 null$0))) :named P56))

(assert (! (or (Btwn$0 next$0 lst$0 curr_2$0 curr_2$0)
    (not (lseg_struct$0 sk_?X_14$0 next$0 lst$0 curr_2$0))) :named P57))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P58))

(assert (! (= curr_2$0 lst$0) :named P59))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0) :named P60))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P61))

(assert (! (= emptyset$0 (intersection$0 sk_?X_8$0 sk_?X_9$0)) :named P62))

(assert (! (= sk_?X_8$0 sk_?X_7$0) :named P63))

(assert (! (= sk_?X_10$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P64))

(assert (! (lseg_struct$0 sk_?X_7$0 next$0 lst_1$0 curr_3$0) :named P65))

(assert (! (not (= curr_3$0 null$0)) :named P66))

(assert (! (= emptyset$0 (intersection$0 sk_?X_13$0 sk_?X_12$0)) :named P67))

(assert (! (= sk_?X_11$0 FP_1$0) :named P68))

(assert (! (= sk_?X_13$0 sk_?X_14$0) :named P69))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P70))

(assert (! (lseg_struct$0 sk_?X_14$0 next$0 lst$0 curr_2$0) :named P71))

(assert (! (= sk_?X_15$0 FP$0) :named P72))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P73))

(assert (! (not (= lst$0 null$0)) :named P74))

(assert (! (not (in$0 null$0 Alloc$0)) :named P75))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_2$0 null$0)))))) :named P76))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0)))))) :named P77))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst_1$0 l1 curr_3$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst_1$0 curr_3$0))
                 (not (= l1 curr_3$0)))
            (and
                 (or (= l1 curr_3$0)
                     (not (Btwn$0 next$0 lst_1$0 l1 curr_3$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst_1$0 curr_3$0)))))) :named P78))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P79))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P80))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P81))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P82))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P83))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P84))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P85))

(check-sat)

(get-interpolants (and P21 P31 P68 P18 P16 P5 P41 P30 P42 P50 P12 P70 P44 P24 P45 P69 P34 P22 P9 P36 P67 P13 P58 P55 P85 P65 P6 P63 P49 P59 P74 P17 P7 P82 P14 P29 P1 P43 P60 P71 P73 P51 P66) (and P48 P38 P3 P57 P11 P33 P39 P0 P64 P62 P35 P52 P19 P56 P54 P10 P47 P15 P32 P84 P2 P26 P83 P72 P77 P76 P28 P23 P80 P20 P8 P61 P75 P46 P81 P79 P53 P27 P25 P37 P78 P40 P4))

(exit)