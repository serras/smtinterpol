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
  tests/spl/sl/rec_concat.spl:30:2-14:Possible heap access through null or dangling reference
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
(declare-fun FP_3$0 () SetLoc)
(declare-fun FP_4$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun a_1$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun l_5$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun sk_?X_42$0 () SetLoc)
(declare-fun sk_?X_43$0 () SetLoc)
(declare-fun sk_?X_44$0 () SetLoc)
(declare-fun sk_?X_45$0 () SetLoc)
(declare-fun sk_?X_46$0 () SetLoc)
(declare-fun sk_?X_47$0 () SetLoc)
(declare-fun sk_?X_48$0 () SetLoc)
(declare-fun sk_?X_49$0 () SetLoc)
(declare-fun sk_?X_50$0 () SetLoc)
(declare-fun sk_?X_51$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 l_5$0 ?y ?y)) (= l_5$0 ?y)
            (Btwn$0 next$0 l_5$0 (read$0 next$0 l_5$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 l_5$0) l_5$0))
            (not (Btwn$0 next$0 l_5$0 ?y ?y)) (= l_5$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 l_5$0 (read$0 next$0 l_5$0) (read$0 next$0 l_5$0)) :named P4))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P5))

(assert (! (or (in$0 (ep$0 next$0 FP_3$0 null$0) FP_3$0)
    (= null$0 (ep$0 next$0 FP_3$0 null$0))) :named P6))

(assert (! (or (in$0 (ep$0 next$0 FP_3$0 a_1$0) FP_3$0)
    (= a_1$0 (ep$0 next$0 FP_3$0 a_1$0))) :named P7))

(assert (! (or (in$0 (ep$0 next$0 FP_3$0 b$0) FP_3$0) (= b$0 (ep$0 next$0 FP_3$0 b$0))) :named P8))

(assert (! (or (in$0 (ep$0 next$0 FP_3$0 l_5$0) FP_3$0)
    (= l_5$0 (ep$0 next$0 FP_3$0 l_5$0))) :named P9))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 FP_3$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y FP_3$0)))) :named P10))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 a_1$0 (ep$0 next$0 FP_3$0 a_1$0) ?y)
            (not (Btwn$0 next$0 a_1$0 ?y ?y)) (not (in$0 ?y FP_3$0)))) :named P11))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 b$0 (ep$0 next$0 FP_3$0 b$0) ?y)
            (not (Btwn$0 next$0 b$0 ?y ?y)) (not (in$0 ?y FP_3$0)))) :named P12))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 l_5$0 (ep$0 next$0 FP_3$0 l_5$0) ?y)
            (not (Btwn$0 next$0 l_5$0 ?y ?y)) (not (in$0 ?y FP_3$0)))) :named P13))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 FP_3$0 null$0)
  (ep$0 next$0 FP_3$0 null$0)) :named P14))

(assert (! (Btwn$0 next$0 a_1$0 (ep$0 next$0 FP_3$0 a_1$0) (ep$0 next$0 FP_3$0 a_1$0)) :named P15))

(assert (! (Btwn$0 next$0 b$0 (ep$0 next$0 FP_3$0 b$0) (ep$0 next$0 FP_3$0 b$0)) :named P16))

(assert (! (Btwn$0 next$0 l_5$0 (ep$0 next$0 FP_3$0 l_5$0) (ep$0 next$0 FP_3$0 l_5$0)) :named P17))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P18))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_4$0 Alloc$0))
                 (or (in$0 x FP_4$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_4$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_4$0 Alloc$0)))))) :named P19))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_3$0 sk_?X_43$0))
                 (or (in$0 x FP_3$0) (in$0 x sk_?X_43$0)))
            (and (not (in$0 x FP_3$0)) (not (in$0 x sk_?X_43$0))
                 (not (in$0 x (union$0 FP_3$0 sk_?X_43$0)))))) :named P20))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_3$0 FP$0))
                 (or (in$0 x FP_3$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_3$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_3$0 FP$0)))))) :named P21))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_3$0) sk_?X_49$0))
                 (or (in$0 x (setminus$0 FP$0 FP_3$0)) (in$0 x sk_?X_49$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_3$0)))
                 (not (in$0 x sk_?X_49$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_3$0) sk_?X_49$0)))))) :named P22))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P23))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_46$0 sk_?X_48$0))
                 (or (in$0 x sk_?X_46$0) (in$0 x sk_?X_48$0)))
            (and (not (in$0 x sk_?X_46$0)) (not (in$0 x sk_?X_48$0))
                 (not (in$0 x (union$0 sk_?X_46$0 sk_?X_48$0)))))) :named P24))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_3$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_3$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_3$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_3$0)
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P25))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_46$0) (in$0 x sk_?X_48$0)
                 (in$0 x (intersection$0 sk_?X_46$0 sk_?X_48$0)))
            (and (or (not (in$0 x sk_?X_46$0)) (not (in$0 x sk_?X_48$0)))
                 (not (in$0 x (intersection$0 sk_?X_46$0 sk_?X_48$0)))))) :named P26))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_3$0) (in$0 x sk_?X_43$0)
                 (in$0 x (intersection$0 FP_3$0 sk_?X_43$0)))
            (and (or (not (in$0 x FP_3$0)) (not (in$0 x sk_?X_43$0)))
                 (not (in$0 x (intersection$0 FP_3$0 sk_?X_43$0)))))) :named P27))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_3$0)
                 (in$0 x (intersection$0 Alloc$0 FP_3$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_3$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_3$0)))))) :named P28))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P29))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 FP_3$0))
                 (not (in$0 x FP_3$0)))
            (and (or (in$0 x FP_3$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 FP_3$0)))))) :named P30))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P31))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P32))

(assert (! (= (read$0 next$0 null$0) null$0) :named P33))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P34))

(assert (! (or (Btwn$0 next$0 a_1$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_45$0 next$0 a_1$0 null$0))) :named P35))

(assert (! (or (Btwn$0 next$0 a_1$0 l_5$0 l_5$0)
    (not (lseg_struct$0 sk_?X_46$0 next$0 a_1$0 l_5$0))) :named P36))

(assert (! (= FP_4$0
  (union$0 (setminus$0 FP$0 FP_3$0)
    (union$0 (intersection$0 Alloc$0 FP_3$0) (setminus$0 Alloc$0 Alloc$0)))) :named P37))

(assert (! (Frame$0 FP_3$0 Alloc$0 next$0 next$0) :named P38))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P39))

(assert (! (= emptyset$0 emptyset$0) :named P40))

(assert (! (= sk_?X_46$0 (lseg_domain$0 next$0 a_1$0 l_5$0)) :named P41))

(assert (! (= sk_?X_48$0 sk_?X_47$0) :named P42))

(assert (! (= sk_?X_49$0 (union$0 sk_?X_46$0 sk_?X_48$0)) :named P43))

(assert (! (= emptyset$0 emptyset$0) :named P44))

(assert (! (= sk_?X_42$0 (union$0 sk_?X_44$0 sk_?X_43$0)) :named P45))

(assert (! (= sk_?X_43$0 (lseg_domain$0 next$0 b$0 null$0)) :named P46))

(assert (! (= sk_?X_45$0 (lseg_domain$0 next$0 a_1$0 null$0)) :named P47))

(assert (! (lseg_struct$0 sk_?X_43$0 next$0 b$0 null$0) :named P48))

(assert (! (not (= a_1$0 null$0)) :named P49))

(assert (! (= sk_?X_50$0 sk_?X_51$0) :named P50))

(assert (! (= sk_?X_51$0 (lseg_domain$0 next$0 a_1$0 null$0)) :named P51))

(assert (! (lseg_struct$0 sk_?X_51$0 next$0 a_1$0 null$0) :named P52))

(assert (! (not (in$0 null$0 Alloc$0)) :named P53))

(assert (! (not (in$0 l_5$0 FP_4$0)) :named P54))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_1$0 l1 l_5$0)
                 (in$0 l1 (lseg_domain$0 next$0 a_1$0 l_5$0))
                 (not (= l1 l_5$0)))
            (and (or (= l1 l_5$0) (not (Btwn$0 next$0 a_1$0 l1 l_5$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 a_1$0 l_5$0)))))) :named P55))

(assert (! (or (Btwn$0 next$0 a_1$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_51$0 next$0 a_1$0 null$0))) :named P56))

(assert (! (or (Btwn$0 next$0 b$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_43$0 next$0 b$0 null$0))) :named P57))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P58))

(assert (! (= Alloc$0 (union$0 FP_4$0 Alloc$0)) :named P59))

(assert (! (= (read$0 next$0 l_5$0) null$0) :named P60))

(assert (! (= emptyset$0 (intersection$0 sk_?X_46$0 sk_?X_48$0)) :named P61))

(assert (! (= sk_?X_47$0 (setenum$0 l_5$0)) :named P62))

(assert (! (= sk_?X_49$0
  (union$0 (intersection$0 Alloc$0 FP_3$0) (setminus$0 Alloc$0 Alloc$0))) :named P63))

(assert (! (lseg_struct$0 sk_?X_46$0 next$0 a_1$0 l_5$0) :named P64))

(assert (! (= emptyset$0 (intersection$0 sk_?X_44$0 sk_?X_43$0)) :named P65))

(assert (! (= sk_?X_42$0 FP$0) :named P66))

(assert (! (= sk_?X_44$0 sk_?X_45$0) :named P67))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P68))

(assert (! (lseg_struct$0 sk_?X_45$0 next$0 a_1$0 null$0) :named P69))

(assert (! (= emptyset$0 emptyset$0) :named P70))

(assert (! (= sk_?X_50$0 FP_3$0) :named P71))

(assert (! (= FP$0 (union$0 FP_3$0 FP$0)) :named P72))

(assert (! (not (= a_1$0 null$0)) :named P73))

(assert (! (not (in$0 null$0 Alloc$0)) :named P74))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_1$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 a_1$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a_1$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 a_1$0 null$0)))))) :named P75))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 b$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 b$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 b$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 b$0 null$0)))))) :named P76))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P77))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P78))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P79))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P80))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P81))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P82))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P83))

(check-sat)

(get-interpolants (and P50 P7 P73 P57 P77 P31 P12 P5 P72 P16 P60 P79 P70 P54 P67 P38 P23 P43 P40 P14 P35 P17 P41 P68 P71 P52 P46 P59 P39 P56 P3 P74 P62 P29 P82 P66 P83 P80 P44 P53 P51 P19) (and P36 P76 P34 P1 P4 P48 P13 P47 P42 P6 P81 P20 P75 P61 P0 P45 P21 P24 P55 P32 P37 P27 P9 P65 P78 P69 P49 P8 P33 P2 P10 P15 P18 P30 P11 P26 P28 P64 P58 P22 P25 P63))

(exit)