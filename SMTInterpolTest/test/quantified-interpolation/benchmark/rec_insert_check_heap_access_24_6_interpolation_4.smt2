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
  tests/spl/sl/rec_insert.spl:24:6-21:Possible heap access through null or dangling reference
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
(declare-fun elt$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst$0 () Loc)
(declare-fun n1_2$0 () Loc)
(declare-fun n2_2$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_1$0 () FldLoc)
(declare-fun nondet_1$0 () Bool)
(declare-fun sk_?X_26$0 () SetLoc)
(declare-fun sk_?X_27$0 () SetLoc)
(declare-fun sk_?X_28$0 () SetLoc)
(declare-fun sk_?X_29$0 () SetLoc)
(declare-fun sk_?X_30$0 () SetLoc)
(declare-fun sk_?X_31$0 () SetLoc)
(declare-fun sk_?X_32$0 () SetLoc)
(declare-fun sk_?X_33$0 () SetLoc)
(declare-fun sk_?X_34$0 () SetLoc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 elt$0 ?y ?y)) (= elt$0 ?y)
            (Btwn$0 next$0 elt$0 (read$0 next$0 elt$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 lst$0 ?y ?y)) (= lst$0 ?y)
            (Btwn$0 next$0 lst$0 (read$0 next$0 lst$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_1$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_1$0 null$0 (read$0 next_1$0 null$0) ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_1$0 elt$0 ?y ?y)) (= elt$0 ?y)
            (Btwn$0 next_1$0 elt$0 (read$0 next_1$0 elt$0) ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next_1$0 lst$0 ?y ?y)) (= lst$0 ?y)
            (Btwn$0 next_1$0 lst$0 (read$0 next_1$0 lst$0) ?y))) :named P5))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 elt$0) elt$0))
            (not (Btwn$0 next$0 elt$0 ?y ?y)) (= elt$0 ?y))) :named P6))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P7))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 lst$0) lst$0))
            (not (Btwn$0 next$0 lst$0 ?y ?y)) (= lst$0 ?y))) :named P8))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_1$0 null$0) null$0))
            (not (Btwn$0 next_1$0 null$0 ?y ?y)) (= null$0 ?y))) :named P9))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_1$0 elt$0) elt$0))
            (not (Btwn$0 next_1$0 elt$0 ?y ?y)) (= elt$0 ?y))) :named P10))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next_1$0 lst$0) lst$0))
            (not (Btwn$0 next_1$0 lst$0 ?y ?y)) (= lst$0 ?y))) :named P11))

(assert (! (Btwn$0 next$0 elt$0 (read$0 next$0 elt$0) (read$0 next$0 elt$0)) :named P12))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P13))

(assert (! (Btwn$0 next$0 lst$0 (read$0 next$0 lst$0) (read$0 next$0 lst$0)) :named P14))

(assert (! (Btwn$0 next_1$0 null$0 (read$0 next_1$0 null$0) (read$0 next_1$0 null$0)) :named P15))

(assert (! (Btwn$0 next_1$0 elt$0 (read$0 next_1$0 elt$0) (read$0 next_1$0 elt$0)) :named P16))

(assert (! (Btwn$0 next_1$0 lst$0 (read$0 next_1$0 lst$0) (read$0 next_1$0 lst$0)) :named P17))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 next$0 null$0) (read$0 next_1$0 null$0))
        (not (in$0 null$0 (setminus$0 Alloc$0 FP_1$0))))) :named P18))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 next$0 elt$0) (read$0 next_1$0 elt$0))
        (not (in$0 elt$0 (setminus$0 Alloc$0 FP_1$0))))) :named P19))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 next$0 lst$0) (read$0 next_1$0 lst$0))
        (not (in$0 lst$0 (setminus$0 Alloc$0 FP_1$0))))) :named P20))

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
                                     (ep$0 next$0 FP_1$0 null$0))))))))) :named P21))

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
                                     (ep$0 next$0 FP_1$0 lst$0))))))))) :named P22))

(assert (! (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 n1_2$0 ?z ?y)
                     (Btwn$0 next_1$0 n1_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 n1_2$0 ?z ?y))
                     (not (Btwn$0 next_1$0 n1_2$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 n1_2$0 ?y
                           (ep$0 next$0 FP_1$0 n1_2$0))
                         (and (Btwn$0 next$0 n1_2$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 n1_2$0
                                     (ep$0 next$0 FP_1$0 n1_2$0)
                                     (ep$0 next$0 FP_1$0 n1_2$0))))))))) :named P23))

(assert (! (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 n2_2$0 ?z ?y)
                     (Btwn$0 next_1$0 n2_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 n2_2$0 ?z ?y))
                     (not (Btwn$0 next_1$0 n2_2$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 n2_2$0 ?y
                           (ep$0 next$0 FP_1$0 n2_2$0))
                         (and (Btwn$0 next$0 n2_2$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 n2_2$0
                                     (ep$0 next$0 FP_1$0 n2_2$0)
                                     (ep$0 next$0 FP_1$0 n2_2$0))))))))) :named P24))

(assert (! (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 null$0 FP_1$0)
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_1$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_1$0 null$0 ?z ?y)))
                (not (= null$0 (ep$0 next$0 FP_1$0 null$0)))))) :named P25))

(assert (! (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 lst$0 FP_1$0)
                (and (Btwn$0 next$0 lst$0 ?z ?y)
                     (Btwn$0 next_1$0 lst$0 ?z ?y))
                (and (not (Btwn$0 next$0 lst$0 ?z ?y))
                     (not (Btwn$0 next_1$0 lst$0 ?z ?y)))
                (not (= lst$0 (ep$0 next$0 FP_1$0 lst$0)))))) :named P26))

(assert (! (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 n1_2$0 FP_1$0)
                (and (Btwn$0 next$0 n1_2$0 ?z ?y)
                     (Btwn$0 next_1$0 n1_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 n1_2$0 ?z ?y))
                     (not (Btwn$0 next_1$0 n1_2$0 ?z ?y)))
                (not (= n1_2$0 (ep$0 next$0 FP_1$0 n1_2$0)))))) :named P27))

(assert (! (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 n2_2$0 FP_1$0)
                (and (Btwn$0 next$0 n2_2$0 ?z ?y)
                     (Btwn$0 next_1$0 n2_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 n2_2$0 ?z ?y))
                     (not (Btwn$0 next_1$0 n2_2$0 ?z ?y)))
                (not (= n2_2$0 (ep$0 next$0 FP_1$0 n2_2$0)))))) :named P28))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 FP_1$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P29))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 lst$0 (ep$0 next$0 FP_1$0 lst$0) ?y)
            (not (Btwn$0 next$0 lst$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P30))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 n1_2$0 (ep$0 next$0 FP_1$0 n1_2$0) ?y)
            (not (Btwn$0 next$0 n1_2$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P31))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 n2_2$0 (ep$0 next$0 FP_1$0 n2_2$0) ?y)
            (not (Btwn$0 next$0 n2_2$0 ?y ?y)) (not (in$0 ?y FP_1$0)))) :named P32))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 null$0) FP_1$0)
    (= null$0 (ep$0 next$0 FP_1$0 null$0))) :named P33))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 lst$0) FP_1$0)
    (= lst$0 (ep$0 next$0 FP_1$0 lst$0))) :named P34))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 n1_2$0) FP_1$0)
    (= n1_2$0 (ep$0 next$0 FP_1$0 n1_2$0))) :named P35))

(assert (! (or (in$0 (ep$0 next$0 FP_1$0 n2_2$0) FP_1$0)
    (= n2_2$0 (ep$0 next$0 FP_1$0 n2_2$0))) :named P36))

(assert (! (Btwn$0 next$0 null$0 (ep$0 next$0 FP_1$0 null$0)
  (ep$0 next$0 FP_1$0 null$0)) :named P37))

(assert (! (Btwn$0 next$0 lst$0 (ep$0 next$0 FP_1$0 lst$0) (ep$0 next$0 FP_1$0 lst$0)) :named P38))

(assert (! (Btwn$0 next$0 n1_2$0 (ep$0 next$0 FP_1$0 n1_2$0)
  (ep$0 next$0 FP_1$0 n1_2$0)) :named P39))

(assert (! (Btwn$0 next$0 n2_2$0 (ep$0 next$0 FP_1$0 n2_2$0)
  (ep$0 next$0 FP_1$0 n2_2$0)) :named P40))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P41))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))) :named P42))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_34$0 sk_?X_29$0))
                 (or (in$0 x sk_?X_34$0) (in$0 x sk_?X_29$0)))
            (and (not (in$0 x sk_?X_34$0)) (not (in$0 x sk_?X_29$0))
                 (not (in$0 x (union$0 sk_?X_34$0 sk_?X_29$0)))))) :named P43))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_1$0 FP$0))
                 (or (in$0 x FP_1$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_1$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_1$0 FP$0)))))) :named P44))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_30$0 sk_?X_29$0))
                 (or (in$0 x sk_?X_30$0) (in$0 x sk_?X_29$0)))
            (and (not (in$0 x sk_?X_30$0)) (not (in$0 x sk_?X_29$0))
                 (not (in$0 x (union$0 sk_?X_30$0 sk_?X_29$0)))))) :named P45))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_26$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_26$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_26$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_26$0)))))) :named P46))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P47))

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
                          (setminus$0 Alloc$0 Alloc$0))))))) :named P48))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_34$0) (in$0 x sk_?X_29$0)
                 (in$0 x (intersection$0 sk_?X_34$0 sk_?X_29$0)))
            (and (or (not (in$0 x sk_?X_34$0)) (not (in$0 x sk_?X_29$0)))
                 (not (in$0 x (intersection$0 sk_?X_34$0 sk_?X_29$0)))))) :named P49))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_30$0) (in$0 x sk_?X_29$0)
                 (in$0 x (intersection$0 sk_?X_30$0 sk_?X_29$0)))
            (and (or (not (in$0 x sk_?X_30$0)) (not (in$0 x sk_?X_29$0)))
                 (not (in$0 x (intersection$0 sk_?X_30$0 sk_?X_29$0)))))) :named P50))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_1$0)
                 (in$0 x (intersection$0 Alloc$0 FP_1$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_1$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_1$0)))))) :named P51))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))) :named P52))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 FP_1$0))
                 (not (in$0 x FP_1$0)))
            (and (or (in$0 x FP_1$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 FP_1$0)))))) :named P53))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 FP_1$0))
                 (not (in$0 x FP_1$0)))
            (and (or (in$0 x FP_1$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 FP_1$0)))))) :named P54))

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

(assert (! (= (read$0 next_1$0 null$0) null$0) :named P58))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P59))

(assert (! (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_34$0 next$0 lst$0 null$0))) :named P60))

(assert (! (or (Btwn$0 next_1$0 n2_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_26$0 next_1$0 n2_2$0 null$0))) :named P61))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P62))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next_1$0) :named P63))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P64))

(assert (! (= emptyset$0 emptyset$0) :named P65))

(assert (! (= sk_?X_27$0 (union$0 sk_?X_30$0 sk_?X_28$0)) :named P66))

(assert (! (= sk_?X_28$0 sk_?X_29$0) :named P67))

(assert (! (= sk_?X_30$0 (lseg_domain$0 next$0 n1_2$0 null$0)) :named P68))

(assert (! (lseg_struct$0 sk_?X_30$0 next$0 n1_2$0 null$0) :named P69))

(assert (! (= emptyset$0 emptyset$0) :named P70))

(assert (! (= sk_?X_31$0 (union$0 sk_?X_34$0 sk_?X_32$0)) :named P71))

(assert (! (= sk_?X_32$0 sk_?X_33$0) :named P72))

(assert (! (= sk_?X_34$0 (lseg_domain$0 next$0 lst$0 null$0)) :named P73))

(assert (! (lseg_struct$0 sk_?X_34$0 next$0 lst$0 null$0) :named P74))

(assert (! (= sk_?X_26$0 (lseg_domain$0 next_1$0 n2_2$0 null$0)) :named P75))

(assert (! (not (= lst$0 null$0)) :named P76))

(assert (! (not (in$0 null$0 Alloc$0)) :named P77))

(assert (! (not nondet_1$0) :named P78))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 n1_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 n1_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 n1_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 n1_2$0 null$0)))))) :named P79))

(assert (! (or (and Axiom_2$0 Axiom_1$0 Axiom$0)
    (not (Frame$0 FP_1$0 Alloc$0 next$0 next_1$0))) :named P80))

(assert (! (or (Btwn$0 next$0 n1_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_30$0 next$0 n1_2$0 null$0))) :named P81))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))) :named P82))

(assert (! (= n1_2$0 (read$0 next$0 lst$0)) :named P83))

(assert (! (= Alloc$0 (union$0 FP_2$0 Alloc$0)) :named P84))

(assert (! (= (read$0 next$0 elt$0) null$0) :named P85))

(assert (! (= emptyset$0 (intersection$0 sk_?X_30$0 sk_?X_28$0)) :named P86))

(assert (! (= sk_?X_27$0 FP_1$0) :named P87))

(assert (! (= sk_?X_29$0 (setenum$0 elt$0)) :named P88))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P89))

(assert (! (= (read$0 next$0 elt$0) null$0) :named P90))

(assert (! (= emptyset$0 (intersection$0 sk_?X_34$0 sk_?X_32$0)) :named P91))

(assert (! (= sk_?X_31$0 FP$0) :named P92))

(assert (! (= sk_?X_33$0 (setenum$0 elt$0)) :named P93))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P94))

(assert (! (= sk_?X_26$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))) :named P95))

(assert (! (lseg_struct$0 sk_?X_26$0 next_1$0 n2_2$0 null$0) :named P96))

(assert (! (not (in$0 null$0 Alloc$0)) :named P97))

(assert (! (not (in$0 lst$0 FP_2$0)) :named P98))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0)))))) :named P99))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_1$0 n2_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_1$0 n2_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_1$0 n2_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_1$0 n2_2$0 null$0)))))) :named P100))

(assert (! (forall ((?x Loc)) (Btwn$0 next_1$0 ?x ?x ?x)) :named P101))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P102))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_1$0 ?x ?y ?x)) (= ?x ?y))) :named P103))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P104))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?y)) (not (Btwn$0 next_1$0 ?x ?z ?z))
            (Btwn$0 next_1$0 ?x ?y ?z) (Btwn$0 next_1$0 ?x ?z ?y))) :named P105))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P106))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z))
            (and (Btwn$0 next_1$0 ?x ?y ?y) (Btwn$0 next_1$0 ?y ?z ?z)))) :named P107))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P108))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?y)) (not (Btwn$0 next_1$0 ?y ?z ?z))
            (Btwn$0 next_1$0 ?x ?z ?z))) :named P109))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P110))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z)) (not (Btwn$0 next_1$0 ?y ?u ?z))
            (and (Btwn$0 next_1$0 ?x ?y ?u) (Btwn$0 next_1$0 ?x ?u ?z)))) :named P111))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P112))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z)) (not (Btwn$0 next_1$0 ?x ?u ?y))
            (and (Btwn$0 next_1$0 ?x ?u ?z) (Btwn$0 next_1$0 ?u ?y ?z)))) :named P113))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P114))

(check-sat)

(get-interpolants (and P52 P102 P93 P51 P110 P30 P67 P42 P65 P14 P78 P91 P46 P61 P92 P80 P23 P64 P108 P28 P13 P107 P17 P39 P98 P66 P38 P77 P33 P27 P40 P11 P85 P44 P1 P2 P9 P68 P58 P29 P24 P34 P56 P95 P71 P112 P81 P10 P89 P16 P75 P105 P55 P12 P63 P36 P114 P4) (and P15 P73 P21 P53 P94 P62 P50 P70 P60 P103 P74 P97 P19 P22 P88 P76 P83 P26 P86 P49 P113 P45 P100 P48 P79 P111 P99 P7 P82 P54 P59 P104 P20 P18 P101 P35 P5 P25 P90 P109 P106 P96 P0 P84 P69 P87 P37 P47 P32 P72 P3 P41 P43 P57 P31 P6 P8))

(exit)