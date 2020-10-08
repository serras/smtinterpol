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
  tests/spl/sl/rec_copy.spl:44:4-19:Possible heap access through null or dangling reference
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
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_2$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_3$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun cp$0 () Loc)
(declare-fun cp_1$0 () Loc)
(declare-fun curr$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_2$0 () FldLoc)
(declare-fun old_cp_2$0 () Loc)
(declare-fun sk_?X_39$0 () SetLoc)
(declare-fun sk_?X_40$0 () SetLoc)
(declare-fun sk_?X_41$0 () SetLoc)
(declare-fun tmp_1$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 tmp_1$0 ?y ?y)) (= tmp_1$0 ?y)
            (Btwn$0 next$0 tmp_1$0 (read$0 next$0 tmp_1$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 tmp_1$0) tmp_1$0))
            (not (Btwn$0 next$0 tmp_1$0 ?y ?y)) (= tmp_1$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P4))

(assert (! (Btwn$0 next$0 tmp_1$0 (read$0 next$0 tmp_1$0) (read$0 next$0 tmp_1$0)) :named P5))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P6))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 Alloc$0 (setenum$0 tmp_1$0)))
                 (or (in$0 x Alloc$0) (in$0 x (setenum$0 tmp_1$0))))
            (and (not (in$0 x Alloc$0)) (not (in$0 x (setenum$0 tmp_1$0)))
                 (not (in$0 x (union$0 Alloc$0 (setenum$0 tmp_1$0))))))) :named P7))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_41$0 sk_?X_40$0))
                 (or (in$0 x sk_?X_41$0) (in$0 x sk_?X_40$0)))
            (and (not (in$0 x sk_?X_41$0)) (not (in$0 x sk_?X_40$0))
                 (not (in$0 x (union$0 sk_?X_41$0 sk_?X_40$0)))))) :named P8))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 (setenum$0 tmp_1$0)))
                 (or (in$0 x FP$0) (in$0 x (setenum$0 tmp_1$0))))
            (and (not (in$0 x FP$0)) (not (in$0 x (setenum$0 tmp_1$0)))
                 (not (in$0 x (union$0 FP$0 (setenum$0 tmp_1$0))))))) :named P9))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P10))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_41$0) (in$0 x sk_?X_40$0)
                 (in$0 x (intersection$0 sk_?X_41$0 sk_?X_40$0)))
            (and (or (not (in$0 x sk_?X_41$0)) (not (in$0 x sk_?X_40$0)))
                 (not (in$0 x (intersection$0 sk_?X_41$0 sk_?X_40$0)))))) :named P11))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P12))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P13))

(assert (! (= (read$0 (write$0 next$0 tmp_1$0 old_cp_2$0) tmp_1$0) old_cp_2$0) :named P14))

(assert (! (or (= null$0 tmp_1$0)
    (= (read$0 next$0 null$0)
      (read$0 (write$0 next$0 tmp_1$0 old_cp_2$0) null$0))) :named P15))

(assert (! (or (= tmp_1$0 tmp_1$0)
    (= (read$0 next$0 tmp_1$0)
      (read$0 (write$0 next$0 tmp_1$0 old_cp_2$0) tmp_1$0))) :named P16))

(assert (! (= (read$0 next$0 null$0) null$0) :named P17))

(assert (! (= (read$0 next_2$0 null$0) null$0) :named P18))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P19))

(assert (! (or (Btwn$0 next$0 curr$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_40$0 next$0 curr$0 null$0))) :named P20))

(assert (! (= FP_3$0 (union$0 FP$0 (setenum$0 tmp_1$0))) :named P21))

(assert (! (= cp_1$0 tmp_1$0) :named P22))

(assert (! (= old_cp_2$0 cp$0) :named P23))

(assert (! (= emptyset$0 (intersection$0 sk_?X_41$0 sk_?X_40$0)) :named P24))

(assert (! (= sk_?X_39$0 FP$0) :named P25))

(assert (! (= sk_?X_41$0 (lseg_domain$0 next$0 cp$0 null$0)) :named P26))

(assert (! (lseg_struct$0 sk_?X_40$0 next$0 curr$0 null$0) :named P27))

(assert (! (not (= curr$0 null$0)) :named P28))

(assert (! (not (in$0 null$0 Alloc$0)) :named P29))

(assert (! (not (in$0 tmp_1$0 Alloc$0)) :named P30))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr$0 null$0)))))) :named P31))

(assert (! (or (Btwn$0 next$0 cp$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_41$0 next$0 cp$0 null$0))) :named P32))

(assert (! (= Alloc_2$0 (union$0 Alloc$0 (setenum$0 tmp_1$0))) :named P33))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P34))

(assert (! (= next_2$0 (write$0 next$0 cp_1$0 old_cp_2$0)) :named P35))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P36))

(assert (! (= sk_?X_39$0 (union$0 sk_?X_41$0 sk_?X_40$0)) :named P37))

(assert (! (= sk_?X_40$0 (lseg_domain$0 next$0 curr$0 null$0)) :named P38))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P39))

(assert (! (lseg_struct$0 sk_?X_41$0 next$0 cp$0 null$0) :named P40))

(assert (! (not (= tmp_1$0 null$0)) :named P41))

(assert (! (not (in$0 curr$0 FP_3$0)) :named P42))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 cp$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 cp$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 cp$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 cp$0 null$0)))))) :named P43))

(assert (! (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 cp_1$0 old_cp_2$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v cp_1$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z cp_1$0 cp_1$0)))))
                          (and (not (= cp_1$0 ?v))
                               (or (Btwn$0 next$0 ?z cp_1$0 ?v)
                                   (and (Btwn$0 next$0 ?z cp_1$0 cp_1$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u cp_1$0)
                               (or (Btwn$0 next$0 old_cp_2$0 ?v cp_1$0)
                                   (and (Btwn$0 next$0 old_cp_2$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 old_cp_2$0 cp_1$0
                                               cp_1$0)))))
                          (and (not (= cp_1$0 ?v))
                               (or (Btwn$0 next$0 ?z cp_1$0 ?v)
                                   (and (Btwn$0 next$0 ?z cp_1$0 cp_1$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 old_cp_2$0 ?u ?v)
                               (or (Btwn$0 next$0 old_cp_2$0 ?v cp_1$0)
                                   (and (Btwn$0 next$0 old_cp_2$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 old_cp_2$0 cp_1$0
                                               cp_1$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v cp_1$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z cp_1$0 cp_1$0)))))
                 (and (not (= cp_1$0 ?v))
                      (or (Btwn$0 next$0 ?z cp_1$0 ?v)
                          (and (Btwn$0 next$0 ?z cp_1$0 cp_1$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u cp_1$0)
                      (or (Btwn$0 next$0 old_cp_2$0 ?v cp_1$0)
                          (and (Btwn$0 next$0 old_cp_2$0 ?v ?v)
                               (not (Btwn$0 next$0 old_cp_2$0 cp_1$0 cp_1$0)))))
                 (and (not (= cp_1$0 ?v))
                      (or (Btwn$0 next$0 ?z cp_1$0 ?v)
                          (and (Btwn$0 next$0 ?z cp_1$0 cp_1$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 old_cp_2$0 ?u ?v)
                      (or (Btwn$0 next$0 old_cp_2$0 ?v cp_1$0)
                          (and (Btwn$0 next$0 old_cp_2$0 ?v ?v)
                               (not (Btwn$0 next$0 old_cp_2$0 cp_1$0 cp_1$0)))))
                 (not (Btwn$0 (write$0 next$0 cp_1$0 old_cp_2$0) ?z ?u ?v))))) :named P44))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P45))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P46))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P47))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P48))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P49))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P50))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P51))

(check-sat)

(get-interpolants (and P25 P8 P39 P10 P27 P42 P20 P26 P35 P24 P41 P36 P49 P31 P3 P4 P9 P21 P34 P32 P40 P12 P44 P13 P30 P51) (and P48 P17 P33 P2 P28 P29 P46 P38 P5 P15 P47 P43 P0 P22 P23 P16 P19 P1 P7 P14 P6 P50 P18 P45 P37 P11))

(exit)