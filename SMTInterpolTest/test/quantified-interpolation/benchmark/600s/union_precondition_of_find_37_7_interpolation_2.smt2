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
  tests/spl/union_find.spl:37:7-22:A precondition for this call of find might not hold
  tests/spl/union_find.spl:12:11-58:Related location: This is the precondition that might not hold
  |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_3$0 () SetLoc)
(declare-fun X_1$0 () SetLoc)
(declare-fun Y$0 () SetLoc)
(declare-fun lseg_set_X$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_struct$0 (SetLoc FldLoc Loc Loc SetLoc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun root_x_1$0 () Loc)
(declare-fun root_y$0 () Loc)
(declare-fun sk_?X_48$0 () SetLoc)
(declare-fun sk_?X_49$0 () SetLoc)
(declare-fun sk_?X_50$0 () SetLoc)
(declare-fun sk_?X_51$0 () SetLoc)
(declare-fun sk_?X_52$0 () SetLoc)
(declare-fun sk_?X_53$0 () SetLoc)
(declare-fun sk_?X_54$0 () SetLoc)
(declare-fun sk_?X_55$0 () SetLoc)
(declare-fun sk_?X_56$0 () SetLoc)
(declare-fun sk_?X_57$0 () SetLoc)
(declare-fun sk_?X_58$0 () SetLoc)
(declare-fun sk_?X_59$0 () SetLoc)
(declare-fun sk_?X_60$0 () SetLoc)
(declare-fun sk_?e_3$0 () Loc)
(declare-fun sk_FP_1$0 () SetLoc)
(declare-fun sk_X_1$0 () SetLoc)
(declare-fun x_1$0 () Loc)
(declare-fun y$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 root_y$0 ?y ?y)) (= root_y$0 ?y)
            (Btwn$0 next$0 root_y$0 (read$0 next$0 root_y$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 root_x_1$0 ?y ?y)) (= root_x_1$0 ?y)
            (Btwn$0 next$0 root_x_1$0 (read$0 next$0 root_x_1$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 root_y$0) root_y$0))
            (not (Btwn$0 next$0 root_y$0 ?y ?y)) (= root_y$0 ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 root_x_1$0) root_x_1$0))
            (not (Btwn$0 next$0 root_x_1$0 ?y ?y)) (= root_x_1$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P5))

(assert (! (Btwn$0 next$0 root_y$0 (read$0 next$0 root_y$0) (read$0 next$0 root_y$0)) :named P6))

(assert (! (Btwn$0 next$0 root_x_1$0 (read$0 next$0 root_x_1$0)
  (read$0 next$0 root_x_1$0)) :named P7))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P8))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P9))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_54$0 sk_?X_49$0))
                 (or (in$0 x sk_?X_54$0) (in$0 x sk_?X_49$0)))
            (and (not (in$0 x sk_?X_54$0)) (not (in$0 x sk_?X_49$0))
                 (not (in$0 x (union$0 sk_?X_54$0 sk_?X_49$0)))))) :named P10))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P11))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_52$0 sk_?X_50$0))
                 (or (in$0 x sk_?X_52$0) (in$0 x sk_?X_50$0)))
            (and (not (in$0 x sk_?X_52$0)) (not (in$0 x sk_?X_50$0))
                 (not (in$0 x (union$0 sk_?X_52$0 sk_?X_50$0)))))) :named P12))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_60$0 sk_?X_55$0))
                 (or (in$0 x sk_?X_60$0) (in$0 x sk_?X_55$0)))
            (and (not (in$0 x sk_?X_60$0)) (not (in$0 x sk_?X_55$0))
                 (not (in$0 x (union$0 sk_?X_60$0 sk_?X_55$0)))))) :named P13))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_60$0 sk_?X_52$0))
                 (or (in$0 x sk_?X_60$0) (in$0 x sk_?X_52$0)))
            (and (not (in$0 x sk_?X_60$0)) (not (in$0 x sk_?X_52$0))
                 (not (in$0 x (union$0 sk_?X_60$0 sk_?X_52$0)))))) :named P14))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_54$0) (in$0 x sk_?X_49$0)
                 (in$0 x (intersection$0 sk_?X_54$0 sk_?X_49$0)))
            (and (or (not (in$0 x sk_?X_54$0)) (not (in$0 x sk_?X_49$0)))
                 (not (in$0 x (intersection$0 sk_?X_54$0 sk_?X_49$0)))))) :named P15))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_60$0) (in$0 x sk_?X_52$0)
                 (in$0 x (intersection$0 sk_?X_60$0 sk_?X_52$0)))
            (and (or (not (in$0 x sk_?X_60$0)) (not (in$0 x sk_?X_52$0)))
                 (not (in$0 x (intersection$0 sk_?X_60$0 sk_?X_52$0)))))) :named P16))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))) :named P17))

(assert (! (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))) :named P18))

(assert (! (= (read$0 next$0 null$0) null$0) :named P19))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P20))

(assert (! (or (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0)
    (not (lseg_set_struct$0 sk_?X_56$0 next$0 x_1$0 root_x_1$0 X_1$0))) :named P21))

(assert (! (or (Btwn$0 next$0 y$0 root_y$0 root_y$0)
    (not (lseg_set_struct$0 sk_?X_55$0 next$0 y$0 root_y$0 Y$0))) :named P22))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P23))

(assert (! (= (read$0 next$0 root_y$0) null$0) :named P24))

(assert (! (= emptyset$0 (intersection$0 sk_?X_54$0 sk_?X_49$0)) :named P25))

(assert (! (= Y$0 (lseg_set_X$0 next$0 y$0 root_y$0)) :named P26))

(assert (! (= sk_?X_48$0 FP$0) :named P27))

(assert (! (= sk_?X_50$0 sk_?X_51$0) :named P28))

(assert (! (= sk_?X_52$0 sk_?X_53$0) :named P29))

(assert (! (= sk_?X_54$0 (union$0 sk_?X_56$0 sk_?X_55$0)) :named P30))

(assert (! (= sk_?X_56$0 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)) :named P31))

(assert (! (lseg_set_struct$0 sk_?X_55$0 next$0 y$0 root_y$0 Y$0) :named P32))

(assert (! (= sk_?X_57$0 (union$0 sk_?X_60$0 sk_?X_58$0)) :named P33))

(assert (! (= sk_?X_59$0 (setenum$0 root_x_1$0)) :named P34))

(assert (! (= sk_FP_1$0 sk_?X_57$0) :named P35))

(assert (! (or (in$0 sk_?e_3$0 (intersection$0 sk_?X_60$0 sk_?X_58$0))
    (and (in$0 sk_?e_3$0 sk_FP_1$0) (not (in$0 sk_?e_3$0 FP$0)))
    (not (= (read$0 next$0 root_x_1$0) null$0))
    (not (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0))) :named P36))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 x_1$0 l1 root_x_1$0)
                 (in$0 l1 (lseg_set_X$0 next$0 x_1$0 root_x_1$0))
                 (not (= l1 root_x_1$0)))
            (and
                 (or (= l1 root_x_1$0)
                     (not (Btwn$0 next$0 x_1$0 l1 root_x_1$0)))
                 (not (in$0 l1 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)))))) :named P37))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 y$0 l1 root_y$0)
                 (in$0 l1 (lseg_set_X$0 next$0 y$0 root_y$0))
                 (not (= l1 root_y$0)))
            (and (or (= l1 root_y$0) (not (Btwn$0 next$0 y$0 l1 root_y$0)))
                 (not (in$0 l1 (lseg_set_X$0 next$0 y$0 root_y$0)))))) :named P38))

(assert (! (or (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0)
    (not (lseg_set_struct$0 sk_?X_60$0 next$0 x_1$0 root_x_1$0 sk_X_1$0))) :named P39))

(assert (! (= FP_Caller_3$0 (setminus$0 FP_Caller$0 FP$0)) :named P40))

(assert (! (= (read$0 next$0 root_x_1$0) null$0) :named P41))

(assert (! (= emptyset$0 emptyset$0) :named P42))

(assert (! (= X_1$0 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)) :named P43))

(assert (! (= sk_?X_48$0 (union$0 sk_?X_54$0 sk_?X_49$0)) :named P44))

(assert (! (= sk_?X_49$0 (union$0 sk_?X_52$0 sk_?X_50$0)) :named P45))

(assert (! (= sk_?X_51$0 (setenum$0 root_y$0)) :named P46))

(assert (! (= sk_?X_53$0 (setenum$0 root_x_1$0)) :named P47))

(assert (! (= sk_?X_55$0 (lseg_set_domain$0 next$0 y$0 root_y$0)) :named P48))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P49))

(assert (! (lseg_set_struct$0 sk_?X_56$0 next$0 x_1$0 root_x_1$0 X_1$0) :named P50))

(assert (! (= sk_?X_58$0 sk_?X_59$0) :named P51))

(assert (! (= sk_?X_60$0 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)) :named P52))

(assert (! (= sk_X_1$0 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)) :named P53))

(assert (! (not (in$0 null$0 Alloc$0)) :named P54))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 x_1$0 l1 root_x_1$0)
                 (in$0 l1 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0))
                 (not (= l1 root_x_1$0)))
            (and
                 (or (= l1 root_x_1$0)
                     (not (Btwn$0 next$0 x_1$0 l1 root_x_1$0)))
                 (not (in$0 l1 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)))))) :named P55))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 y$0 l1 root_y$0)
                 (in$0 l1 (lseg_set_domain$0 next$0 y$0 root_y$0))
                 (not (= l1 root_y$0)))
            (and (or (= l1 root_y$0) (not (Btwn$0 next$0 y$0 l1 root_y$0)))
                 (not (in$0 l1 (lseg_set_domain$0 next$0 y$0 root_y$0)))))) :named P56))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P57))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P58))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P59))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P60))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P61))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P62))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P63))

(check-sat)

(get-interpolants (and P27 P58 P4 P50 P13 P38 P17 P8 P2 P25 P32 P61 P7 P16 P45 P28 P43 P49 P41 P57 P47 P52 P18 P20 P35 P42 P1 P9 P56 P44 P46 P30) (and P24 P10 P59 P62 P39 P23 P29 P40 P54 P55 P5 P33 P6 P19 P26 P34 P0 P22 P60 P48 P14 P21 P37 P36 P11 P63 P15 P53 P3 P51 P31 P12))

(exit)