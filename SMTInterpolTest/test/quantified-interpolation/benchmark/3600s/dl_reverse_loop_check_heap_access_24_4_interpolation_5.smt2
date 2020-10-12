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
  tests/spl/dl/dl_reverse.spl:24:4-22:Possible heap access through null or dangling reference
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
(declare-fun Axiom_13$0 () Bool)
(declare-fun Axiom_14$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun end_2$0 () Loc)
(declare-fun end_init$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_4$0 () Loc)
(declare-fun prv_init$0 () Loc)
(declare-fun sk_?X_12$0 () SetLoc)
(declare-fun sk_?X_13$0 () SetLoc)
(declare-fun sk_?X_14$0 () SetLoc)
(declare-fun start_2$0 () Loc)
(declare-fun start_init$0 () Loc)
(declare-fun tmp_2$0 () Loc)
(declare-fun tmp_4$0 () Loc)
(declare-fun tmp_init$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 end_2$0 ?y ?y)) (= end_2$0 ?y)
            (Btwn$0 next$0 end_2$0 (read$0 next$0 end_2$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 start_init$0 ?y ?y)) (= start_init$0 ?y)
            (Btwn$0 next$0 start_init$0 (read$0 next$0 start_init$0) ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))) :named P3))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 end_2$0) end_2$0))
            (not (Btwn$0 next$0 end_2$0 ?y ?y)) (= end_2$0 ?y))) :named P4))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 start_init$0) start_init$0))
            (not (Btwn$0 next$0 start_init$0 ?y ?y)) (= start_init$0 ?y))) :named P5))

(assert (! (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)) :named P6))

(assert (! (Btwn$0 next$0 end_2$0 (read$0 next$0 end_2$0) (read$0 next$0 end_2$0)) :named P7))

(assert (! (Btwn$0 next$0 start_init$0 (read$0 next$0 start_init$0)
  (read$0 next$0 start_init$0)) :named P8))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_13$0)) (not (in$0 null$0 sk_?X_13$0)))) :named P9))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 null$0) end_2$0)
        (not (= (read$0 next$0 end_2$0) null$0))
        (not (in$0 end_2$0 sk_?X_13$0)) (not (in$0 null$0 sk_?X_13$0)))) :named P10))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 null$0) start_init$0)
        (not (= (read$0 next$0 start_init$0) null$0))
        (not (in$0 start_init$0 sk_?X_13$0)) (not (in$0 null$0 sk_?X_13$0)))) :named P11))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_13$0)) (not (in$0 curr_init$0 sk_?X_13$0)))) :named P12))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 curr_init$0) end_2$0)
        (not (= (read$0 next$0 end_2$0) curr_init$0))
        (not (in$0 end_2$0 sk_?X_13$0)) (not (in$0 curr_init$0 sk_?X_13$0)))) :named P13))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 curr_init$0) start_init$0)
        (not (= (read$0 next$0 start_init$0) curr_init$0))
        (not (in$0 start_init$0 sk_?X_13$0))
        (not (in$0 curr_init$0 sk_?X_13$0)))) :named P14))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 prv_init$0) null$0)
        (not (= (read$0 next$0 null$0) prv_init$0))
        (not (in$0 null$0 sk_?X_13$0)) (not (in$0 prv_init$0 sk_?X_13$0)))) :named P15))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 prv_init$0) end_2$0)
        (not (= (read$0 next$0 end_2$0) prv_init$0))
        (not (in$0 end_2$0 sk_?X_13$0)) (not (in$0 prv_init$0 sk_?X_13$0)))) :named P16))

(assert (! (or (not Axiom_14$0)
    (or (= (read$0 prev$0 prv_init$0) start_init$0)
        (not (= (read$0 next$0 start_init$0) prv_init$0))
        (not (in$0 start_init$0 sk_?X_13$0))
        (not (in$0 prv_init$0 sk_?X_13$0)))) :named P17))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 null$0) null$0)
        (not (= (read$0 next$0 null$0) null$0))
        (not (in$0 null$0 sk_?X_14$0)) (not (in$0 null$0 sk_?X_14$0)))) :named P18))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 null$0) end_2$0)
        (not (= (read$0 next$0 end_2$0) null$0))
        (not (in$0 end_2$0 sk_?X_14$0)) (not (in$0 null$0 sk_?X_14$0)))) :named P19))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 null$0) start_init$0)
        (not (= (read$0 next$0 start_init$0) null$0))
        (not (in$0 start_init$0 sk_?X_14$0)) (not (in$0 null$0 sk_?X_14$0)))) :named P20))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 curr_init$0) null$0)
        (not (= (read$0 next$0 null$0) curr_init$0))
        (not (in$0 null$0 sk_?X_14$0)) (not (in$0 curr_init$0 sk_?X_14$0)))) :named P21))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 curr_init$0) end_2$0)
        (not (= (read$0 next$0 end_2$0) curr_init$0))
        (not (in$0 end_2$0 sk_?X_14$0)) (not (in$0 curr_init$0 sk_?X_14$0)))) :named P22))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 curr_init$0) start_init$0)
        (not (= (read$0 next$0 start_init$0) curr_init$0))
        (not (in$0 start_init$0 sk_?X_14$0))
        (not (in$0 curr_init$0 sk_?X_14$0)))) :named P23))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 prv_init$0) null$0)
        (not (= (read$0 next$0 null$0) prv_init$0))
        (not (in$0 null$0 sk_?X_14$0)) (not (in$0 prv_init$0 sk_?X_14$0)))) :named P24))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 prv_init$0) end_2$0)
        (not (= (read$0 next$0 end_2$0) prv_init$0))
        (not (in$0 end_2$0 sk_?X_14$0)) (not (in$0 prv_init$0 sk_?X_14$0)))) :named P25))

(assert (! (or (not Axiom_13$0)
    (or (= (read$0 prev$0 prv_init$0) start_init$0)
        (not (= (read$0 next$0 start_init$0) prv_init$0))
        (not (in$0 start_init$0 sk_?X_14$0))
        (not (in$0 prv_init$0 sk_?X_14$0)))) :named P26))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P27))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_14$0 sk_?X_13$0))
                 (or (in$0 x sk_?X_14$0) (in$0 x sk_?X_13$0)))
            (and (not (in$0 x sk_?X_14$0)) (not (in$0 x sk_?X_13$0))
                 (not (in$0 x (union$0 sk_?X_14$0 sk_?X_13$0)))))) :named P28))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P29))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_14$0) (in$0 x sk_?X_13$0)
                 (in$0 x (intersection$0 sk_?X_14$0 sk_?X_13$0)))
            (and (or (not (in$0 x sk_?X_14$0)) (not (in$0 x sk_?X_13$0)))
                 (not (in$0 x (intersection$0 sk_?X_14$0 sk_?X_13$0)))))) :named P30))

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

(assert (! (= (read$0 prev$0 null$0) null$0) :named P34))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P35))

(assert (! (or
    (and (Btwn$0 next$0 prv_init$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 start_init$0) null$0)
                  (= (read$0 prev$0 prv_init$0) curr_init$0)
                  (in$0 start_init$0 sk_?X_13$0))
             (and (= curr_init$0 start_init$0) (= prv_init$0 null$0)))
         Axiom_14$0)
    (not
         (dlseg_struct$0 sk_?X_13$0 next$0 prev$0 prv_init$0 curr_init$0
           null$0 start_init$0))) :named P36))

(assert (! (= curr_4$0 curr_init$0) :named P37))

(assert (! (= prv_4$0 prv_init$0) :named P38))

(assert (! (= tmp_2$0 tmp_init$0) :named P39))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P40))

(assert (! (= sk_?X_12$0 (union$0 sk_?X_14$0 sk_?X_13$0)) :named P41))

(assert (! (= sk_?X_13$0
  (dlseg_domain$0 next$0 prev$0 prv_init$0 curr_init$0 null$0 start_init$0)) :named P42))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P43))

(assert (! (dlseg_struct$0 sk_?X_14$0 next$0 prev$0 curr_init$0 prv_init$0 null$0
  end_init$0) :named P44))

(assert (! (not (in$0 null$0 Alloc$0)) :named P45))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0
                     null$0 end_init$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0
                          null$0 end_init$0)))))) :named P46))

(assert (! (or
    (and (Btwn$0 next$0 curr_init$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 end_init$0) null$0)
                  (= (read$0 prev$0 curr_init$0) prv_init$0)
                  (in$0 end_init$0 sk_?X_14$0))
             (and (= curr_init$0 null$0) (= prv_init$0 end_init$0)))
         Axiom_13$0)
    (not
         (dlseg_struct$0 sk_?X_14$0 next$0 prev$0 curr_init$0 prv_init$0
           null$0 end_init$0))) :named P47))

(assert (! (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)) :named P48))

(assert (! (= end_2$0 end_init$0) :named P49))

(assert (! (= start_2$0 start_init$0) :named P50))

(assert (! (= tmp_4$0 curr_4$0) :named P51))

(assert (! (= emptyset$0 (intersection$0 sk_?X_14$0 sk_?X_13$0)) :named P52))

(assert (! (= sk_?X_12$0 FP$0) :named P53))

(assert (! (= sk_?X_14$0
  (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0 null$0 end_init$0)) :named P54))

(assert (! (dlseg_struct$0 sk_?X_13$0 next$0 prev$0 prv_init$0 curr_init$0 null$0
  start_init$0) :named P55))

(assert (! (not (= curr_4$0 null$0)) :named P56))

(assert (! (not (in$0 curr_4$0 FP$0)) :named P57))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 prv_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 prv_init$0 curr_init$0
                     null$0 start_init$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 prv_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 prv_init$0 curr_init$0
                          null$0 start_init$0)))))) :named P58))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P59))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P60))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P61))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P62))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P63))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P64))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P65))

(check-sat)

(get-interpolants (and P10 P65 P61 P7 P53 P48 P1 P22 P43 P37 P28 P14 P49 P44 P36 P33 P47 P6 P46 P25 P27 P24 P13 P30 P62 P17 P63 P16 P3 P57 P31 P23 P12) (and P40 P8 P52 P9 P5 P38 P0 P64 P21 P51 P15 P54 P11 P50 P56 P19 P59 P55 P35 P2 P60 P32 P34 P29 P18 P39 P45 P4 P20 P26 P58 P42 P41))

(exit)