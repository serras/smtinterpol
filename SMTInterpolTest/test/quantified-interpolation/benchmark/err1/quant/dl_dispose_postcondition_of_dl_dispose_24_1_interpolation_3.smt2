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
  tests/spl/dl/dl_dispose.spl:24:1-2:A postcondition of procedure dl_dispose might not hold at this return point
  tests/spl/dl/dl_dispose.spl:13:12-15:Related location: This is the postcondition that might not hold
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
(declare-fun Alloc_1$0 () SetLoc)
(declare-fun Axiom_2$0 () Bool)
(declare-fun Axiom_3$0 () Bool)
(declare-fun Axiom_4$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun FP_Caller_final_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun a_1$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun b_1$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun prv_3$0 () Loc)
(declare-fun sk_?X_2$0 () SetLoc)
(declare-fun sk_?X_3$0 () SetLoc)
(declare-fun sk_?X_4$0 () SetLoc)
(declare-fun sk_?e$0 () Loc)

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 b_1$0 ?y ?y)) (= b_1$0 ?y)
            (Btwn$0 next$0 b_1$0 (read$0 next$0 b_1$0) ?y))) :named P0))

(assert (! (forall ((?y Loc))
        (or (not (Btwn$0 next$0 a_1$0 ?y ?y)) (= a_1$0 ?y)
            (Btwn$0 next$0 a_1$0 (read$0 next$0 a_1$0) ?y))) :named P1))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 b_1$0) b_1$0))
            (not (Btwn$0 next$0 b_1$0 ?y ?y)) (= b_1$0 ?y))) :named P2))

(assert (! (forall ((?y Loc))
        (or (not (= (read$0 next$0 a_1$0) a_1$0))
            (not (Btwn$0 next$0 a_1$0 ?y ?y)) (= a_1$0 ?y))) :named P3))

(assert (! (Btwn$0 next$0 b_1$0 (read$0 next$0 b_1$0) (read$0 next$0 b_1$0)) :named P4))

(assert (! (Btwn$0 next$0 a_1$0 (read$0 next$0 a_1$0) (read$0 next$0 a_1$0)) :named P5))

(assert (! (or (in$0 (ep$0 next$0 FP$0 a$0) FP$0) (= a$0 (ep$0 next$0 FP$0 a$0))) :named P6))

(assert (! (or (in$0 (ep$0 next$0 FP$0 a_1$0) FP$0) (= a_1$0 (ep$0 next$0 FP$0 a_1$0))) :named P7))

(assert (! (or (in$0 (ep$0 next$0 FP$0 b_1$0) FP$0) (= b_1$0 (ep$0 next$0 FP$0 b_1$0))) :named P8))

(assert (! (or (in$0 (ep$0 next$0 FP$0 sk_?e$0) FP$0)
    (= sk_?e$0 (ep$0 next$0 FP$0 sk_?e$0))) :named P9))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 a$0) b_1$0) (not (= (read$0 next$0 b_1$0) a$0))
        (not (in$0 b_1$0 sk_?X_2$0)) (not (in$0 a$0 sk_?X_2$0)))) :named P10))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 a$0) a_1$0) (not (= (read$0 next$0 a_1$0) a$0))
        (not (in$0 a_1$0 sk_?X_2$0)) (not (in$0 a$0 sk_?X_2$0)))) :named P11))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 a_1$0) b_1$0) (not (= (read$0 next$0 b_1$0) a_1$0))
        (not (in$0 b_1$0 sk_?X_2$0)) (not (in$0 a_1$0 sk_?X_2$0)))) :named P12))

(assert (! (or (not Axiom_4$0)
    (or (= (read$0 prev$0 a_1$0) a_1$0) (not (= (read$0 next$0 a_1$0) a_1$0))
        (not (in$0 a_1$0 sk_?X_2$0)) (not (in$0 a_1$0 sk_?X_2$0)))) :named P13))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 a$0) b_1$0) (not (= (read$0 next$0 b_1$0) a$0))
        (not (in$0 b_1$0 sk_?X_4$0)) (not (in$0 a$0 sk_?X_4$0)))) :named P14))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 a$0) a_1$0) (not (= (read$0 next$0 a_1$0) a$0))
        (not (in$0 a_1$0 sk_?X_4$0)) (not (in$0 a$0 sk_?X_4$0)))) :named P15))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 a_1$0) b_1$0) (not (= (read$0 next$0 b_1$0) a_1$0))
        (not (in$0 b_1$0 sk_?X_4$0)) (not (in$0 a_1$0 sk_?X_4$0)))) :named P16))

(assert (! (or (not Axiom_2$0)
    (or (= (read$0 prev$0 a_1$0) a_1$0) (not (= (read$0 next$0 a_1$0) a_1$0))
        (not (in$0 a_1$0 sk_?X_4$0)) (not (in$0 a_1$0 sk_?X_4$0)))) :named P17))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 a$0 (ep$0 next$0 FP$0 a$0) ?y)
            (not (Btwn$0 next$0 a$0 ?y ?y)) (not (in$0 ?y FP$0)))) :named P18))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 a_1$0 (ep$0 next$0 FP$0 a_1$0) ?y)
            (not (Btwn$0 next$0 a_1$0 ?y ?y)) (not (in$0 ?y FP$0)))) :named P19))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 b_1$0 (ep$0 next$0 FP$0 b_1$0) ?y)
            (not (Btwn$0 next$0 b_1$0 ?y ?y)) (not (in$0 ?y FP$0)))) :named P20))

(assert (! (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_?e$0 (ep$0 next$0 FP$0 sk_?e$0) ?y)
            (not (Btwn$0 next$0 sk_?e$0 ?y ?y)) (not (in$0 ?y FP$0)))) :named P21))

(assert (! (Btwn$0 next$0 a$0 (ep$0 next$0 FP$0 a$0) (ep$0 next$0 FP$0 a$0)) :named P22))

(assert (! (Btwn$0 next$0 a_1$0 (ep$0 next$0 FP$0 a_1$0) (ep$0 next$0 FP$0 a_1$0)) :named P23))

(assert (! (Btwn$0 next$0 b_1$0 (ep$0 next$0 FP$0 b_1$0) (ep$0 next$0 FP$0 b_1$0)) :named P24))

(assert (! (Btwn$0 next$0 sk_?e$0 (ep$0 next$0 FP$0 sk_?e$0) (ep$0 next$0 FP$0 sk_?e$0)) :named P25))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 a$0) b_1$0) (not (= (read$0 next$0 b_1$0) a$0))
        (not (in$0 b_1$0 sk_?X_3$0)) (not (in$0 a$0 sk_?X_3$0)))) :named P26))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 a$0) a_1$0) (not (= (read$0 next$0 a_1$0) a$0))
        (not (in$0 a_1$0 sk_?X_3$0)) (not (in$0 a$0 sk_?X_3$0)))) :named P27))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 a_1$0) b_1$0) (not (= (read$0 next$0 b_1$0) a_1$0))
        (not (in$0 b_1$0 sk_?X_3$0)) (not (in$0 a_1$0 sk_?X_3$0)))) :named P28))

(assert (! (or (not Axiom_3$0)
    (or (= (read$0 prev$0 a_1$0) a_1$0) (not (= (read$0 next$0 a_1$0) a_1$0))
        (not (in$0 a_1$0 sk_?X_3$0)) (not (in$0 a_1$0 sk_?X_3$0)))) :named P29))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))) :named P30))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc_1$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc_1$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc_1$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc_1$0)))))) :named P31))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP$0))
                 (or (in$0 x FP$0) (in$0 x FP$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP$0 FP$0)))))) :named P32))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_2$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_2$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_2$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_2$0)))))) :named P33))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))) :named P34))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_1$0 FP_2$0))
                 (or (in$0 x FP_Caller_1$0) (in$0 x FP_2$0)))
            (and (not (in$0 x FP_Caller_1$0)) (not (in$0 x FP_2$0))
                 (not (in$0 x (union$0 FP_Caller_1$0 FP_2$0)))))) :named P35))

(assert (! (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc_1$0 FP$0)
                     (setminus$0 Alloc_1$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc_1$0 FP$0))
                     (in$0 x (setminus$0 Alloc_1$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc_1$0 FP$0)))
                 (not (in$0 x (setminus$0 Alloc_1$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc_1$0 FP$0)
                          (setminus$0 Alloc_1$0 Alloc$0))))))) :named P36))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc_1$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 Alloc_1$0 FP$0)))
            (and (or (not (in$0 x Alloc_1$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 Alloc_1$0 FP$0)))))) :named P37))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x Alloc_1$0) (in$0 x (setminus$0 Alloc_1$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc_1$0)))
                 (not (in$0 x (setminus$0 Alloc_1$0 Alloc$0)))))) :named P38))

(assert (! (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 FP$0)))))) :named P39))

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

(assert (! (= (read$0 prev$0 null$0) null$0) :named P43))

(assert (! (forall ((x Loc)) (not (in$0 x emptyset$0))) :named P44))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X_4$0)))
         Axiom_2$0)
    (not (dlseg_struct$0 sk_?X_4$0 next$0 prev$0 a$0 null$0 null$0 b$0))) :named P45))

(assert (! (or
    (and (Btwn$0 next$0 a_1$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b_1$0) null$0)
                  (= (read$0 prev$0 a_1$0) prv_3$0) (in$0 b_1$0 sk_?X_2$0))
             (and (= a_1$0 null$0) (= prv_3$0 b_1$0)))
         Axiom_4$0)
    (not (dlseg_struct$0 sk_?X_2$0 next$0 prev$0 a_1$0 prv_3$0 null$0 b_1$0))) :named P46))

(assert (! (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)) :named P47))

(assert (! (= a_1$0 null$0) :named P48))

(assert (! (= prv_2$0 null$0) :named P49))

(assert (! (Frame$0 FP_1$0 Alloc$0 prev$0 prev$0) :named P50))

(assert (! (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)) :named P51))

(assert (! (= sk_?X_2$0 (dlseg_domain$0 next$0 prev$0 a_1$0 prv_3$0 null$0 b_1$0)) :named P52))

(assert (! (= sk_?X_3$0 FP_1$0) :named P53))

(assert (! (= FP$0 (union$0 FP_1$0 FP$0)) :named P54))

(assert (! (= sk_?X_4$0 FP$0) :named P55))

(assert (! (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)) :named P56))

(assert (! (in$0 sk_?e$0
  (union$0 (intersection$0 Alloc_1$0 FP$0) (setminus$0 Alloc_1$0 Alloc$0))) :named P57))

(assert (! (not (in$0 null$0 Alloc_1$0)) :named P58))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 prv_2$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 prv_2$0 null$0 b$0)))))) :named P59))

(assert (! (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) prv_2$0) (in$0 b$0 sk_?X_3$0))
             (and (= a$0 null$0) (= prv_2$0 b$0)))
         Axiom_3$0)
    (not (dlseg_struct$0 sk_?X_3$0 next$0 prev$0 a$0 prv_2$0 null$0 b$0))) :named P60))

(assert (! (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc_1$0 FP_1$0)
      (setminus$0 Alloc_1$0 Alloc$0)))) :named P61))

(assert (! (= FP_Caller_final_1$0 (union$0 FP_Caller_1$0 FP_2$0)) :named P62))

(assert (! (= b_1$0 b$0) :named P63))

(assert (! (Frame$0 FP_1$0 Alloc$0 next$0 next$0) :named P64))

(assert (! (= Alloc_1$0 (union$0 FP_2$0 Alloc_1$0)) :named P65))

(assert (! (= sk_?X_2$0
  (union$0 (intersection$0 Alloc_1$0 FP_1$0) (setminus$0 Alloc_1$0 Alloc$0))) :named P66))

(assert (! (dlseg_struct$0 sk_?X_2$0 next$0 prev$0 a_1$0 prv_3$0 null$0 b_1$0) :named P67))

(assert (! (= sk_?X_3$0 (dlseg_domain$0 next$0 prev$0 a$0 prv_2$0 null$0 b$0)) :named P68))

(assert (! (dlseg_struct$0 sk_?X_3$0 next$0 prev$0 a$0 prv_2$0 null$0 b$0) :named P69))

(assert (! (= sk_?X_4$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)) :named P70))

(assert (! (dlseg_struct$0 sk_?X_4$0 next$0 prev$0 a$0 null$0 null$0 b$0) :named P71))

(assert (! (not (in$0 null$0 Alloc$0)) :named P72))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))) :named P73))

(assert (! (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_1$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a_1$0 prv_3$0 null$0 b_1$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a_1$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a_1$0 prv_3$0 null$0
                          b_1$0)))))) :named P74))

(assert (! (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)) :named P75))

(assert (! (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))) :named P76))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))) :named P77))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))) :named P78))

(assert (! (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))) :named P79))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))) :named P80))

(assert (! (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))) :named P81))

(check-sat)

(get-interpolants (and P18 P71 P34 P38 P21 P28 P62 P30 P44 P6 P54 P77 P47 P76 P29 P36 P25 P17 P31 P13 P78 P20 P59 P65 P24 P14 P0 P46 P1 P73 P57 P58 P7 P8 P49 P19 P45 P56 P55 P40 P33) (and P81 P43 P63 P53 P5 P35 P16 P67 P2 P15 P42 P79 P66 P26 P75 P52 P39 P23 P64 P11 P70 P72 P51 P37 P80 P22 P10 P48 P3 P41 P74 P68 P9 P12 P32 P4 P27 P61 P69 P50 P60))

(exit)