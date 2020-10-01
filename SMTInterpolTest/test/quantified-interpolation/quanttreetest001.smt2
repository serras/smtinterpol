(set-option :print-success false)
;(set-option :produce-proofs true)
(set-option :interpolant-check-mode true)
(set-option :produce-interpolants true)
(set-info :source "{
Desired Interpolant:
}")
(set-option :print-terms-cse false)
(set-option :verbosity 5)
(set-logic UFLIA)
(set-info :smt-lib-version 2.0)
(set-info :status unsat)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun e () Int)
(declare-fun s () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)

(assert (! (forall ((x Int)) (= (f (g x)) a)) :named P0))
(assert (! (= (g b) c) :named P1))
(assert (! (distinct (f s) a) :named P2))
(assert (! (= e s) :named P3))
(assert (! (= d e) :named P4))
(assert (! (= c d) :named P5))
(assert (! true :named P6))

(check-sat)
(get-proof)
(get-interpolants P0 (P1) P2 (P3 (P4) P5) P6)
(get-interpolants P1 (P2) P3 (P4 (P5) P0) P6)
(get-interpolants P2 (P3) P4 (P5 (P0) P1) P6)
(get-interpolants P3 (P4) P5 (P0 (P1) P2) P6)
(exit)
