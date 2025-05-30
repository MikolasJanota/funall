(set-info :smt-lib-version 2.6)
(set-logic AUFNIRA)
(set-info :source |
Generated by: Mirek Olšák, Mikoláš Janota, Chad E. Brown
Generated on: 2024-04-14
Application: Mathematics challenges involving function synthesis
From a collection by: Vít Musil
Source url: https://prase.cz/library/FunkcionalniRovniceVM/FunkcionalniRovniceVM.pdf
Original source: c1068820h2391983p19634015
|)
(set-info :license "https://creativecommons.org/licenses/by-nc/4.0/")
(set-info :category "crafted")
(set-info :status sat)

; Header
(declare-fun f (Real) Real)

; Equations
(assert (forall ((x Real) (y Real)) (= (- (* (- x y) (f (+ x y))) (* (+ x y) (f (- x y)))) (* (* (* 4.0 x) y) (- (* x x) (* y y))))))

; Find all possible f

(check-sat)
(exit)
(get-model)
