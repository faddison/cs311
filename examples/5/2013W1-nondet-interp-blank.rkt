#lang plai-typed

(require "2013W1-lecture3-utils.rkt")

;; NEW concrete syntax:
; <expr> ::= <addition>
;          | <multiplication>
;          | <nondetnum>
;
; <addition> ::= (+ <expr> <expr>)
;
; <multiplication> ::= (* <expr> <expr>)
;
; <nondetnum> ::= (? <list-of-numbers>)
;
; <list-of-numbers> ::= <number>
;                     | <number> <list-of-numbers>
;
; <number> ::= a valid Racket number


;; TODO 1: change the AST to support the new syntax (and not the old).
; ArithC AST
;; The "C" is for "Core", BTW.
(define-type ArithC
  [numC (n : number)]
  [plusC (l : ArithC) (r : ArithC)]
  [multC (l : ArithC) (r : ArithC)])

;; TODO 3: change the parser to handle the new syntax (and not the old).
; parse s-expressions into ArithC ASTs
(define (parse [s-exp : s-expression]) : ArithC
  (s-exp-type-case 
   s-exp
   ;;;;; LIST CASE ;;;;;
   (lambda ([selst : (listof s-expression)]) : ArithC 
     (if (and (= (length selst) 3)
              (s-exp-symbol? (first selst))) 
         (case (s-exp->symbol (first selst))
           [(+) (plusC (parse (second selst)) (parse (third selst)))]
           [(*) (multC (parse (second selst)) (parse (third selst)))]
           [else (error 'parse (string-append "non-operator in operator position in: " 
                                              (to-string selst)))])
         (error 'parse (string-append "malformed operator expression in: " (to-string selst)))))

   ;;;;; NUMBER CASE ;;;;;
   (lambda ([senum : number]) : ArithC (numC senum))

   ;;;;; SYMBOL CASE ;;;;;
   (lambda ([sesym : symbol]) : ArithC 
     (error 'parse (string-append "unexpected symbol in: " (to-string sesym))))

   ;;;;; STRING CASE ;;;;;
   (lambda ([sestr : string]) : ArithC 
     (error 'parse (string-append "unexpected string in: " (to-string sestr))))))


;; TODO 2: patch the parser test cases for the new syntax (and not the old).

; Test the "standard" cases:
(test (parse '1) (numC 1))
(test (parse '(+ 1 2)) (plusC (numC 1) (numC 2)))
(test (parse '(* 1 2)) (multC (numC 1) (numC 2)))

; Test one "complex" case, just to be safe.
(test (parse '(+ (* 1 2) (+ 3 4))) (plusC (multC (numC 1) (numC 2))
                                          (plusC (numC 3) (numC 4))))

; Test various erroneous programs:
(test/exn (parse '(1 2 3)) "")
(test/exn (parse '()) "")
(test/exn (parse '(+)) "")
(test/exn (parse '(+ 1)) "")
(test/exn (parse '(+ 1 2 3)) "")
(test/exn (parse '(*)) "")
(test/exn (parse '(* 1)) "")
(test/exn (parse '(* 1 2 3)) "")
(test/exn (parse '(- 1 2)) "")
(test/exn (parse '(- 1 2)) "")

; Test some especially odd inputs that are hard to even construct.
(test/exn (parse (symbol->s-exp '-)) "")
(test/exn (parse '"hello") "")



;; We DO have to decide how values will be represented, however.  As numbers?
;; As numCs?  We'll use numbers as Shriram does.  Should we worry that this
;; means that interp cannot be called on its own results.  Will we be able
;; to do that in the future?  Is that a bad thing?

;; TODO 4: revisit the decision of how values will be represented.

;; TODO 6: patch the interpreter itself!
; interpret (evaluate) the given well-formed arithmetic expression AST
(define (interp [ast : ArithC]) : number
  (type-case ArithC ast
    [numC (n) n]
    [plusC (l r) (+ (interp l) (interp r))]
    [multC (l r) (* (interp l) (interp r))]))


;; Writing the test cases, we might as well start with our passing parse tests.
;; You can either use parse or just borrow the RHS of the parse tests, which
;; are already ASTs.

;; TODO 5: patch the interp test cases.

; Test the "standard" cases:
(test (interp (parse '1)) 1)
(test (interp (parse '(+ 1 2))) (+ 1 2))
(test (interp (parse '(* 1 2))) (* 1 2))

; Test one "complex" case, just to be safe.
(test (interp (parse '(+ (* 1 2) (+ 3 4)))) (+ (* 1 2) (+ 3 4)))
