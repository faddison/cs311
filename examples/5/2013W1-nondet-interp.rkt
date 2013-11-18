#lang plai-typed

(require "2013W1-lecture3-utils.rkt")
(require (typed-in racket [andmap : (('a -> boolean) (listof 'a) -> boolean)]))

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
  [numSetC (nums : (listof number))]
  [plusC (l : ArithC) (r : ArithC)]
  [multC (l : ArithC) (r : ArithC)])

;; TODO 3: change the parser to handle the new syntax (and not the old).
; parse s-expressions into ArithC ASTs
(define (parse [s-exp : s-expression]) : ArithC
  (s-exp-type-case 
   s-exp
   ;;;;; LIST CASE ;;;;;
   (lambda ([selst : (listof s-expression)]) : ArithC 
     (if (and (> (length selst) 1)
                  (s-exp-symbol? (first selst))
                  (symbol=? (s-exp->symbol (first selst)) '?))
             (if (andmap s-exp-number? (rest selst))
                 (numSetC (map s-exp->number (rest selst)))
                 (error 'parse (string-append "non-number in ? expression in: "
                                              (to-string selst))))
             (if (and (= (length selst) 3)
                      (s-exp-symbol? (first selst))) 
                 (case (s-exp->symbol (first selst))
                   [(+) (plusC (parse (second selst)) (parse (third selst)))]
                   [(*) (multC (parse (second selst)) (parse (third selst)))]
                   [else (error 'parse (string-append "non-operator in operator position in: " 
                                                      (to-string selst)))])
                 (error 'parse (string-append "malformed operator expression in: " (to-string selst))))))

   ;;;;; NUMBER CASE ;;;;;
   (lambda ([senum : number]) : ArithC (error 'parse "numbers no longer allowed!")) ; TODO!!

   ;;;;; SYMBOL CASE ;;;;;
   (lambda ([sesym : symbol]) : ArithC 
     (error 'parse (string-append "unexpected symbol in: " (to-string sesym))))

   ;;;;; STRING CASE ;;;;;
   (lambda ([sestr : string]) : ArithC 
     (error 'parse (string-append "unexpected string in: " (to-string sestr))))))


;; TODO 2: patch the parser test cases for the new syntax (and not the old).

; Test some nondet number specific cases.
(test (parse '(? 1 2)) (numSetC (list 1 2)))
(test (parse '(? 1 2 3)) (numSetC (list 1 2 3)))
(test (parse '(? 2 2)) (numSetC (list 2 2)))

(test/exn (parse '(? (+ (? 1) (? 2)) 2)) "")  ; SHOULD this really be like this?

(test/exn (parse '1) "")
(test/exn (parse '(?)) "")

; Test the "standard" cases:
(test (parse '(? 1)) (numSetC (list 1)))
(test (parse '(+ (? 1) (? 2))) (plusC (numSetC (list 1)) (numSetC (list 2))))
(test (parse '(* (? 1) (? 2))) (multC (numSetC (list 1)) (numSetC (list 2))))

; Test one "complex" case, just to be safe.
(test (parse '(+ (* (? 1 2) (? 3 4)) (+ (? 5 6) (? 7 8)))) 
      (plusC (multC (numSetC (list 1 2)) (numSetC (list 3 4)))
             (plusC (numSetC (list 5 6)) (numSetC (list 7 8)))))

; Test various erroneous programs:
(test/exn (parse '((? 1) (? 2) (? 3))) "")
(test/exn (parse '()) "")
(test/exn (parse '(+)) "")
(test/exn (parse '(+ (? 1))) "")
(test/exn (parse '(+ (? 1) (? 2) (? 3))) "")
(test/exn (parse '(*)) "")
(test/exn (parse '(* (? 1))) "")
(test/exn (parse '(* (? 1) (? 2) (? 3))) "")
(test/exn (parse '(- (? 1) (? 2))) "")
(test/exn (parse '(- (? 1) (? 2))) "")

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
; contract: ArithC -> (normalized-set-of number)
(define (interp [ast : ArithC]) : (listof number)
  (type-case ArithC ast
    [numSetC (ns) (normalize-set ns)]
    [plusC (l r) ((map2-non-deterministic +) (interp l) (interp r))]
    [multC (l r) ((map2-non-deterministic *) (interp l) (interp r))]))


;; Writing the test cases, we might as well start with our passing parse tests.
;; You can either use parse or just borrow the RHS of the parse tests, which
;; are already ASTs.

; run the program (through the parser and then the interpreter).
; contract: s-expression -> (norm'dsetof number)
(define (run [program : s-expression]) : (listof number)
  (interp (parse program)))

;; Writing the test cases, we might as well start with our passing parse tests.
;; You can either use parse or just borrow the RHS of the parse tests, which
;; are already ASTs.

;; TODO 5: patch the interp test cases.

(test (run '(? 1 2)) (list 1 2))
(test (run '(? 1 2 3)) (list 1 2 3))
(test (run '(? 2 2)) (list 2))


; Test the "standard" cases:
(test (run '(? 1)) (list 1))
(test (run '(+ (? 1) (? 2))) (list 3))
(test (run '(* (? 1) (? 2))) (list 2))

; Test a bit of nondeterminism in a simple way.
(test (run '(+ (? 2 1) (? 3 4))) (list 4 5 6))
(test (run '(* (? 2 1) (? 2 4))) (list 2 4 8))


; Test one "complex" case, just to be safe.
(test (run '(+ (* (? 1 2) (? 3 4)) (+ (? 5 6) (? 7 8)))) 
      (list 15 16 17 18 19 20 21 22))
