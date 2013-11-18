#lang plai-typed

; DESUGARING is the process of converting a surface language to an
; underlying core via a static transformation.  In other words, we're
; not running the program yet, but we are "simplifying" it.  
;
; Be careful of that word "simplifying", however.  In some cases, the
; underlying core may seem more complex than the surface language, but
; it will generally present at least one of the advantages below.

(require "2013W1-lecture3-utils.rkt")
(require (typed-in racket [andmap : (('a -> boolean) (listof 'a) -> boolean)]))

;; We want to add plain old numbers to our concrete syntax.
;; For example, we'd like to be able to write: (+ 3 (? 1 3 4)) and have it evaluate to (? 4 6 7).
;;
;; TODO 1: Let's start with the EBNF:
;
; <expr> ::= <addition>
;          | <multiplication>
;          | <nondetnum>
;          | <number>
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


;; TODO 2: now, we must change the SURFACE AST to support the new syntax (and not the old).
; ArithS AST
;; The "S" is for "Surface", BTW.
(define-type ArithS
  [numS (n : number)]
  [numSetS (ns : (listof number))]
  [plusS (l : ArithS) (r : ArithS)]
  [multS (l : ArithS) (r : ArithS)])

;; TODO 4: change the parser to handle the new syntax (and not the old).
; parse s-expressions into ArithS ASTs
(define (parse [s-exp : s-expression]) : ArithS
  (s-exp-type-case 
   s-exp
   ;;;;; LIST CASE ;;;;;
   (lambda ([selst : (listof s-expression)]) : ArithS
     (if (and (> (length selst) 1)
                  (s-exp-symbol? (first selst))
                  (symbol=? (s-exp->symbol (first selst)) '?))
             (if (andmap s-exp-number? (rest selst))
                 (numSetS (map s-exp->number (rest selst)))
                 (error 'parse (string-append "non-number in ? expression in: "
                                              (to-string selst))))
             (if (and (= (length selst) 3)
                      (s-exp-symbol? (first selst))) 
                 (case (s-exp->symbol (first selst))
                   [(+) (plusS (parse (second selst)) (parse (third selst)))]
                   [(*) (multS (parse (second selst)) (parse (third selst)))]
                   [else (error 'parse (string-append "non-operator in operator position in: " 
                                                      (to-string selst)))])
                 (error 'parse (string-append "malformed operator expression in: " (to-string selst))))))

   ;;;;; NUMBER CASE ;;;;;
   (lambda ([senum : number]) : ArithS (numS senum))

   ;;;;; SYMBOL CASE ;;;;;
   (lambda ([sesym : symbol]) : ArithS 
     (error 'parse (string-append "unexpected symbol in: " (to-string sesym))))

   ;;;;; STRING CASE ;;;;;
   (lambda ([sestr : string]) : ArithS 
     (error 'parse (string-append "unexpected string in: " (to-string sestr))))))


;; TODO 3: patch the parser test cases for the new syntax (and not the old).

; Test det number specific cases.
(test (parse '0) (numS 0))
(test (parse '42) (numS 42))
(test (parse '(+ 3 (? 1 3 4))) (plusS (numS 3) (numSetS (list 1 3 4))))

; Test some nondet number specific cases.
(test (parse '(? 1 2)) (numSetS (list 1 2)))
(test (parse '(? 1 2 3)) (numSetS (list 1 2 3)))
(test (parse '(? 2 2)) (numSetS (list 2 2)))

(test/exn (parse '(? (+ (? 1) (? 2)) 2)) "")  ; SHOULD this really be like this?

;(test/exn (parse '1) "")
(test/exn (parse '(?)) "")

; Test the "standard" cases:
(test (parse '(? 1)) (numSetS (list 1)))
(test (parse '(+ (? 1) (? 2))) (plusS (numSetS (list 1)) (numSetS (list 2))))
(test (parse '(* (? 1) (? 2))) (multS (numSetS (list 1)) (numSetS (list 2))))

; Test one "complex" case, just to be safe.
(test (parse '(+ (* (? 1 2) (? 3 4)) (+ (? 5 6) (? 7 8)))) 
      (plusS (multS (numSetS (list 1 2)) (numSetS (list 3 4)))
             (plusS (numSetS (list 5 6)) (numSetS (list 7 8)))))

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


;; TODO 5: Decide if we need to change the CORE AST.

; ArithC AST
;; The "C" is for "Core", BTW.
(define-type ArithC
  ;; In response to a Q after class: how would we change this to allow expressions
  ;; inside (? ...)?
  ;;
  ;; We'd change numSetC to [numSetC (n : (listof ArithC))].  Now, all our cases
  ;; are recursive (require calls to the interpreter on ArithC expressions).  
  ;; Technically, we CAN "bottom out" in our recursion if we hit an empty numSetC,
  ;; but that's not going to work well.  Instead, we need another variant to 
  ;; represent plain only numbers: [numC (n : number)].  
  ;;
  ;; With that, we're all set, and our interpreter will have a case like:
  ;;   [numSetC (ns) (normalize-set (flatten (map interp ns)))]
  [numSetC (n : (listof number))]
  [plusC (l : ArithC) (r : ArithC)]
  [multC (l : ArithC) (r : ArithC)])

;; TODO 7: implement the desugarer

; desugars the surface syntax to the core
(define (desugar [sast : ArithS]) : ArithC
  (type-case ArithS sast
    [numS (n) (numSetC (list n))]
    [numSetS (ns) (numSetC ns)]
    [plusS (l r) (plusC (desugar l) (desugar r))]
    [multS (l r) (multC (desugar l)  (desugar r))]))

;; TODO 6: Write test cases for our desugarer.
(test (desugar (parse '0)) (numSetC (list 0)))
(test (desugar (parse '2)) (numSetC (list 2)))
(test (desugar (parse '(+ 3 (? 1 3 4)))) (plusC (numSetC (list 3)) 
                                                (numSetC (list 1 3 4))))


;; TODO 8: figure out how to change the interpreter

;; Values are now normalized sets of numbers.

; interpret (evaluate) the given well-formed arithmetic expression AST
(define (interp [ast : ArithC]) : (listof number)
  (type-case ArithC ast
    [numSetC (ns) (normalize-set ns)]
    [plusC (l r) ((map2-non-deterministic +) (interp l) (interp r))]
    [multC (l r) ((map2-non-deterministic *) (interp l) (interp r))]))

; run the program (through the parser and then the interpreter).
; contract: s-expression -> (norm'dsetof number)
(define (run [program : s-expression]) : (listof number)
  (interp (desugar (parse program))))

;; Writing the test cases, we might as well start with our passing parse tests.
;; You can either use parse or just borrow the RHS of the parse tests, which
;; are already ASTs.

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

;; TODO the LAST: If we have time, let's do something else:
;;
;; - something we feel like doing, or
;; - allow numeric ranges, like this (-- 3 7), or
;; - change our UNDERLYING IMPLEMENTATION to allow arbitrary expressions in a numSetC 
;;   (at which point numC becomes the only non-recursive type)
;;
;; On that last one, what will we need to change?  The parser?  The desugarer?  
;; The interpreter?  How can we tell?  What forms the INTERFACE between these pieces
;; and buffers them from each other?  
;;
;; Having these kinds of interfaces that decouple parts of our language's program
;; transformation "pipeline" makes it MUCH easier for us to change how various parts
;; work!
