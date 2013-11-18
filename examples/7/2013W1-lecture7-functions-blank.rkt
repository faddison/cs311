#lang plai-typed

(require "utils.rkt")

;; Using the test module ensures that the tests are run if we run this
;; file but not if we run another that requires this one.  Definitions
;; inside the test module are also not available outside of it (so we
;; can define helper functions there without cluttering the local
;; namespace or exporting to other files that require this one).  The
;; module also visually (and functionally) groups tests.  
;;
;; However, tests inside this module are NOT type-checked, which can
;; lead you to some headscratching before you find type errors in your
;; tests!  Use with caution!
(module+ test
  ;; Only print out the failed test cases.
  (print-only-errors true))

(define-type FunDefC
  [fdC (name : symbol) (arg : symbol) (body : ExprC)])  ; so, we'll need exprCs!


; ExprS ST: arithmetic with predefined functions
(define-type ExprS
  [numS (n : number)]
  [divS (l : ExprS) (r : ExprS)]
  [plusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [appS (f : symbol) (a : ExprS)]
  [idS (i : symbol)])


; ExprC AST: arithmetic with predefined functions
(define-type ExprC
  [numC (n : number)]
  [divC (l : ExprC) (r : ExprC)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [appC (f : symbol) (a : ExprC)]
  [idC (i : symbol)])

; Binary operator symbol map.
(define binop-map (hash (list (values '/ divS)
			      (values '+ plusS)
                              (values '- bminusS)
                              (values '* multS))))

; check if the identifier is disallowed as a variable or function name
(define (reserved? [s : symbol]) : boolean
  (some? (hash-ref binop-map s)))

(module+ test
  (test (reserved? '+) true)
  (test (reserved? '/) true)
  (test (reserved? '-) true)
  (test (reserved? '*) true)
  (test (reserved? '_) false)
  (test (reserved? 'a) false))

; parse s-expressions into ExprS STs
(define (parse [s-exp : s-expression]) : ExprS
  (s-exp-type-case s-exp
                   (lambda ([selst : (listof s-expression)]) : ExprS
                     (cond 
                       [(and (= (length selst) 3)
                             (s-exp-symbol? (first selst)))
                        (type-case (optionof (ExprS ExprS -> ExprS)) (hash-ref binop-map (s-exp->symbol (first selst)))
                          [none () (error 'parse (string-append "non-binary-operator symbol used as binary operator in: " (to-string selst)))]
                          [some (opS) (opS (parse (second selst)) (parse (third selst)))])]
                       [(and (= (length selst) 2)
                             (s-exp-symbol? (first selst))
                             (not (reserved? (s-exp->symbol (first selst)))))
                        (appS (s-exp->symbol (first selst)) (parse (second selst)))]
                       [else
                        (error 'parse (string-append "malformed operator expression in: " (to-string selst)))]))
                   (lambda ([senum : number]) : ExprS (numS senum))
                   (lambda ([sesym : symbol]) : ExprS (if (reserved? sesym)
                                                          (error 'parse (string-append "attempt to use reserved word as identifier in: " (to-string sesym)))
                                                          (idS sesym)))
                   (lambda ([sestr : string]) : ExprS (error 'parse (string-append "unexpected string in: " (to-string sestr))))))


; Test the "standard" cases:
(module+ test
  (test (parse '1) (numS 1))
  (test (parse '(+ 1 2)) (plusS (numS 1) (numS 2)))
  (test (parse '(* 1 2)) (multS (numS 1) (numS 2)))
  (test (parse '(- 1 2)) (bminusS (numS 1) (numS 2)))
  (test (parse '(/ 1 2)) (divS (numS 1) (numS 2)))
  (test (parse '(a 1)) (appS 'a (numS 1)))
  (test (parse (symbol->s-exp 'a)) (idS 'a))
  
  ; Test one "complex" case, just to be safe.
  (test (parse '(+ (* 1 2) (- 3 4))) (plusS (multS (numS 1) (numS 2))
                                            (bminusS (numS 3) (numS 4))))
  
  ; Test various erroneous programs:
  (test/exn (parse '(1 2 3)) "")
  (test/exn (parse '()) "")
  (test/exn (parse '(+)) "")
  (test/exn (parse '(+ 1)) "")
  (test/exn (parse '(+ 1 2 3)) "")
  (test/exn (parse '(*)) "")
  (test/exn (parse '(* 1)) "")
  (test/exn (parse '(* 1 2 3)) "")
  (test/exn (parse '(-)) "")
  (test/exn (parse '(- 1 2 3)) "")
  (test/exn (parse '(^ 1 2)) "")
  (test/exn (parse '(not)) "")
  (test/exn (parse '(not 1 2)) "")
  (test/exn (parse (symbol->s-exp '+)) "")
  
  ; Test some especially odd inputs that are hard to even construct.
  (test/exn (parse (first (s-exp->list '(- 1 2)))) "")
  (test/exn (parse (first (s-exp->list '("hello" 1 2)))) ""))


; desugar the surface abstract syntax tree into our core abstract syntax tree
(define (desugar [st : ExprS]) : ExprC
  (type-case ExprS st
    [numS (n) (numC n)]
    [divS (l r) (divC (desugar l) (desugar r))]
    [plusS (l r) (plusC (desugar l) (desugar r))]
    [multS (l r) (multC (desugar l) (desugar r))]
    [bminusS (l r) (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [appS (f a) (appC f (desugar a))]
    [idS (i) (idC i)]))

(module+ test
  (test (desugar (numS 1)) (numC 1))
  (test (desugar (divS (numS 1) (numS 2))) (divC (numC 1) (numC 2)))
  (test (desugar (plusS (numS 1) (numS 2))) (plusC (numC 1) (numC 2)))
  (test (desugar (multS (numS 1) (numS 2))) (multC (numC 1) (numC 2)))
  (test (desugar (bminusS (numS 1) (numS 2))) (plusC (numC 1) (multC (numC -1) (numC 2))))
  (test (desugar (appS 'f (idS 'x))) (appC 'f (idC 'x)))
  (test (desugar (idS 'x)) (idC 'x))
  
  ; Test one "complex" case, just to be safe.
  (test (desugar (bminusS (multS (numS 1) (numS 2))
                          (plusS (numS 3) (numS 4))))
        (plusC (multC (numC 1) (desugar (numS 2)))
               (multC (numC -1) (plusC (numC 3) (numC 4))))))


;; We have finished parsing and desugaring for functions with
;; arithmetic that includes division.  We've left division in the
;; core.  There's a few more things to do, however!

;; TODO 1: finish substitution for division, id, and app cases.

;; TODO 4: revisit and implement lazy evaluation ("uncached" lazy evaluation, in particular)

;; TODO 5: revisit and add a debug expression?

; substitute the value new AS A numC for the symbol old in expr
(define subst : (number symbol ExprC -> ExprC)
  (lambda (new old expr)
    (local ([define (helper expr)
              (type-case ExprC expr
                [numC (n) expr]
                [divC (l r) (error 'subst "subst over / unimplemented")]
                [plusC (l r) (plusC (helper l) (helper r))]
                [multC (l r) (multC (helper l) (helper r))]
                [appC (f a) (error 'subst "subst over function application unimplemented")]
                [idC (i) (error 'subst "subst over identifiers unimplemented")])])
      (helper expr))))

(module+ test
  (test (subst 1 'x (idC 'x)) (numC 1))
  (test (subst 1 'x (idC 'y)) (idC 'y))
  (test (subst 1 'x (numC 0)) (numC 0))
  (test (subst 1 'x (divC (idC 'x) (numC 2))) (divC (numC 1) (numC 2)))
  (test (subst 1 'x (plusC (idC 'x) (numC 2))) (plusC (numC 1) (numC 2)))
  (test (subst 1 'x (multC (idC 'x) (numC 2))) (multC (numC 1) (numC 2)))
  (test (subst 1 'x (appC 'f (idC 'x))) (appC 'f (numC 1)))
  (test (subst 1 'x (appC 'x (idC 'x))) (appC 'x (numC 1)))) ; Really need to think about whether this is desired behaviour!

;; SHOULD identifiers be allowed to have the same name as functions?
;; Can we stop it?  (In this language?  In others?)
;;
;; Which mainstream languages enforce functions and variables having
;; different names?

;; TODO 3: implement division, identifiers, and application.

; interpret (evaluate) the given well-formed arithmetic expression AST
(define (interp [ast : ExprC] [fds : (listof FunDefC)]) : number
  (local ([define (helper [ast : ExprC]) : number
            (type-case ExprC ast
              [numC (n) n]
              [divC (l r) (error 'interp "divC case is unimplemented")]
              [plusC (l r) (+ (helper l) (helper r))]
              [multC (l r) (* (helper l) (helper r))]
              [appC (f a) (type-case (optionof FunDefC) (findf (lambda (fd) (symbol=? (fdC-name fd) f)) fds)
                            [some (fd) (error 'interp (string-append (to-string fd) " is the function, but what do I do with it?"))]
                            [none () (error 'interp (string-append "unknown function in: " (to-string ast)))])]
              [idC (i) (error 'interp "identifiers are unimplemented")])])
    (helper ast)))


;; TODO 2: write a few CAREFUL test cases.  See the lecture notes!
(module+ test
  ;; in-class tests
  )

(module+ test
  (define yield1 (fdC 'yield1 'x (numC 1)))
  (define identity (fdC 'identity 'x (idC 'x)))
  (define rename (fdC 'rename 'rename (idC 'rename)))

  (define yield2 (fdC 'yield2 'x (numC 2)))
  (define yield3 (fdC 'yield2 'x (numC 3)))
  
  (define fds1 (list yield1 yield2 yield3))
  (define fds2 (list yield1 yield3 yield2))
  (define fds3 (list yield2 yield1 yield3))
  (define fds4 (list yield2 yield3 yield1))
  (define fds5 (list yield3 yield1 yield2))
  (define fds6 (list yield3 yield2 yield1))
  (define fdss (list fds1 fds2 fds3 fds4 fds5 fds6))
  
  (map (lambda (x) (test (interp (appC 'yield1 (numC 0)) x) 1)) fdss)

  ;; Division test cases.
  (test (interp (divC (numC 1) (numC -2)) empty) (/ -1 2))
  (test/exn (interp (divC (numC 1) (numC 0)) empty) "")


  (test (interp (numC 1) empty) 1)
  (test (interp (plusC (numC 1) (numC -2)) empty) -1)
  (test (interp (multC (numC -3) (numC 2)) empty) -6)
  (test (interp (appC 'yield1 (numC 5)) (list yield1)) 1)
  (test (interp (appC 'identity (numC 5)) (list identity)) 5)
  (test (interp (appC 'rename (numC 5)) (list rename)) 5)

  ; Test one "complex" case, just to be safe.
  (test (interp (desugar (parse '(- (* 2 -1) (+ 3 4)))) empty)
        (- (* 2 -1) (+ 3 4)))
  
  (test/exn (interp (idC 'x) empty) "")
  (test/exn (interp (idC 'x) (list (fdC 'x 'y (numC 0)))) "")
  (test/exn (interp (appC 'foo (numC 0)) fds1) ""))
  
(define (run [sexp : s-expression] [fds : (listof FunDefC)]) : number
  (interp (desugar (parse sexp)) fds))

(module+ test
  ; Test some parsed behaviour
  (test (run '1 empty) 1)
  (test (run '(+ 1 2) empty) (+ 1 2))
  (test (run '(* 2 3) empty) (* 2 3))
  (test (run '(- 2 3) empty) (- 2 3)))
