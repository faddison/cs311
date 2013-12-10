#lang plai-typed

;; Let's convert to Continuation-Passing Style!

(require "utils.rkt")

(module+ test
  (print-only-errors true))

(define-type Value
  [contV (k : ((Value * Store) -> 'a))]
  [boxV (loc : Location)]
  [numV (n : number)]
  [closV (arg : symbol) (body : ExprC) (env : Env)])  

; ExprS ST: arithmetic w/functions anywhere
(define-type ExprS
  [numS (n : number)]
  [plusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [appS (f : ExprS) (a : ExprS)]
  [idS (i : symbol)]
  [lamS (id : symbol) (body : ExprS)]
  [letS (id : symbol) (val : ExprS) (body : ExprS)]
  [letccS (id : symbol) (body : ExprS)]
  [boxS (arg : ExprS)]
  [unboxS (arg : ExprS)]
  [setboxS (box : ExprS) (val : ExprS)]
  [beginS (exps : (listof ExprS)) (return : ExprS)]
  [throwS (e : ExprS)]
  [catchS (e1 : ExprS) (id : symbol) (e2 : ExprS)]
  [throwForwardS]
)

; Annoying import required to specialize and impose types on generic-parse.
(module parser racket
  (provide parse-builder)
  (require "parser.rkt")
  (define (parse-builder numS plusS multS bminusS appS idS lamS letS letccS boxS unboxS setboxS beginS)
    (lambda (sexp)
      (generic-parse sexp
                     #:numTC numS
                     #:bplusTC plusS
                     #:bmultTC multS
                     #:bminusTC bminusS
                     #:bexprAppTC appS
                     #:idTC idS
                     #:lamTC lamS
                     #:uletTC letS
                     #:letccTC letccS
                     #:boxTC boxS
                     #:unboxTC unboxS
                     #:setboxTC setboxS
                     #:arbbeginTC beginS))))

; Continuation of annoying import required to specialize and impose types on generic-parse.
(require (typed-in 'parser [parse-builder : ((number -> ExprS) 
                                             (ExprS ExprS -> ExprS)
                                             (ExprS ExprS -> ExprS)
                                             (ExprS ExprS -> ExprS)
                                             (ExprS ExprS -> ExprS)
                                             (symbol -> ExprS)
                                             (symbol ExprS -> ExprS)
                                             (symbol ExprS ExprS -> ExprS)
                                             (symbol ExprS -> ExprS)
                                             (ExprS -> ExprS)
                                             (ExprS -> ExprS)
                                             (ExprS ExprS -> ExprS)
                                             ((listof ExprS) ExprS -> ExprS)
                                             -> (s-expression -> ExprS))]))

; Finally, we can define our parse function!
(define parse : (s-expression -> ExprS)
  (parse-builder numS plusS multS bminusS appS idS lamS letS letccS boxS unboxS setboxS beginS))





; ExprC AST: arithmetic w/functions anywhere
(define-type ExprC
  [lamC (arg : symbol) (body : ExprC)]  
  [appC (fun : ExprC) (arg : ExprC)]
  [numC (n : number)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [idC (i : symbol)]
  [letccC (i : symbol) (body : ExprC)]
  [beginC (non-return : ExprC) (return : ExprC)]
  [boxC (arg : ExprC)]
  [unboxC (arg : ExprC)]
  [setboxC (b : ExprC) (v : ExprC)]
  [throwC (expr : ExprC)]
  [catchC (e1 : ExprC) (id : symbol) (e2 : ExprC)]
)


; desugar the surface abstract syntax tree into our core abstract syntax tree
(define (desugar [st : ExprS]) : ExprC
  (type-case ExprS st
    [numS (n) (numC n)]
    [plusS (l r) (plusC (desugar l) (desugar r))]
    [multS (l r) (multC (desugar l) (desugar r))]
    [bminusS (l r) (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [appS (f a) (appC (desugar f) (desugar a))]
    [idS (i) (idC i)]
    [lamS (id body) (lamC id (desugar body))]
    [letS (i v b) (appC (lamC i (desugar b)) (desugar v))]
    [letccS (i b) (letccC i (desugar b))]
    [beginS (nrs r) 
            (local [(define (unroll nrs)
                      (if (empty? nrs)
                          (desugar r)
                          (beginC (desugar (first nrs)) (unroll (rest nrs)))))]
              (unroll nrs))
            
            ; Old version; kept to check that the two are equivalent per our test cases (for run, not for desugar, of course!).
            #;(local [(define (unroll nrs)
                        (if (empty? nrs)
                            (desugar r)
                            (appC (lamC 'begin (unroll (rest nrs))) (desugar (first nrs)))))]
                (unroll nrs))]
    [boxS (arg) (boxC (desugar arg))]
    [unboxS (arg) (unboxC (desugar arg))]
    [setboxS (b v) (setboxC (desugar b) (desugar v))]
    
    ;; for final exam practice
    [throwS (e) (throwC (desugar e))]
    [catchS (e1 i e2) (catchC (desugar e1) i (desugar e2))] ;; is this all that needs to be done?
    [throwForwardS () (throwForwardC)]
    ;; [throwForwardS () (throwC (IdC current-id))] throws unbound identifer because i hasnt been set yet?
    ;; [plusS (lexp rexp) (plusC (desugar lexp) (desugar rexp))]
	)
)

(define-type-alias Location number)

(define-type Binding
  [bind (name : symbol) (loc : Location)])

(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)

(define-type Storage
  [cell (location : Location) (val : Value)])

(define-type-alias Store (listof Storage))
(define mt-store empty)
(define extend-store cons)
(define override-store cons)


; look up the id in env, giving an error if id is not present
(define (lookup [id : symbol] [env : Env]) : Location
  (type-case (optionof Binding) (findf (lambda (binding) (symbol=? (bind-name binding) id)) env)
    [some (binding) (bind-loc binding)]
    [none () (error 'lookup (string-append "no binding found for identifier: " (to-string id)))]))

; look up the location in the store, giving an error if the location is not present.
(define (fetch [loc : Location] [sto : Store]) : Value
  (type-case (optionof Storage) (findf (lambda (cell) (= (cell-location cell) loc)) sto)
    [some (cell) (cell-val cell)]
    [none () (error 'fetch (string-append "no cell found for location: " (to-string loc)))]))

; get a new location number
; assumes location numbers are all positive
(define (new-loc [store : Store]) : Location
  (+ (foldl max 0 (map cell-location store)) 1))

; interpret (evaluate) the given well-formed arithmetic expression AST in the given environment and store
;; TODO: convert to CPS.  To ensure that we've done that, we'll have an error as the second statement of
;; the body of interp (and helper, where all the work really happens).  If ever we reach that error, 
;; we're not in CPS!  After all, CPS should ALWAYS continue with the continuation, NOT return to where it
;; came from.  (To really accomplish that, we need to make sure our very first continuation will itself
;; "cut off" evaluation, or else DrRacket will roll us back to all those errors!  Later on, we'll 
;; want to take the errors out so that the recursive calls are in tail position (else, DrRacket will
;; waste memory storing a bunch of continuations of our recursive calls that really should be in tail
;; position!).
(define (interp [ast : ExprC] [env : Env] [store : Store]) : (Value * Store)
  (local [(define (interp-only/k [pred? : (Value -> boolean)] 
                                 [err : string]
                                 [ast : ExprC]
                                 [env : Env]
                                 [store : Store]
                                 k) : (Value * Store)
            (helper/k ast env store
                      (lambda (result*store2)
                        (local [(define-values (result store2) result*store2)]
                          ;; TODO: decide whether to convert pred? to pred?/k
                          (if (pred? result)
                              (k (values result store2))
                              (error 'interp (string-append err (to-string ast))))))))
          (define (helper/k [ast : ExprC] [env : Env] [store : Store] k) : (Value * Store)
              (type-case ExprC ast
              
                ;; Here's our cool new functionality!
                ;;
                ;; We bind the id to the continuation of THIS expression and then
                ;; evaluate the body in tail position.
                ;; 
                ;; Happily, k IS the continuation of THIS expression.
                ;;
                ;; Notice that this "uses k" twice:
                ;; as the continuation of the actual interpretation of the body
                ;; and as a value in the environment.
                ;;
                ;; In turn, when we apply a contV in the appC case, we'll "use k"
                ;; ZERO times.  (So, we kind of "balance out".. much like what happens
                ;; with the env parameter when creating/using a closure.)
                [letccC (id body)
                        (local [(define addr (new-loc store))]
                          (helper/k
                           body 
                           (extend-env (bind id addr) env)
                           (extend-store (cell addr (contV k)) store)
                           k))]
                           
                [throwC (e) (k (error 'throw (to-string e)))]
                ;; do we throw a real error here?
                ;; what does the catcher continuation do? What makes it different than k?
                
                [catchC (e1 id e2) 
                	(helper/k e1 env store 
                		(lambda (e1-result)
                			(local [(define-values (e1-value e1-store) e1-result)]
                				(if (numV? e1-value)
                					(k (values e1-value e1-store))
                					(helper/k e2 env e1-store k)
                				)
                			)
                		)
                	)
                ]
                ;; how can we use letccC here?
                ;; how do we handle the error here?
                ;; do we pass to interp, interp-only, or helper?
                ;; how can we use the continuation to revert to a previous state?
                
                
                           
                [numC (n) (k (values (numV n) store))]   
                [beginC (e1 e2) 
                        (helper/k e1 env store
                                  (lambda (e1-result)
                                    (local [(define-values (e1-value e1-store) e1-result)]
                                      ;; We COULD say:
                                      ;
                                      ; (helper/k e2 env e1-store (lambda (e2-result) (k e2-result)))
                                      ;
                                      ; But, (lambda (e2-result) (k e2-result)) just says "get the result
                                      ; from e2 and then 'pass it forward' to the remaining work k."
                                      ;
                                      ; Instead, we decided to just say "the remaining work IS k", which
                                      ; amounts to the same thing but in fewer words (and less space in
                                      ; the implementation!!).
                                      ;
                                      ; THAT is what a tail call looks like! :)
                                      (helper/k e2 env e1-store k))))]
                [setboxC (be ve) 
                         (interp-only/k 
                          boxV? "expected box value from: " be env store
                          (lambda (be-result)
                            (local [(define-values (be-value be-store) be-result)]
                              (helper/k
                               ve env be-store
                               (lambda (ve-result)
                                 (local [(define-values (ve-value ve-store) ve-result)]
                                   (k (values ve-value 
                                              (override-store (cell (boxV-loc be-value) ve-value) ve-store)))))))))]
                [plusC (l r) 
                       (interp-only/k
                        numV? "expected numeric value from: " l env store
                        (lambda (l-result)
                          (local [(define-values (lvalue lstore) l-result)
                                  (define lnum (numV-n lvalue))]
                            (interp-only/k
                             numV? "expected numeric value from: " r env lstore
                             (lambda (r-result)
                               (local [(define-values (rvalue rstore) r-result)
                                       (define rnum (numV-n rvalue))]
                                 (k (values (numV (+ lnum rnum)) rstore))))))))]
                [multC (l r)
                       (interp-only/k
                        numV? "expected numeric value from: " l env store
                        (lambda (l-result)
                          (local [(define-values (lvalue lstore) l-result)
                                  (define lnum (numV-n lvalue))]
                            (interp-only/k
                             numV? "expected numeric value from: " r env lstore
                             (lambda (r-result)
                               (local [(define-values (rvalue rstore) r-result)
                                       (define rnum (numV-n rvalue))]
                                 (k (values (numV (* lnum rnum)) rstore))))))))]
                [appC (f a) 
                      (interp-only/k
                       (lambda (x) (or (closV? x) (contV? x)))
                       "expected a closure (function value) for application from: " f env store
                       (lambda (f-result)
                         (local [(define-values (fv store2) f-result)]
                           (helper/k 
                            a env store2
                            ;; If the "function" is a closure, then we do the normal thing:
                            ;; call the function and eventually "return" to k.
                            ;;
                            ;; However, if the "function" is actually a continuation, we're
                            ;; asking to REPLACE k with the continuation.  So, we just supply
                            ;; it INSTEAD OF k to the call to helper to evaluate a!
                            ;;
                            ;; As noted in the letcc case above, notice how we use k ZERO
                            ;; times here if fv is a continuation.
                            (if (closV? fv)
                                (lambda (a-result)
                                  (local [(define-values (av store3) a-result)
                                          (define fv-arg (closV-arg fv))
                                          (define fv-body (closV-body fv))
                                          (define fv-env (closV-env fv))
                                          (define addr (new-loc store3))]
                                    ; Where should we return to after we run the function?
                                    ; Well, right "here", of course.  To whatever code uses
                                    ; the function's return value, which is just what k
                                    ; represents.
                                    (helper/k fv-body 
                                              (extend-env (bind fv-arg addr) fv-env) 
                                              (extend-store (cell addr av) store3)
                                              k)))
                                (contV-k fv))))))]
                [lamC (arg body) (k (values (closV arg body env) store))]
                [idC (i) (k (values (fetch (lookup i env) store) store))]
                [boxC (a) 
                      (helper/k 
                       a env store
                       (lambda (a-result)
                         (local [(define-values (result store2) a-result)
                                 (define addr (new-loc store2))]
                           (k (values (boxV addr) (extend-store (cell addr result) store2))))))]
                [unboxC (a)
                        (interp-only/k 
                         boxV? "expected box value from: " a env store
                         (lambda (a-result)
                           (local [(define-values (result store2) a-result)]
                             (k (values (fetch (boxV-loc result) store2) store2)))))]))]
    ;; TODO: For testing purposes, wrap helper/k's body above so that it looks like:
    ;; (begin ... (error 'helper/k "shouldn't ever return!"))
    ;; 
    ;; Then, replace the call to helper/k below with:
    ;;
    ;; (let/cc k
    ;;   (helper/k ast env store k))
    ;; 
    ;; What this does is to tell helper/k that its continuation is the same as the one
    ;; that called interp itself.  "let/cc" stands for "let current continuation".
    ;;
    ;; When THIS k is applied, it will "travel back in time" to the point that interp
    ;; was called and return the value passed to it as interp's result.  It will NEVER
    ;; return to the point in the runtime call tree that called k.  (In other words,
    ;; this "k" is NOT quite a normal function.  It's like a normal function call except
    ;; that it IGNORES its own continuation.)
    (helper/k ast env store identity)))


(define (interp-to-val ast env store)
  (local [(define-values (value ignore) (interp ast env store))]
    value))

(define (run [sexp : s-expression]) : Value
  (local [(define-values (result store) (interp (desugar (parse sexp)) mt-env mt-store))]
    result))




;;;;;;;;;;;;; parse tests ;;;;;;;;;;;;;;;;;;;;;;;

; This should be replaced with tests that just ensure that we get
; the right type constructors for the right syntax with the right
; order of arguments.  (Everything else is tested inside parse-builder.)
; I've cut to just this type of test.  We need more!
(module+ test
  (test (parse '1) (numS 1))
  (test (parse '(+ 1 2)) (plusS (numS 1) (numS 2)))
  (test (parse '(* 1 2)) (multS (numS 1) (numS 2)))
  (test (parse '(- 1 2)) (bminusS (numS 1) (numS 2)))
  (test (parse '(a 1)) (appS (idS 'a) (numS 1)))
  (test (parse (symbol->s-exp 'a)) (idS 'a)))

;;;;;;;;;;;;; desugar tests ;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (test (desugar (beginS empty (numS 1)))
        (numC 1))
  (test (desugar (beginS (list (numS 1)) (numS 2)))
        (beginC (numC 1) (numC 2)))
  (test (desugar (beginS (list (numS 1) (numS 2) (numS 3)) (numS 4)))
        (beginC (numC 1) (beginC (numC 2) (beginC (numC 3) (numC 4)))))
  (test (desugar (letS 'x (numS 1) (numS 2)))
        (appC (lamC 'x (numC 2)) (numC 1)))
  
  (test (desugar (lamS 'x (numS 1)))
        (lamC 'x (numC 1)))
  
  (test (desugar (numS 1)) (numC 1))
  (test (desugar (plusS (numS 1) (numS 2))) (plusC (numC 1) (numC 2)))
  (test (desugar (multS (numS 1) (numS 2))) (multC (numC 1) (numC 2)))
  (test (desugar (bminusS (numS 1) (numS 2))) (plusC (numC 1) (multC (numC -1) (numC 2))))
  (test (desugar (appS (idS 'f) (idS 'x))) (appC (idC 'f) (idC 'x)))
  (test (desugar (idS 'x)) (idC 'x))
  
  ; Test one "complex" case, just to be safe.
  (test (desugar (bminusS (multS (numS 1) (numS 2))
                          (plusS (numS 3) (numS 4))))
        (plusC (multC (numC 1) (desugar (numS 2)))
               (multC (numC -1) (plusC (numC 3) (numC 4))))))


;;;;;;;;;;;;; store-related tests ;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (test (new-loc empty) 1)
  (test (new-loc (list (cell 3 (numV 0)) (cell 5 (numV 1)) (cell 1 (numV 2)))) 6)
  
  (test/exn (lookup 'a mt-env) "")
  (test (lookup 'a (extend-env (bind 'a 1) mt-env)) 1)
  (test (lookup 'a (extend-env (bind 'a 2) (extend-env (bind 'a 1) mt-env))) 2)
  (test (lookup 'a (extend-env (bind 'b 2) (extend-env (bind 'a 1) mt-env))) 1)
  (test (lookup 'b (extend-env (bind 'b 2) (extend-env (bind 'a 1) mt-env))) 2)
  (test/exn (lookup 'c (extend-env (bind 'b 2) (extend-env (bind 'a 1) mt-env))) "")
  
  (test/exn (fetch 1 mt-store) "")
  (test (fetch 1 (extend-store (cell 1 (numV 1)) mt-store)) (numV 1))
  (test (fetch 1 (override-store (cell 1 (numV 2)) (extend-store (cell 1 (numV 1)) mt-store))) (numV 2))
  (test (fetch 1 (extend-store (cell 2 (numV 2)) (extend-store (cell 1 (numV 1)) mt-store))) (numV 1))
  (test (fetch 2 (extend-store (cell 2 (numV 2)) (extend-store (cell 1 (numV 1)) mt-store))) (numV 2))
  (test (fetch 6 (extend-store (cell 6 (closV 'x (numC 0) mt-env)) mt-store)) (closV 'x (numC 0) mt-env))
  (test/exn (fetch 3 (extend-store (cell 2 (numV 2)) (extend-store (cell 1 (numV 1)) mt-store))) "")) 

;;;;;;;;;;;;; interp/run tests ;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  ; Shriram's static scoping test
  (test (interp-to-val (appC (appC (lamC 'x
                                         (lamC 'y
                                               (plusC (idC 'x) (idC 'y))))
                                   (numC 4))
                             (numC 5)) mt-env mt-store) (numV 9))
  
  (test (interp-to-val (lamC 'x (idC 'y)) (extend-env (bind 'y 1) mt-env) (extend-store (cell 1 (numV 5)) mt-store))
        (closV 'x (idC 'y) (extend-env (bind 'y 1) mt-env)))
  (test (interp-to-val (appC (lamC 'x (idC 'x)) (numC 1)) mt-env mt-store) (numV 1))
  (test (interp-to-val (appC (lamC 'x (numC 2)) (numC 1)) mt-env mt-store) (numV 2))
  
  ; We SHOULD get access to this y, since the function's lexical scope includes this "definition".
  (test (interp-to-val (appC (lamC 'x (idC 'y)) (numC 1)) (extend-env (bind 'y 1) mt-env) (extend-store (cell 1 (numV 5)) mt-store))
        (numV 5))
  
  ; Now, let's play with static vs. dynamic scope.  We want something like:
  ; (let ((x 1))
  ;   (let ((f (lambda (y) (+ x y)))
  ;     (let ((x 10))
  ;       (let ((y 100))
  ;          (f 1000))))) => 1001
  ; We can also strip the outermost binding and get an exception.
  ; We can also strip the innermost two bindings with no effect.
  ; Here's a translation of that:
  ; (appC (lamC 'x (appC (lamC 'f (appC (lamC 'x (appC (lamC 'y (appC (idC 'f (numC 1000)))))
  ;                                                                (numC 100)))
  ;                                             (numC 10)))
  ;                          (lamC 'y (plusC (idC 'x) (idC 'y)))))
  ;       (numC 1))
  
  (test (interp-to-val (appC (lamC 'x (appC (lamC 'f (appC (idC 'f) (numC 1000)))
                                            (lamC 'y (plusC (idC 'x) (idC 'y)))))
                             (numC 1)) 
                       mt-env mt-store)
        (numV 1001))
  (test (interp-to-val (appC (lamC 'x (appC (lamC 'f (appC (lamC 'x (appC (lamC 'y (appC (idC 'f) (numC 1000)))
                                                                          (numC 100)))
                                                           (numC 10)))
                                            (lamC 'y (plusC (idC 'x) (idC 'y)))))
                             (numC 1)) 
                       mt-env mt-store)
        (numV 1001))
  (test/exn (interp-to-val (appC (lamC 'f (appC (lamC 'x (appC (lamC 'y (appC (idC 'f) (numC 1000)))
                                                               (numC 100)))
                                                (numC 10)))
                                 (lamC 'y (plusC (idC 'x) (idC 'y))))
                           mt-env mt-store)
            "")
  
  (test/exn (interp (appC (numC 1) (numC 0)) mt-env mt-store) "")
  (test/exn (interp (plusC (lamC 'x (numC 1)) (numC 0)) mt-env mt-store) "")
  
  (test (interp-to-val (numC 1) mt-env mt-store) (numV 1))
  (test (interp-to-val (plusC (numC 1) (numC -2)) mt-env mt-store) (numV -1))
  (test (interp-to-val (multC (numC -3) (numC 2)) mt-env mt-store) (numV -6))
  
  ; Test one "complex" case, just to be safe.
  (test (interp-to-val (desugar (parse '(- (* 2 -1) (+ 3 4)))) mt-env mt-store)
        (numV (- (* 2 -1) (+ 3 4))))
  
  (test/exn (interp (idC 'x) mt-env mt-store) "")
  
  (test (interp-to-val (idC 'x) (extend-env (bind 'x 5) mt-env) (extend-store (cell 5 (numV 5)) mt-store)) (numV 5))
  
  ; Mutability testing.
  (test (run '(let (a 3) (begin a a))) (numV 3)) ; purely for coverage
  
  (test (run '(unbox (box 1))) (numV 1))
  (test (run '(unbox (unbox (box (box 1))))) (numV 1))
  (test (run '(let (b (box 1))
                (begin
                  (set-box! b 2)
                  (unbox b))))
        (numV 2))
  (test (run '(let (b (box 1))
                (+
                 (begin (set-box! b (* 10 (unbox b)))
                        (unbox b))
                 (begin (set-box! b (* 10 (unbox b)))
                        (unbox b)))))
        (numV 110))
  (test (run '(let (b (box 1))
                (*
                 (begin (set-box! b (* 10 (unbox b)))
                        (unbox b))
                 (begin (set-box! b (* 10 (unbox b)))
                        (unbox b)))))
        (numV 1000))
  (test (run '(let (b (box 1))
                (+ (*
                    (+
                     (begin (set-box! b (* 10 (unbox b)))
                            (unbox b))
                     (begin (set-box! b (* 10 (unbox b)))
                            (unbox b)))
                    2)
                   (unbox b))))
        (numV 320))
  (test (run '(let (*10! (lambda (x) 
                           (begin 
                             (set-box! x (* 10 (unbox x)))
                             (unbox x))))
                (let (b (box 1))
                  ((begin (*10! b)
                          *10!)
                   (box (+ (unbox b) (*10! b)))))))
        (numV 1100))
  (test (run '(let (*10! (lambda (x) 
                           (begin 
                             (set-box! x (* 10 (unbox x)))
                             (unbox x))))
                (let (b (box 1))
                  (begin
                    (set-box! (begin (*10! b) b)
                              (+ 1 (*10! b)))
                    (unbox b)))))
        (numV 101))
  
  (test (run '(let (b (box 0))
                (unbox (unbox (box (begin (set-box! b 1) b))))))
        (numV 1))
  
  )


(module+ test
  ; Some Ch 8 examples in passing.
  
  (test (run '(let (new-loc
                    (let (n (box 0))
                      (lambda (ignore)
                        (begin
                          (set-box! n (+ (unbox n) 1))
                          (unbox n)))))
                (begin
                  (new-loc 0)
                  (new-loc 0))))
        (numV 2))
  
  (test (run '(let (new-loc
                    (lambda (ignore)
                      (let (n (box 0))
                        (begin
                          (set-box! n (+ (unbox n) 1))
                          (unbox n)))))
                (begin
                  (new-loc 0)
                  (new-loc 0))))
        (numV 1))
  
  (test (run '(let (b (box 0))
                (begin (begin (set-box! b (+ 1 (unbox b)))
                              (set-box! b (+ 1 (unbox b))))
                       (unbox b))))
        (numV 2))
  
  (test (run '(let (b (box 0))
                (+ (begin (set-box! b (+ 1 (unbox b)))
                          (unbox b))
                   (begin (set-box! b (+ 1 (unbox b)))
                          (unbox b)))))
        (numV 3))
  
  (test/exn (run '(+ (let (b (box 0))
                       1)
                     b)) "")
  
  (test (run '(let (a (box 1))
                (let (f (lambda (x) (+ x (unbox a))))
                  (begin
                    (set-box! a 2)
                    (f 10)))))
        (numV 12))
  
  (test/exn (run '(set-box! 1 0)) "")
  (test/exn (run '(unbox 0)) "")
  
  ; I'm bad.  I missed this in testing!
  (test (run '(let (b1 (box 0))
                (let (b2 (box 10))
                  (begin
                    (set-box! b1 (begin (set-box! b2 100) 1))
                    (unbox b2)))))
        (numV 100)))
        
  ;; final exam tests
  ;; throwC
  
  (test/exn (interp-to-val (throwC (numC 1)) mt-env mt-store) "throw: (numC 1)")
  
  ;; catchC
  (test (interp-to-val (catchC (numC 1) 'x (numC 2)) mt-env mt-store) (numV 1))
	;;(test/exn (interp-to-val (catchC (throwC (numC 2)) 'x (numC 2)) mt-env mt-store) "throw: (numC 2)")
	;;(test (interp-to-val (catchC  'x (numC 3)) mt-env mt-store) (numV 3))
	(test (interp-to-val (catchC (throwC (numC 2)) 'x (numC 3)) mt-env mt-store) (numV 3))


(module+ test
  ; Test some parsed behaviour
  (test (run '1) (numV 1))
  (test (run '(+ 1 2)) (numV (+ 1 2)))
  (test (run '(* 2 3)) (numV (* 2 3)))
  (test (run '(- 2 3)) (numV (- 2 3)))
  
  (test (run '(let (x 1) x)) (numV 1))
  (test (run '(let (x 1) (let (f (lambda (y) (+ x y))) (let (x 10) (let (y 100) (f 1000)))))) (numV 1001))
  
  (test (run '(begin 1 2)) (numV 2)))
