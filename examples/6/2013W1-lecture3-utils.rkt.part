#lang plai-typed

(print-only-errors true)

; Here's how we import untyped elements of Racket.
; Note that the types I gave were too specific, but that's OK (e.g. for flatten).
(require (typed-in racket 
                   [sort : ((listof 'a) ('a 'a -> boolean) -> (listof 'a))]
                   [remove-duplicates : ((listof 'a) -> (listof 'a))]
                   [flatten : ((listof (listof 'a)) -> (listof 'a))]))

; consumes a list of numbers and produces the normalized set representing that list
; a normalized set is a list with no duplicate elements in sorted order
; the normalized set representing a list is a set in normalized list form
; that is set-equal to the original list
(define (normalize-set [lon : (listof number)]) : (listof number)
  (remove-duplicates (sort lon <)))  ; Side note: could write a more efficient r-d, since it's sorted.

(test (normalize-set empty) empty)
(test (normalize-set (list 888)) (list 888))
(test (normalize-set (list 888 999)) (list 888 999))
(test (normalize-set (list 999 888)) (list 888 999))
(test (normalize-set (list 888 888)) (list 888))
(test (normalize-set (list 888 999 888)) (list 888 999))
(test (normalize-set (list 999 888 888)) (list 888 999))
(test (normalize-set (list 4 2 1 8 2 3 9 5 5 8 2 3 6 6 7 1)) (list 1 2 3 4 5 6 7 8 9))


; consumes a binary function and transforms it into a function over non-deterministic numbers;
; in other words, one that takes in lists representing sets of inputs and produces a 
; (normalized) set of the results of applying the function to each pair of one element from the
; first list and one element from the second.
; contract: ((number number -> number) -> ((listof number) (listof number) -> (norm'dsetof number))
(define (map2-non-deterministic [f : (number number -> number)])
  : ((listof number) (listof number) -> (listof number))
  
  (lambda ([args1 : (listof number)] [args2 : (listof number)])
    (normalize-set (flatten (map (lambda (x) (map (lambda (y) (f x y)) args2)) args1)))))

(test ((map2-non-deterministic +) empty empty) empty)
(test ((map2-non-deterministic +) empty (list 1 2)) empty)
(test ((map2-non-deterministic +) (list 3 4) empty) empty)
(test ((map2-non-deterministic +) (list 1) (list 2)) (list 3))
(test ((map2-non-deterministic +) (list 1) (list 2 3)) (list 3 4))
(test ((map2-non-deterministic +) (list 2 3) (list 1)) (list 3 4))
(test ((map2-non-deterministic +) (list 2 3) (list 1 2)) (list 3 4 5))
(test ((map2-non-deterministic +) (list 2 3) (list 1 6)) (list 3 4 8 9))
(test ((map2-non-deterministic +) (list 1 2 3 4) (list 10 20 30 10)) (list 11 12 13 14 21 22 23 24 31 32 33 34))

(test ((map2-non-deterministic *) empty empty) empty)
(test ((map2-non-deterministic *) empty (list 1 2)) empty)
(test ((map2-non-deterministic *) (list 3 4) empty) empty)
(test ((map2-non-deterministic *) (list 1) (list 2)) (list 2))
(test ((map2-non-deterministic *) (list 1) (list 2 3)) (list 2 3))
(test ((map2-non-deterministic *) (list 2 3) (list 1)) (list 2 3))
(test ((map2-non-deterministic *) (list 2 4) (list 1 2)) (list 2 4 8))
(test ((map2-non-deterministic *) (list 2 3) (list 1 6)) (list 2 3 12 18))
(test ((map2-non-deterministic *) (list 1 2 3 4) (list 10 20 30 10)) (list 10 20 30 40 60 80 90 120))


; A custom "type-case" over an s-expression.
; The four function arguments represent the four cases:
; list, number, symbol, and string.
(define (s-exp-type-case [s-exp : s-expression]
                         [flist : ((listof 'a) -> 'b)]
                         [fnum : (number -> 'b)]
                         [fsym : (symbol -> 'b)]
                         [fstr : (string -> 'b)]) : 'b
  (cond [(s-exp-list? s-exp) (flist (s-exp->list s-exp))]
        [(s-exp-number? s-exp) (fnum (s-exp->number s-exp))]
        [(s-exp-symbol? s-exp) (fsym (s-exp->symbol s-exp))]
        [(s-exp-string? s-exp) (fstr (s-exp->string s-exp))]
        [else (error 's-exp-type-case (string-append (to-string s-exp) " is not a known type of s-expression"))]))

; Here's a useful template for this one:
#;
(define (use-s-exp-type-case-fn [s-exp : s-expression]) : 'a
  (s-exp-type-case s-exp
                   (lambda ([selst : (listof s-expression)]) : 'a 
                     (... (map use-s-exp-type-case-fn selst)))
                   (lambda ([senum : number]) : 'a ...)
                   (lambda ([sesym : symbol]) : 'a ...)
                   (lambda ([sestr : string]) : 'a ...)))

; Helpers for testing s-exp-type-case
(define (any->y-maker [y : 'b]) : ('a -> 'b) (lambda (x) y))
(test ((any->y-maker true) 'foo) true)

;; Some interesting, but not totally relevant, notes below. :)

;; In Haskell, "point-free style" is good style:
;(define any->true (any->y-maker true))
;(define any->false (any->y-maker false))
;; Why can't we use these here?  The answer is somewhat deep, although it comes down to "side effects" (largely: mutation).
;; Here's simpler code that exercises the same problem:
;(define (any->true [x : 'a]) : boolean true)
;(define any->true2 any->true)
;(test (any->true2 5) true)
;(test (any->true2 "5") true)
;; A few notes: (1) it's not the lack of type signature; you can
;; label any->true2 as any->true2 : ('a -> boolean) to see that, and
;; (2) BOTH tests are necessary for this to fail.
(define (any->true [x : 'a]) : boolean ((any->y-maker true) x))
(define (any->false [x : 'a]) : boolean ((any->y-maker false) x))
(test (any->true 'foo) true)
(test (any->false 'foo) false)

; Test that selection works correctly.
(test (s-exp-type-case '(a) any->true any->false any->false any->false) true)
(test (s-exp-type-case (first (s-exp->list '(1 a "a"))) any->false any->true any->false any->false) true)
(test (s-exp-type-case (second (s-exp->list '(1 a "a"))) any->false any->false any->true any->false) true)
(test (s-exp-type-case (third (s-exp->list '(1 a "a"))) any->false any->false any->false any->true) true)

; Test that values come through correctly.
(test (s-exp-type-case '(a) identity 
                       (any->y-maker (list '(WRONG))) 
                       (any->y-maker (list '(WRONG))) 
                       (any->y-maker (list '(WRONG))))
      (s-exp->list '(a)))
(test (s-exp-type-case (first (s-exp->list '(1 a "a"))) (any->y-maker 2) identity (any->y-maker 2) (any->y-maker 2)) 1)
(test (s-exp-type-case (second (s-exp->list '(1 a "a"))) (any->y-maker 'b) (any->y-maker 'b) identity (any->y-maker 'b)) 'a)
(test (s-exp-type-case (third (s-exp->list '(1 a "a"))) (any->y-maker "b") (any->y-maker "b") (any->y-maker "b") identity) "a")

