#lang plai-typed

;; General utilities missing presently from plai-typed.

(module+ test
  (print-only-errors true))

; A custom "type-case" over an s-expression.
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


(module+ test
  ; Helpers for testing s-exp-type-case
  (define (any->y-maker [y : 'b]) : ('a -> 'b) (lambda (x) y))
  (test ((any->y-maker true) 'foo) true)
  
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
  (test (s-exp-type-case (third (s-exp->list '(1 a "a"))) (any->y-maker "b") (any->y-maker "b") (any->y-maker "b") identity) "a"))

(module+ main
  (print-only-errors true))


;; Could also just import from Racket and give a type.  Here, we
;; implement it directly.
; find and return the first element in the list matching the given predicate 
; (or none if no predicate matches)
(define findf : (('a -> boolean) (listof 'a) -> (optionof 'a))
  (lambda (pred? lst)
    (let ((matches (filter pred? lst)))
      (if (empty? matches)
          (none)
          (some (first matches))))))

(module+ test
  (test (findf identity (list true false)) (some true))
  (test (findf identity (list false true)) (some true))
  (test (findf identity (list false false)) (none))
  
  (test (findf (lambda (x) (local ([define-values (a b) x]) a))
               (list (values true 5)
                     (values true 7)
                     (values false 8)
                     (values true 9)))
        (some (values true 5)))
  
  (test (findf (lambda (x) (local ([define-values (a b) x]) a))
               (list (values false 5)
                     (values true 7)
                     (values false 8)
                     (values true 9)))
        (some (values true 7)))
  
  (test (findf (lambda (x) (local ([define-values (a b) x]) a))
               (list (values false 5)
                     (values false 7)
                     (values false 8)
                     (values false 9)))
      (none)))
  