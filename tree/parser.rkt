#lang racket


;; This is a rather basic generic parser.  I have been working on a
;; better one, but it's difficult to write one that is nicely generic
;; and yet will type correctly in plai-typed without substantial
;; effort on the import!

(provide generic-parse)

(require (only-in plai-typed [error plai-error]))

;; Attractive changes:
;; - obviously, replace with a declarative(-ish) yacc-like tool as in the Racket Parser Tools library.
;; - semi-automate production of binary (and unary?) operators
;; - switch to accepting a hash table
;; - reduce repetition of key tokens (i.e., shouldn't need to "declare" the name bplus in so many places!)

(require rackunit)

; Used as a default type for unimplemented syntax below.
(struct parse-error (errFun))

; Make a "fake" match predicate that returns true only if the given syntax 
; type constructor is a real (not default parse-error) constructor.
(define (syn-pred-maker synTC)
  (lambda (expr)
    (not (parse-error? synTC))))

; Construct a function to report a type error for the given syntax type.
(define (error-maker syn-name [context 'generic-parse])
  (parse-error (lambda (expr)
                 (plai-error context 
                        (format "~a syntax unsupported in this language, in expr: ~a" 
                                syn-name expr)))))

;; generic-parse : sexp -> [AST structure passed in]
;; Consumes an sexp and generates the corresponding AST,
;; according to the language provided.
;;
;; Supports all the basic syntax types required in PLAI. 
;;
;; To add a new syntactic construct:
;; (1) Add it to the test cases below.
;; (2) Add it to the list of keyword arguments here as: #:<name>TC [<name>TC (error-maker "<long name>")]
;; (3) Add it to the set of reserved words below (see the definition of reserved-words inside parse).
;; (4) Add appropriate match cases to parse it inside parse's helper function.
(define (generic-parse
         expr
         #:numTC [numTC (error-maker "number")]
         #:bplusTC [bplusTC (error-maker "binary addition")]
         #:bmultTC [bmultTC (error-maker "binary multiplication")]
         #:bminusTC [bminusTC (error-maker "binary subtraction")]
         #:bAppTC [bAppTC (error-maker "named function application")]
         #:bexprAppTC [bexprAppTC (error-maker "one-argument arbitrary function application")]
         #:idTC [idTC (error-maker "identifier reference")]
         #:lamTC [lamTC (error-maker "anonymous function construction")]
         #:fdTC [fdTC (error-maker "named function construction")]
         #:uletTC [uletTC (error-maker "unary let binding")]
         #:arbletTC [arbletTC (error-maker "arbitrary size let bindings")]
         #:uminusTC [uminusTC (error-maker "unary negation")]
         #:ifTC [ifTC (error-maker "if-then-else")]
         #:leqTC [leqTC (error-maker "less-than-or-equal")]
         #:ltTC [ltTC (error-maker "less-than")]
         #:geqTC [geqTC (error-maker "greater-than-or-equal")]
         #:gtTC [gtTC (error-maker "greater-than")]
         #:eqTC [eqTC (error-maker "equal")]
         #:neqTC [neqTC (error-maker "not-equal")]
         #:bandTC [bandTC (error-maker "binary logical and")]
         #:borTC [borTC (error-maker "binary logical or")]
         #:notTC [notTC (error-maker "logical negation")]
         #:boxTC [boxTC (error-maker "box creation")]
         #:unboxTC [unboxTC (error-maker "unboxing")]
         #:setboxTC [setboxTC (error-maker "set-box")]
         #:bbeginTC [bbeginTC (error-maker "binary begin sequence")]
         #:arbbeginTC [arbbeginTC (error-maker "arbitrary begin sequence")]
         #:setTC [setTC (error-maker "variable set")]
         #:letccTC [letccTC (error-maker "letcc (continuation binding)")]
         #:discardTC [discardTC (error-maker "discard journal")]
         #:commitTC [commitTC (error-maker "commit journal")])
  (local [(define (collect-reserved-words tc symbols)
            (if (parse-error? tc)
                empty
                symbols))
	  (define constructor-symbols
	    (hash numTC empty
		  bplusTC '(+)
		  bmultTC '(*)
		  bminusTC '(-)
		  bexprAppTC empty
		  bAppTC empty
		  idTC empty
		  lamTC '(lambda)
		  fdTC '(define)
		  uletTC '(let)
		  arbletTC '(let)
                  ifTC '(if)
		  uminusTC '(-)
		  leqTC '(<=)
		  ltTC '(<)
		  geqTC '(>=)
		  gtTC '(>)
		  eqTC '(=)
		  neqTC '(!=)
		  bandTC '(and)
		  borTC '(or)
		  notTC '(not)
		  boxTC '(box)
		  unboxTC '(unbox)
		  setboxTC '(set-box!)
		  bbeginTC '(begin)
		  arbbeginTC '(begin)
		  setTC '(set!)
		  letccTC '(letcc)
		  discardTC '(discard!)
		  commitTC '(commit!!)))

          ; List of type constructors and parallel list of reserved words.
	  ; The pairs are actually declared above in the definition of constructor-symbols.
          (define reserved-words
            (flatten (hash-map constructor-symbols collect-reserved-words)))
          (define (reserved? sexp)
            (not (equal? #f (member sexp reserved-words))))
          (define (valid-id? sexp)
            (and (symbol? sexp) (not (reserved? sexp))))
          (define (helper expr)
            {match expr
              [(and (? (syn-pred-maker numTC))
                    (? number?)) 
               (numTC expr)]
	      [(and (? (syn-pred-maker leqTC))
		    (list '<= lexp rexp))
	       (leqTC (helper lexp) (helper rexp))]
	      [(and (? (syn-pred-maker ltTC))
		    (list '< lexp rexp))
	       (ltTC (helper lexp) (helper rexp))]
	      [(and (? (syn-pred-maker geqTC))
		    (list '>= lexp rexp))
	       (geqTC (helper lexp) (helper rexp))]
	      [(and (? (syn-pred-maker gtTC))
		    (list '> lexp rexp))
	       (gtTC (helper lexp) (helper rexp))]
	      [(and (? (syn-pred-maker eqTC))
		    (list '= lexp rexp))
	       (eqTC (helper lexp) (helper rexp))]
	      [(and (? (syn-pred-maker neqTC))
		    (list '!= lexp rexp))
	       (neqTC (helper lexp) (helper rexp))]
	      [(and (? (syn-pred-maker bandTC))
		    (list 'and lexp rexp))
	       (bandTC (helper lexp) (helper rexp))]
	      [(and (? (syn-pred-maker borTC))
		    (list 'or lexp rexp))
	       (borTC (helper lexp) (helper rexp))]
	      [(and (? (syn-pred-maker notTC))
		    (list 'not arg-exp))
	       (notTC (helper arg-exp))]
	      [(and (? (syn-pred-maker bplusTC))
                    (list '+ lexp rexp))
               (bplusTC (helper lexp) (helper rexp))]
              [(and (? (syn-pred-maker bmultTC))
                    (list '* lexp rexp))
               (bmultTC (helper lexp) (helper rexp))]
              [(and (? (syn-pred-maker bminusTC))
                    (list '- lexp rexp))
               (bminusTC (helper lexp) (helper rexp))]
              [(and (? (syn-pred-maker uminusTC))
                    (list '- arg-exp))
               (uminusTC (helper arg-exp))]
              [(and (? (syn-pred-maker idTC))
                    (? valid-id?))
               (idTC expr)]
              [(and (? (syn-pred-maker lamTC))
                    (list 'lambda (list (? valid-id? param)) body-exp))
               (lamTC param (helper body-exp))]
              [(and (? (syn-pred-maker fdTC))
                    (list 'define (list (? valid-id? name) (? valid-id? arg)) body-exp))
               (fdTC name arg (helper body-exp))]
              [(and (? (syn-pred-maker uletTC))
                    (list 'let (list (? valid-id? id) bound-exp) body-exp))
               (uletTC id (helper bound-exp) (helper body-exp))]
              [(and (? (syn-pred-maker arbletTC))
                    (list 'let (list (list (? valid-id? ids) bound-exps) ...) body-exp))
               (arbletTC ids (map helper bound-exps) (helper body-exp))]
              [(and (? (syn-pred-maker ifTC))
                    (list 'if cexp texp eexp))
               (ifTC (helper cexp) (helper texp) (helper eexp))]
	      [(and (? (syn-pred-maker boxTC))
		    (list 'box arg-exp))
	       (boxTC (helper arg-exp))]
	      [(and (? (syn-pred-maker unboxTC))
		    (list 'unbox arg-exp))
	       (unboxTC (helper arg-exp))]
	      [(and (? (syn-pred-maker setboxTC))
		    (list 'set-box! box-exp val-exp))
	       (setboxTC (helper box-exp) (helper val-exp))]
	      [(and (? (syn-pred-maker bbeginTC))
		    (list 'begin exp1 exp2))
	       (bbeginTC (helper exp1) (helper exp2))]
	      [(and (? (syn-pred-maker arbbeginTC))
		    (list 'begin exps ... return))
	       (arbbeginTC (map helper exps) (helper return))]
	      [(and (? (syn-pred-maker setTC))
		    (list 'set! (? valid-id? var) val-exp))
	       (setTC var (helper val-exp))]
	      [(and (? (syn-pred-maker letccTC))
		    (list 'letcc (? valid-id? id) body-exp))
	       (letccTC id (helper body-exp))]
	      [(and (? (syn-pred-maker discardTC))
		    (list 'discard!))
	       (discardTC)]
	      [(and (? (syn-pred-maker commitTC))
		    (list 'commit!!))
	       (commitTC)]

              ; Be careful with apps.  It requires a certain amount of lookahead to recognize 
              ; that a bexprAppTC-looking construct like '(begin 1) is invalid because of a
              ; reserved word.  By then, we're too late in this parser to backtrack and switch 
              ; to the begin construct.
              [(and (? (syn-pred-maker bAppTC))
                    (list (and (? valid-id?) fun-id) arg-exp))
               (bAppTC fun-id (helper arg-exp))]
              [(and (? (syn-pred-maker bexprAppTC))
                    (list fun-exp arg-exp))
               (bexprAppTC (helper fun-exp) (helper arg-exp))]

              [_ (plai-error 'generic-parse (format "Unable to parse expr: ~a" expr))]})]
    (helper expr)))

(module+ test
  (define (tag-maker tc)
    (lambda args (cons tc args)))
  
  (define (truef exn)
    true)

  (test-exn "Error on empty sexp" ; using app b/c it seems like a likely error source, but this is always an error.
            truef
            (lambda () (generic-parse '() 
                              #:idTC (tag-maker "id")
                              #:bexprAppTC (tag-maker "app"))))
  
  (test-equal? "Basic Number Parsing" 
               (generic-parse '5 #:numTC (tag-maker "num"))
               '("num" 5))
  
  (test-exn "Error on num if no number parsing" 
            truef
            (lambda () (generic-parse '5)))
  
  (test-equal? "Basic if-then-else parsing"
               (generic-parse '(if x y z)
                      #:idTC (tag-maker "id")
                      #:ifTC (tag-maker "if"))
               '("if" ("id" x) ("id" y) ("id" z)))
  
  (test-case "Arity for if-then-else expressions"
             (check-exn truef (lambda () (generic-parse '(if) #:idTC (tag-maker "id") #:ifTC (tag-maker "if"))))
             (check-exn truef (lambda () (generic-parse '(if x) #:idTC (tag-maker "id") #:ifTC (tag-maker "if"))))
             (check-exn truef (lambda () (generic-parse '(if x y) #:idTC (tag-maker "id") #:ifTC (tag-maker "if"))))
             (check-exn truef (lambda () (generic-parse '(if w x y z) #:idTC (tag-maker "id") #:ifTC (tag-maker "if")))))
  
  (test-case "'if' is reserved if and only if the if-then-else syntax is defined"
             (check-equal? (generic-parse 'if #:idTC (tag-maker "id")) '("id" if))
             (check-exn truef (lambda () (generic-parse 'if #:idTC (tag-maker "id") #:ifTC (tag-maker "if")))))
  
  (test-equal? "Basic binary addition parsing"
               (generic-parse '(+ 2 3)
                      #:numTC (tag-maker "num")
                      #:bplusTC (tag-maker "bplus"))
               '("bplus" ("num" 2) ("num" 3)))
  
  (test-exn "Error on binary addition if no bplus parsing" 
            truef
            (lambda () (generic-parse '(+ 2 3) #:numTC (tag-maker "num"))))
  
  (test-exn "+ is reserved if a plus operator is defined"
            truef
            (lambda () (generic-parse '+ 
                              #:idTC (tag-maker "id")
                              #:bplusTC (tag-maker "bplus"))))
  
  (test-exn "Error on binary addition with zero args"
            truef
            (lambda () (generic-parse '(+)
                              #:idTC (tag-maker "id")
                              #:bplusTC (tag-maker "bplus"))))
  
  (test-exn "Error on binary addition with one arg"
            truef
            (lambda () (generic-parse '(+ x)
                              #:idTC (tag-maker "id")
                              #:bplusTC (tag-maker "bplus"))))
  
  (test-exn "Error on binary addition with three args"
            truef
            (lambda () (generic-parse '(+ x y z)
                              #:idTC (tag-maker "id")
                              #:bplusTC (tag-maker "bplus"))))
  
  (test-equal? "+ is reserved ONLY if a plus operator is defined"
               (generic-parse '+
                      #:idTC (tag-maker "id"))
               '("id" +))
  
  (test-equal? "Basic binary multiplication parsing"
               (generic-parse '(* 2 3)
                      #:numTC (tag-maker "num")
                      #:bmultTC (tag-maker "bmult"))
               '("bmult" ("num" 2) ("num" 3)))
  
  (test-exn "Error on binary multiplication if no bmult parsing" 
            truef
            (lambda () (generic-parse '(* 2 3) #:numTC (tag-maker "num"))))
  
  (test-exn "* is reserved if a mult operator is defined"
            truef
            (lambda () (generic-parse '* 
                              #:idTC (tag-maker "id")
                              #:bmultTC (tag-maker "bmult"))))
  
  (test-equal? "* is reserved ONLY if a mult operator is defined"
               (generic-parse '*
                      #:idTC (tag-maker "id"))
               '("id" *))
  

  (test-exn "Error on binary multiplication with zero args"
            truef
            (lambda () (generic-parse '(*)
                              #:idTC (tag-maker "id")
                              #:bmultTC (tag-maker "bmult"))))
  
  (test-exn "Error on binary multiplication with one arg"
            truef
            (lambda () (generic-parse '(* x)
                              #:idTC (tag-maker "id")
                              #:bmultTC (tag-maker "bmult"))))
  
  (test-exn "Error on binary multiplication with three args"
            truef
            (lambda () (generic-parse '(* x y z)
                              #:idTC (tag-maker "id")
                              #:bmultTC (tag-maker "bmult"))))
  
  (test-equal? "Basic unary negation parsing"
               (generic-parse '(- 5)
                      #:numTC (tag-maker "num")
                      #:uminusTC (tag-maker "uminus"))
               '("uminus" ("num" 5)))

  (test-exn "Error on unary subtraction if no uminus parsing" 
            truef
            (lambda () (generic-parse '(- 2) #:numTC (tag-maker "num"))))
  
  (test-exn "- is reserved if unary minus operator is defined"
            truef
            (lambda () (generic-parse '- 
                              #:idTC (tag-maker "id")
                              #:uminusTC (tag-maker "uminus"))))
  
  (test-exn "- is reserved if multiple minus operators are defined"
            truef
            (lambda () (generic-parse '- 
                              #:idTC (tag-maker "id")
                              #:uminusTC (tag-maker "uminus")
                              #:bminusTC (tag-maker "bminus"))))
  
  (test-exn "Error on unary subtraction with zero args"
            truef
            (lambda () (generic-parse '(-)
                              #:idTC (tag-maker "id")
                              #:uminusTC (tag-maker "uminus"))))
  
  (test-exn "Error on unary subtraction with two args"
            truef
            (lambda () (generic-parse '(- x y)
                              #:idTC (tag-maker "id")
                              #:uminusTC (tag-maker "uminus"))))
  
  (test-equal? "Unary subtraction works with both unary and binary subtraction defined"
               (generic-parse '(- x)
                      #:idTC (tag-maker "id")
                      #:uminusTC (tag-maker "uminus")
                      #:bminusTC (tag-maker "bminus"))
               '("uminus" ("id" x)))
  
  (test-equal? "Binary subtraction works with both unary and binary subtraction defined"
               (generic-parse '(- x y)
                      #:idTC (tag-maker "id")
                      #:uminusTC (tag-maker "uminus")
                      #:bminusTC (tag-maker "bminus"))
               '("bminus" ("id" x) ("id" y)))

  (test-equal? "Basic binary subtraction parsing"
               (generic-parse '(- 2 3)
                      #:numTC (tag-maker "num")
                      #:bminusTC (tag-maker "bminus"))
               '("bminus" ("num" 2) ("num" 3)))
  
  (test-exn "Error on binary subtraction if no bminus parsing" 
            truef
            (lambda () (generic-parse '(- 2 3) #:numTC (tag-maker "num"))))
  
  (test-exn "- is reserved if a minus operator is defined"
            truef
            (lambda () (generic-parse '- 
                              #:idTC (tag-maker "id")
                              #:bminusTC (tag-maker "bminus"))))
  
  (test-equal? "- is reserved ONLY if a minus operator is defined"
               (generic-parse '-
                      #:idTC (tag-maker "id"))
               '("id" -))
  
  (test-exn "Error on binary subtraction with zero args"
            truef
            (lambda () (generic-parse '(-)
                              #:idTC (tag-maker "id")
                              #:bminusTC (tag-maker "bminus"))))
  
  (test-exn "Error on binary subtraction with one arg"
            truef
            (lambda () (generic-parse '(- x)
                              #:idTC (tag-maker "id")
                              #:bminusTC (tag-maker "bminus"))))
  
  (test-exn "Error on binary subtraction with three args"
            truef
            (lambda () (generic-parse '(- x y z)
                              #:idTC (tag-maker "id")
                              #:bminusTC (tag-maker "bminus"))))
  

  (test-exn "Error on any app if no app defined" 
            truef
            (lambda () (generic-parse '(f x) #:idTC (tag-maker "id"))))
  
  (test-exn "Error on zero-arg 'full' app"
            truef
            (lambda () (generic-parse '(f) 
                              #:idTC (tag-maker "id")
                              #:bexprAppTC (tag-maker "app"))))
  
  (test-exn "Error on two-arg 'full' app"  ; cannot test EVERY number; this will have to do.
            truef
            (lambda () (generic-parse '(f x y) 
                              #:idTC (tag-maker "id")
                              #:bexprAppTC (tag-maker "app"))))
  
  (test-equal? "id-only app works if 'full' app defined"
               (generic-parse '(f x)
                      #:idTC (tag-maker "id")
                      #:bexprAppTC (tag-maker "app"))
               '("app" ("id" f) ("id" x)))
  
  (test-equal? "exp app works if 'full' app defined"
               (generic-parse '((f x) y)
                      #:idTC (tag-maker "id")
                      #:bexprAppTC (tag-maker "app"))
               '("app" ("app" ("id" f) ("id" x)) ("id" y)))

  (test-exn "Error on 'full' app if no 'full' app defined"  
            truef
            (lambda () (generic-parse '((f x) y) #:idTC (tag-maker "id") #:bappTC (tag-maker "app"))))

  (test-case "Named app arity tests"
             (check-exn truef (lambda () (generic-parse '(f) #:idTC (tag-maker "id") #:bAppTC (tag-maker "app"))))
             (check-exn truef (lambda () (generic-parse '(f x y) #:idTC (tag-maker "id") #:bAppTC (tag-maker "app")))))
  
  (test-equal? "id-only app works if named app defined"
               (generic-parse '(f x)
                      #:idTC (tag-maker "id")
                      #:bAppTC (tag-maker "app"))
               '("app" f ("id" x)))
  
  (test-exn "exp app does not work if (only) named app defined"
            truef
            (lambda () (generic-parse '((f x) y)
                              #:idTC (tag-maker "id")
                              #:bAppTC (tag-maker "app"))))

  (test-equal? "Basic ID check"
               (generic-parse 'x
                      #:idTC (tag-maker "id"))
               '("id" x))
  
  (test-equal? "Basic lambda check"
               (generic-parse '(lambda (x) y)
                      #:lamTC (tag-maker "lambda")
                      #:idTC (tag-maker "id"))
               '("lambda" x ("id" y)))

  (test-exn "Error on lambda with reserved word arg"
            truef
            (lambda () (generic-parse '(lambda (lambda) y)
                              #:lamTC (tag-maker "lambda")
                              #:idTC (tag-maker "id"))))
              
  (test-exn "Error on lambda with numeric arg"
            truef
            (lambda () (generic-parse '(lambda (5) y)
                              #:numTC (tag-maker "num")    ; not necessary, but makes me feel better
                              #:lamTC (tag-maker "lambda")
                              #:idTC (tag-maker "id"))))
              

  (test-exn "Error on lambda with no args"
            truef
            (lambda () (generic-parse '(lambda () y)
                              #:lamTC (tag-maker "lambda")
                              #:idTC (tag-maker "id"))))
              
  (test-exn "Error on lambda with unparenthesized args"
            truef
            (lambda () (generic-parse '(lambda x y)
                              #:lamTC (tag-maker "lambda")
                              #:idTC (tag-maker "id"))))
              
  (test-exn "Error on lambda with missing args"
            truef
            (lambda () (generic-parse '(lambda y)
                              #:lamTC (tag-maker "lambda")
                              #:idTC (tag-maker "id"))))
              
  (test-exn "Error on lambda with two args"
            truef
            (lambda () (generic-parse '(lambda (x y) z)
                              #:lamTC (tag-maker "lambda")
                              #:idTC (tag-maker "id"))))

  (test-exn "Error on lambda with no body"
            truef
            (lambda () (generic-parse '(lambda (x))
                              #:lamTC (tag-maker "lambda")
                              #:idTC (tag-maker "id"))))

  (test-exn "Error on lambda with two bodies"
            truef
            (lambda () (generic-parse '(lambda (x) y z)
                              #:lamTC (tag-maker "lambda")
                              #:idTC (tag-maker "id"))))

  (test-exn "Error on 'bare' lambda"
            truef
            (lambda () (generic-parse '(lambda)
                              #:lamTC (tag-maker "lambda")
                              #:idTC (tag-maker "id"))))

  (test-exn "lambda is reserved if the lambda form is defined"
            truef
            (lambda () (generic-parse 'lambda 
                              #:lamTC (tag-maker "lambda")
                              #:idTC (tag-maker "id"))))
  
  (test-equal? "lambda is reserved ONLY if the lambda form is defined"
               (generic-parse 'lambda
                      #:idTC (tag-maker "id"))
               '("id" lambda))
  

  (test-case "Basic fd checks"
             (check-equal? (generic-parse '(define (f x) y)
                                  #:fdTC (tag-maker "define")
                                  #:idTC (tag-maker "id"))
                           '("define" f x ("id" y)))
             (check-exn truef (lambda () (generic-parse '(define (f x) y)
                                                #:idTC (tag-maker "id")))))

  (test-case "fd fun/param must be valid IDs"
             (check-exn truef (lambda () (generic-parse '(define (define x) y)
                                                #:fdTC (tag-maker "define")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(define (f define) y)
                                                #:fdTC (tag-maker "define")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(define (5 x) y)
                                                #:fdTC (tag-maker "define")
                                                #:numTC (tag-maker "num")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(define (f 5) y)
                                                #:fdTC (tag-maker "define")
                                                #:numTC (tag-maker "num")
                                                #:idTC (tag-maker "id")))))

  (test-case "fd arity checks (lots of them to test various arities and listinesses)"
             (check-exn truef (lambda () (generic-parse '(define () y)
                                                #:fdTC (tag-maker "define")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(define x y)
                                                #:fdTC (tag-maker "define")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(define x)
                                                #:fdTC (tag-maker "define")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(define)
                                                #:fdTC (tag-maker "define")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(define (x y z) w)
                                                #:fdTC (tag-maker "define")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(define (x) w)
                                                #:fdTC (tag-maker "define")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(define (x y) w z)
                                                #:fdTC (tag-maker "define")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(define (x y))
                                                #:fdTC (tag-maker "define")
                                                #:idTC (tag-maker "id")))))

  (test-case "define is reserved if and only if the fd form is defined"
             (check-exn truef (lambda () (generic-parse 'define 
                                                #:fdTC (tag-maker "define")
                                                #:idTC (tag-maker "id"))))
             (check-equal? (generic-parse 'define #:idTC (tag-maker "id")) '("id" define)))
  

  
  (test-equal? "Basic let check"
               (generic-parse '(let (x z) y)
                      #:uletTC (tag-maker "let")
                      #:idTC (tag-maker "id"))
               '("let" x ("id" z) ("id" y)))

  (test-exn "Error on let with reserved word arg"
            truef
            (lambda () (generic-parse '(let (let z) y)
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))
              
  (test-exn "Error on let with numeric arg"
            truef
            (lambda () (generic-parse '(let (5 z) y)
                              #:numTC (tag-maker "num")    ; not necessary, but makes me feel better
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))
              

  (test-exn "Error on let with no args"
            truef
            (lambda () (generic-parse '(let () y)
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))
              
  (test-exn "Error on let with unparenthesized args"
            truef
            (lambda () (generic-parse '(let x y z)
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))
              
  (test-exn "Error on let with unparenthesized args and only the name"
            truef
            (lambda () (generic-parse '(let x y)
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))
              
  (test-exn "Error on let with missing args"
            truef
            (lambda () (generic-parse '(let y)
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))
              
  (test-exn "Error on let with extra bound expression"
            truef
            (lambda () (generic-parse '(let (x y z) z)
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))

  (test-exn "Error on let with no bound expression"
            truef
            (lambda () (generic-parse '(let (x) z)
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))

  (test-exn "Error on nested-style let"
            truef
            (lambda () (generic-parse '(let ((x y)) z)
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))

  (test-exn "Error on let with no body"
            truef
            (lambda () (generic-parse '(let (x y))
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))

  (test-exn "Error on let with two bodies"
            truef
            (lambda () (generic-parse '(let (x y) w z)
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))

  (test-exn "Error on 'bare' let"
            truef
            (lambda () (generic-parse '(let)
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))

  (test-exn "let is reserved if the let form is defined"
            truef
            (lambda () (generic-parse 'let 
                              #:uletTC (tag-maker "let")
                              #:idTC (tag-maker "id"))))
  
  (test-equal? "let is reserved ONLY if the let form is defined"
               (generic-parse 'let
                      #:idTC (tag-maker "id"))
               '("id" let))
  

  
  (test-case "Basic let (arbitrary size) checks"
             (check-equal? (generic-parse '(let () z)
                                          #:arbletTC (tag-maker "let")
                                          #:idTC (tag-maker "id"))
               '("let" () () ("id" z)))

             (check-equal? (generic-parse '(let ((x1 y1)) z)
                                          #:arbletTC (tag-maker "let")
                                          #:idTC (tag-maker "id"))
               '("let" (x1) (("id" y1)) ("id" z)))

             (check-equal? (generic-parse '(let ((x1 y1) (x2 y2)) z)
                                          #:arbletTC (tag-maker "let")
                                          #:idTC (tag-maker "id"))
               '("let" (x1 x2) (("id" y1) ("id" y2)) ("id" z)))
             
             (check-exn truef (lambda () (generic-parse '(let () z)
                                                        #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(let ((x1 y1)) z)
                                                        #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(let ((x1 y1) (x2 y2)) z)
                                                        #:idTC (tag-maker "id")))))

  (test-case "Let-bound identifiers must be valid."
            (check-exn truef
                       (lambda () (generic-parse '(let ((let z)) y)
                                                 #:arbletTC (tag-maker "let")
                                                 #:idTC (tag-maker "id"))))
            (check-exn truef
                       (lambda () (generic-parse '(let ((5 z)) y)
                                                 #:arbletTC (tag-maker "let")
                                                 #:numTC (tag-maker "num")
                                                 #:idTC (tag-maker "id"))))
            (check-exn truef
                       (lambda () (generic-parse '(let ((a b) (let z) (c d)) y)
                                                 #:arbletTC (tag-maker "let")
                                                 #:idTC (tag-maker "id"))))
            (check-exn truef
                       (lambda () (generic-parse '(let ((a b) (5 z) (c d)) y)
                                                 #:arbletTC (tag-maker "let")
                                                 #:numTC (tag-maker "num")
                                                 #:idTC (tag-maker "id")))))

  (test-case "Let structural form checks."
             (check-exn truef
                        (lambda () (generic-parse '(let)
                                                  #:arbletTC (tag-maker "let")
                                                  #:idTC (tag-maker "id"))))
              
             (check-exn truef
                        (lambda () (generic-parse '(let x)
                                                  #:arbletTC (tag-maker "let")
                                                  #:idTC (tag-maker "id"))))
              
             (check-exn truef
                        (lambda () (generic-parse '(let x y)
                                                  #:arbletTC (tag-maker "let")
                                                  #:idTC (tag-maker "id"))))
              
             (check-exn truef
                        (lambda () (generic-parse '(let ())
                                                  #:arbletTC (tag-maker "let")
                                                  #:idTC (tag-maker "id"))))
              
             (check-exn truef
                        (lambda () (generic-parse '(let () x y)
                                                  #:arbletTC (tag-maker "let")
                                                  #:idTC (tag-maker "id"))))
              
             (check-exn truef
                        (lambda () (generic-parse '(let (x) z)
                                                  #:arbletTC (tag-maker "let")
                                                  #:idTC (tag-maker "id"))))
              
             (check-exn truef
                        (lambda () (generic-parse '(let ((x)) z)
                                                  #:arbletTC (tag-maker "let")
                                                  #:idTC (tag-maker "id"))))
              
             (check-exn truef
                        (lambda () (generic-parse '(let ((x y z)) z)
                                                  #:arbletTC (tag-maker "let")
                                                  #:idTC (tag-maker "id"))))
              
             (check-exn truef
                        (lambda () (generic-parse '(let (((x y))) z)
                                                  #:arbletTC (tag-maker "let")
                                                  #:idTC (tag-maker "id")))))

  (test-case "Let reserved word status."
             (check-exn truef
                        (lambda () (generic-parse 'let 
                                                  #:arbletTC (tag-maker "let")
                                                  #:idTC (tag-maker "id"))))
             
             (check-equal? (generic-parse 'let #:idTC (tag-maker "id")) '("id" let)))
  

  
  (test-case "Basic n-ary begin parsing"
	     (check-equal? (generic-parse '(begin x)
				  #:idTC (tag-maker "id")
				  #:arbbeginTC (tag-maker "arbbegin"))
			   '("arbbegin" () ("id" x)))
	     (check-equal? (generic-parse '(begin x y)
				  #:idTC (tag-maker "id")
				  #:arbbeginTC (tag-maker "arbbegin"))
			   '("arbbegin" (("id" x)) ("id" y)))
	     (check-equal? (generic-parse '(begin x y z)
				  #:idTC (tag-maker "id")
				  #:arbbeginTC (tag-maker "arbbegin"))
			   '("arbbegin" (("id" x) ("id" y)) ("id" z)))

	     (check-exn truef (lambda () (generic-parse '(begin x)
						#:idTC (tag-maker "id"))))
	     (check-exn truef (lambda () (generic-parse '(begin x y)
						#:idTC (tag-maker "id"))))
	     (check-exn truef (lambda () (generic-parse '(begin x y z)
						#:idTC (tag-maker "id")))))

  (test-case "'begin' is reserved if and only if begin syntax is defined (arbitrary, this time)"
             (check-equal? (generic-parse 'begin #:idTC (tag-maker "id")) '("id" begin))
             (check-exn truef (lambda () (generic-parse 'begin #:idTC (tag-maker "id") #:arbbeginTC (tag-maker "arbbegin")))))

  (test-case "Arity for arbitrary (n-ary) begin expressions"
             (check-exn truef (lambda () (generic-parse '(begin) #:idTC (tag-maker "id") #:arbbeginTC (tag-maker "arbbegin")))))

  ;; TODO: copy set tests to letcc tests.
  (test-case "Basic set checks"
             (check-equal? (generic-parse '(set! x y)
                                  #:setTC (tag-maker "set")
                                  #:idTC (tag-maker "id"))
                           '("set" x ("id" y)))
             (check-exn truef (lambda () (generic-parse '(set! x y)
                                                #:idTC (tag-maker "id")))))

  (test-case "set var must be valid ID"
             (check-exn truef (lambda () (generic-parse '(set! set! y)
                                                #:setTC (tag-maker "set!")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(set! 5 y)
                                                #:setTC (tag-maker "set!")
                                                #:numTC (tag-maker "num")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(set! (f x) y)
                                                #:setTC (tag-maker "set!")
						#:bexprAppTC (tag-maker "app")
                                                #:numTC (tag-maker "num")
                                                #:idTC (tag-maker "id")))))

  (test-case "set arity checks"
             (check-exn truef (lambda () (generic-parse '(set!)
                                                #:setTC (tag-maker "set!")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(set! x)
                                                #:setTC (tag-maker "set!")
                                                #:idTC (tag-maker "id"))))
             (check-exn truef (lambda () (generic-parse '(set! x y z)
                                                #:setTC (tag-maker "set!")
                                                #:idTC (tag-maker "id")))))

  (test-case "set! is reserved if and only if the set form is defined"
             (check-exn truef (lambda () (generic-parse 'set! 
                                                #:setTC (tag-maker "set!")
                                                #:idTC (tag-maker "id"))))
             (check-equal? (generic-parse 'set! #:idTC (tag-maker "id")) '("id" set!)))



  (test-case "All discard tests (simple 0-ary operator)"
	     (check-equal? (generic-parse '(discard!) #:discardTC (tag-maker "discard"))
			   '("discard"))
	     (check-exn truef (lambda () (generic-parse '(discard!) #:idTC (tag-maker "id"))))
	     (check-exn truef (lambda () (generic-parse '(discard! x) #:discardTC (tag-maker "discard") #:idTC (tag-maker "id"))))
             (check-equal? (generic-parse 'discard! #:idTC (tag-maker "id")) '("id" discard!))
             (check-exn truef (lambda () (generic-parse 'discard! #:idTC (tag-maker "id") #:discardTC (tag-maker "discard")))))

  (test-case "All commit tests (simple 0-ary operator)"
	     (check-equal? (generic-parse '(commit!!) #:commitTC (tag-maker "commit"))
			   '("commit"))
	     (check-exn truef (lambda () (generic-parse '(commit!!) #:idTC (tag-maker "id"))))
	     (check-exn truef (lambda () (generic-parse '(commit!! x) #:commitTC (tag-maker "commit") #:idTC (tag-maker "id"))))
             (check-equal? (generic-parse 'commit!! #:idTC (tag-maker "id")) '("id" commit!!))
             (check-exn truef (lambda () (generic-parse 'commit!! #:idTC (tag-maker "id") #:commitTC (tag-maker "commit")))))

  ;;;;;;;; Some unary operator tests ;;;;;;;;;;;
  (test-case "Basic box parsing"
             (check-equal? (generic-parse '(box x)
                                  #:idTC (tag-maker "id")
                                  #:boxTC (tag-maker "box"))
                           '("box" ("id" x)))
             (check-exn truef
                        (lambda () (generic-parse '(box x)
                                          #:idTC (tag-maker "id")))))
  
  (test-case "'box' is reserved if and only if box syntax is defined"
             (check-exn truef (lambda () (generic-parse 'box 
                                                #:idTC (tag-maker "id")
                                                #:boxTC (tag-maker "box"))))
             (check-equal? (generic-parse 'box #:idTC (tag-maker "id")) '("id" box)))

  (test-case "box creation arity tests"
             (check-exn truef (lambda () (generic-parse '(box) #:idTC (tag-maker "id") #:boxTC (tag-maker "box"))))
             (check-exn truef (lambda () (generic-parse '(box x y) #:idTC (tag-maker "id") #:boxTC (tag-maker "box")))))
  


  (test-case "Basic unbox parsing"
             (check-equal? (generic-parse '(unbox x)
                                  #:idTC (tag-maker "id")
                                  #:unboxTC (tag-maker "unbox"))
                           '("unbox" ("id" x)))
             (check-exn truef
                        (lambda () (generic-parse '(unbox x)
                                          #:idTC (tag-maker "id")))))
  
  (test-case "'unbox' is reserved if and only if unbox syntax is defined"
             (check-exn truef (lambda () (generic-parse 'unbox 
                                                #:idTC (tag-maker "id")
                                                #:unboxTC (tag-maker "unbox"))))
             (check-equal? (generic-parse 'unbox #:idTC (tag-maker "id")) '("id" unbox)))

  (test-case "logical negation arity tests"
             (check-exn truef (lambda () (generic-parse '(unbox) #:idTC (tag-maker "id") #:unboxTC (tag-maker "unbox"))))
             (check-exn truef (lambda () (generic-parse '(unbox x y) #:idTC (tag-maker "id") #:unboxTC (tag-maker "unbox")))))




  (test-case "Basic not parsing"
             (check-equal? (generic-parse '(not x)
                                  #:idTC (tag-maker "id")
                                  #:notTC (tag-maker "not"))
                           '("not" ("id" x)))
             (check-exn truef
                        (lambda () (generic-parse '(not x)
                                          #:idTC (tag-maker "id")))))
  
  (test-case "'not' is reserved if and only if not syntax is defined"
             (check-exn truef (lambda () (generic-parse 'not 
                                                #:idTC (tag-maker "id")
                                                #:notTC (tag-maker "not"))))
             (check-equal? (generic-parse 'not #:idTC (tag-maker "id")) '("id" not)))

  (test-case "logical negation arity tests"
             (check-exn truef (lambda () (generic-parse '(not) #:idTC (tag-maker "id") #:notTC (tag-maker "not"))))
             (check-exn truef (lambda () (generic-parse '(not x y) #:idTC (tag-maker "id") #:notTC (tag-maker "not")))))
  
  ;;;;;;;; Scads of binary operator tests. ;;;;;;;;
  (test-case "Basic binary begin parsing"
	     (check-equal? (generic-parse '(begin x y)
				  #:idTC (tag-maker "id")
				  #:bbeginTC (tag-maker "bbegin"))
			   '("bbegin" ("id" x) ("id" y)))
	     (check-exn truef (lambda () (generic-parse '(begin x y) #:idTC (tag-maker "id")))))

  (test-case "'begin' is reserved if and only if begin syntax is defined (binary, this time)"
             (check-equal? (generic-parse 'begin #:idTC (tag-maker "id")) '("id" begin))
             (check-exn truef (lambda () (generic-parse 'begin #:idTC (tag-maker "id") #:bbeginTC (tag-maker "bbegin")))))

  (test-case "Arity for begin expressions"
             (check-exn truef (lambda () (generic-parse '(begin) #:idTC (tag-maker "id") #:bbeginTC (tag-maker "bbegin"))))
             (check-exn truef (lambda () (generic-parse '(begin x) #:idTC (tag-maker "id") #:bbeginTC (tag-maker "bbegin"))))
             (check-exn truef (lambda () (generic-parse '(begin x y z) #:idTC (tag-maker "id") #:bbeginTC (tag-maker "bbegin")))))



  (test-case "Basic binary set-box parsing"
	     (check-equal? (generic-parse '(set-box! x y)
				  #:idTC (tag-maker "id")
				  #:setboxTC (tag-maker "setbox"))
			   '("setbox" ("id" x) ("id" y)))
	     (check-exn truef (lambda () (generic-parse '(set-box! x y) #:idTC (tag-maker "id")))))

  (test-case "'set-box!' is reserved if and only if set-box syntax is defined"
             (check-equal? (generic-parse 'set-box! #:idTC (tag-maker "id")) '("id" set-box!))
             (check-exn truef (lambda () (generic-parse 'set-box! #:idTC (tag-maker "id") #:setboxTC (tag-maker "setbox")))))

  (test-case "Arity for set-box expressions"
             (check-exn truef (lambda () (generic-parse '(set-box!) #:idTC (tag-maker "id") #:setboxTC (tag-maker "setbox"))))
             (check-exn truef (lambda () (generic-parse '(set-box! x) #:idTC (tag-maker "id") #:setboxTC (tag-maker "setbox"))))
             (check-exn truef (lambda () (generic-parse '(set-box! x y z) #:idTC (tag-maker "id") #:setboxTC (tag-maker "setbox")))))




  (test-case "Basic binary less-than-or-equal parsing"
	     (check-equal? (generic-parse '(<= x y)
				  #:idTC (tag-maker "id")
				  #:leqTC (tag-maker "leq"))
			   '("leq" ("id" x) ("id" y)))
	     (check-exn truef (lambda () (generic-parse '(<= x y) #:idTC (tag-maker "id")))))

  (test-case "'<=' is reserved if and only if less-than-or-equal syntax is defined"
             (check-equal? (generic-parse '<= #:idTC (tag-maker "id")) '("id" <=))
             (check-exn truef (lambda () (generic-parse '<= #:idTC (tag-maker "id") #:leqTC (tag-maker "leq")))))

  (test-case "Arity for less-than-or-equal expressions"
             (check-exn truef (lambda () (generic-parse '(<=) #:idTC (tag-maker "id") #:leqTC (tag-maker "leq"))))
             (check-exn truef (lambda () (generic-parse '(<= x) #:idTC (tag-maker "id") #:leqTC (tag-maker "leq"))))
             (check-exn truef (lambda () (generic-parse '(<= x y z) #:idTC (tag-maker "id") #:leqTC (tag-maker "leq")))))


  (test-case "Basic binary less-than parsing"
	     (check-equal? (generic-parse '(< x y)
				  #:idTC (tag-maker "id")
				  #:ltTC (tag-maker "lt"))
			   '("lt" ("id" x) ("id" y)))
	     (check-exn truef (lambda () (generic-parse '(< x y) #:idTC (tag-maker "id")))))

  (test-case "'<' is reserved if and only if less-than syntax is defined"
             (check-equal? (generic-parse '< #:idTC (tag-maker "id")) '("id" <))
             (check-exn truef (lambda () (generic-parse '< #:idTC (tag-maker "id") #:ltTC (tag-maker "lt")))))

  (test-case "Arity for less-than expressions"
             (check-exn truef (lambda () (generic-parse '(<) #:idTC (tag-maker "id") #:ltTC (tag-maker "lt"))))
             (check-exn truef (lambda () (generic-parse '(< x) #:idTC (tag-maker "id") #:ltTC (tag-maker "lt"))))
             (check-exn truef (lambda () (generic-parse '(< x y z) #:idTC (tag-maker "id") #:ltTC (tag-maker "lt")))))


  (test-case "Basic binary greater-than-or-equal parsing"
	     (check-equal? (generic-parse '(>= x y)
				  #:idTC (tag-maker "id")
				  #:geqTC (tag-maker "geq"))
			   '("geq" ("id" x) ("id" y)))
	     (check-exn truef (lambda () (generic-parse '(>= x y) #:idTC (tag-maker "id")))))

  (test-case "'>=' is reserved if and only if greater-than-or-equal syntax is defined"
             (check-equal? (generic-parse '>= #:idTC (tag-maker "id")) '("id" >=))
             (check-exn truef (lambda () (generic-parse '>= #:idTC (tag-maker "id") #:geqTC (tag-maker "geq")))))

  (test-case "Arity for greater-than-or-equal expressions"
             (check-exn truef (lambda () (generic-parse '(>=) #:idTC (tag-maker "id") #:geqTC (tag-maker "geq"))))
             (check-exn truef (lambda () (generic-parse '(>= x) #:idTC (tag-maker "id") #:geqTC (tag-maker "geq"))))
             (check-exn truef (lambda () (generic-parse '(>= x y z) #:idTC (tag-maker "id") #:geqTC (tag-maker "geq")))))


  (test-case "Basic binary greater-than parsing"
	     (check-equal? (generic-parse '(> x y)
				  #:idTC (tag-maker "id")
				  #:gtTC (tag-maker "gt"))
			   '("gt" ("id" x) ("id" y)))
	     (check-exn truef (lambda () (generic-parse '(> x y) #:idTC (tag-maker "id")))))

  (test-case "'>' is reserved if and only if greater-than syntax is defined"
             (check-equal? (generic-parse '> #:idTC (tag-maker "id")) '("id" >))
             (check-exn truef (lambda () (generic-parse '> #:idTC (tag-maker "id") #:gtTC (tag-maker "gt")))))

  (test-case "Arity for greater-than expressions"
             (check-exn truef (lambda () (generic-parse '(>) #:idTC (tag-maker "id") #:gtTC (tag-maker "gt"))))
             (check-exn truef (lambda () (generic-parse '(> x) #:idTC (tag-maker "id") #:gtTC (tag-maker "gt"))))
             (check-exn truef (lambda () (generic-parse '(> x y z) #:idTC (tag-maker "id") #:gtTC (tag-maker "gt")))))


  (test-case "Basic binary equal parsing"
	     (check-equal? (generic-parse '(= x y)
				  #:idTC (tag-maker "id")
				  #:eqTC (tag-maker "eq"))
			   '("eq" ("id" x) ("id" y)))
	     (check-exn truef (lambda () (generic-parse '(= x y) #:idTC (tag-maker "id")))))

  (test-case "'=' is reserved if and only if equal syntax is defined"
             (check-equal? (generic-parse '= #:idTC (tag-maker "id")) '("id" =))
             (check-exn truef (lambda () (generic-parse '= #:idTC (tag-maker "id") #:eqTC (tag-maker "eq")))))

  (test-case "Arity for equal expressions"
             (check-exn truef (lambda () (generic-parse '(=) #:idTC (tag-maker "id") #:eqTC (tag-maker "eq"))))
             (check-exn truef (lambda () (generic-parse '(= x) #:idTC (tag-maker "id") #:eqTC (tag-maker "eq"))))
             (check-exn truef (lambda () (generic-parse '(= x y z) #:idTC (tag-maker "id") #:eqTC (tag-maker "eq")))))


  (test-case "Basic binary not-equal parsing"
	     (check-equal? (generic-parse '(!= x y)
				  #:idTC (tag-maker "id")
				  #:neqTC (tag-maker "neq"))
			   '("neq" ("id" x) ("id" y)))
	     (check-exn truef (lambda () (generic-parse '(!= x y) #:idTC (tag-maker "id")))))

  (test-case "'!=' is reserved if and only if not-equal syntax is defined"
             (check-equal? (generic-parse '!= #:idTC (tag-maker "id")) '("id" !=))
             (check-exn truef (lambda () (generic-parse '!= #:idTC (tag-maker "id") #:neqTC (tag-maker "neq")))))

  (test-case "Arity for not-equal expressions"
             (check-exn truef (lambda () (generic-parse '(!=) #:idTC (tag-maker "id") #:neqTC (tag-maker "neq"))))
             (check-exn truef (lambda () (generic-parse '(!= x) #:idTC (tag-maker "id") #:neqTC (tag-maker "neq"))))
             (check-exn truef (lambda () (generic-parse '(!= x y z) #:idTC (tag-maker "id") #:neqTC (tag-maker "neq")))))


  (test-case "Basic binary binary logical and parsing"
	     (check-equal? (generic-parse '(and x y)
				  #:idTC (tag-maker "id")
				  #:bandTC (tag-maker "band"))
			   '("band" ("id" x) ("id" y)))
	     (check-exn truef (lambda () (generic-parse '(and x y) #:idTC (tag-maker "id")))))

  (test-case "'and' is reserved if and only if binary logical and syntax is defined"
             (check-equal? (generic-parse 'and #:idTC (tag-maker "id")) '("id" and))
             (check-exn truef (lambda () (generic-parse 'and #:idTC (tag-maker "id") #:bandTC (tag-maker "band")))))

  (test-case "Arity for binary logical and expressions"
             (check-exn truef (lambda () (generic-parse '(and) #:idTC (tag-maker "id") #:bandTC (tag-maker "band"))))
             (check-exn truef (lambda () (generic-parse '(and x) #:idTC (tag-maker "id") #:bandTC (tag-maker "band"))))
             (check-exn truef (lambda () (generic-parse '(and x y z) #:idTC (tag-maker "id") #:bandTC (tag-maker "band")))))


  (test-case "Basic binary binary logical or parsing"
	     (check-equal? (generic-parse '(or x y)
				  #:idTC (tag-maker "id")
				  #:borTC (tag-maker "bor"))
			   '("bor" ("id" x) ("id" y)))
	     (check-exn truef (lambda () (generic-parse '(or x y) #:idTC (tag-maker "id")))))

  (test-case "'or' is reserved if and only if binary logical or syntax is defined"
             (check-equal? (generic-parse 'or #:idTC (tag-maker "id")) '("id" or))
             (check-exn truef (lambda () (generic-parse 'or #:idTC (tag-maker "id") #:borTC (tag-maker "bor")))))

  (test-case "Arity for binary logical or expressions"
             (check-exn truef (lambda () (generic-parse '(or) #:idTC (tag-maker "id") #:borTC (tag-maker "bor"))))
             (check-exn truef (lambda () (generic-parse '(or x) #:idTC (tag-maker "id") #:borTC (tag-maker "bor"))))
             (check-exn truef (lambda () (generic-parse '(or x y z) #:idTC (tag-maker "id") #:borTC (tag-maker "bor")))))

  (test-case "Assorted tests that have failed during development."
             (check-equal? (generic-parse '(begin 1)
                                          #:numTC (tag-maker "num")
                                          #:bexprAppTC (tag-maker "app")
                                          #:arbbeginTC (tag-maker "begin"))
                           '("begin" () ("num" 1))))
  
  (test-case "'<=' is reserved if and only if less-than-or-equal syntax is defined"
             (check-equal? (generic-parse '<= #:idTC (tag-maker "id")) '("id" <=))
             (check-exn truef (lambda () (generic-parse '<= #:idTC (tag-maker "id") #:leqTC (tag-maker "leq")))))

  (test-case "Arity for less-than-or-equal expressions"
             (check-exn truef (lambda () (generic-parse '(<=) #:idTC (tag-maker "id") #:leqTC (tag-maker "leq"))))
             (check-exn truef (lambda () (generic-parse '(<= x) #:idTC (tag-maker "id") #:leqTC (tag-maker "leq"))))
             (check-exn truef (lambda () (generic-parse '(<= x y z) #:idTC (tag-maker "id") #:leqTC (tag-maker "leq")))))

  )
