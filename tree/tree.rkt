#lang plai-typed

; Creating a static analysis to produce the AST as a GV graph and a
; dynamic analysis to produce the call tree as a GV graph.
;
; To use, you might run:
;
; (display (parse-to-gv '(let (x 2) (+ x x))))
;
; This will output code appropriate to run through GraphViz.
; You could then produce a png file by pasting this into, e.g.,
; ast.gv and running:
;
;   dot ast.gv | neato -n -Tpng -o ast.png
;
; Similarly, produce the function call graph with:
;
; (display (run-to-gv '(let (x 2) (+ x x))))
;
; (Of course, this program doesn't have a very interesting 
; function call graph!  It looks pretty much just like the AST.)



(require "utils.rkt")


(define MAX-PROP-NAME-LENGTH 10)
(define PROP-NAME-PADDING "...")

(require (typed-in racket 
                   [string-length : (string -> number)]
                   [substring : (string number number -> string)]))

(module+ test
  (print-only-errors true))

(define-type Value
  [numV (n : number)]
  [strV (s : string)]
  [closV (arg : symbol) (body : ExprC) (env : Env)])  

; ExprS ST: arithmetic w/functions anywhere
(define-type ExprS
  [numS (n : number)]
  [strS (s : string)]
  [plusS (l : ExprS) (r : ExprS)]
  [seqS (exp1 : ExprS) (exp2 : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [appS (f : ExprS) (a : ExprS)]
  [idS (i : symbol)]
  [lamS (id : symbol) (body : ExprS)]
  [letS (id : symbol) (val : ExprS) (body : ExprS)]
  [if0S (tst : ExprS) (thn : ExprS) (els : ExprS)]
  [displayS (exp : ExprS)]
  [readS]
  [letrecS (id : symbol) (val : ExprS) (body : ExprS)])  ; val must be a lamS

; ExprC AST: arithmetic w/functions anywhere
(define-type ExprC
  [lamC (arg : symbol) (body : ExprC)]  
  [letrecC (id : symbol) (val : ExprC) (body : ExprC)]  ; val must be a lamC
  [letC (id : symbol) (val : ExprC) (body : ExprC)]
  [appC (fun : ExprC) (arg : ExprC)]
  [displayC (exp : ExprC)]
  [seqC (exp1 : ExprC) (exp2 : ExprC)]
  [readC]
  [strC (s : string)]
  [numC (n : number)]
  [if0C (tst : ExprC) (then : ExprC) (else : ExprC)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [idC (i : symbol)])

; Binary operator symbol map.
(define binop-map (hash (list (values '+ plusS)
                              (values '- bminusS)
                              (values '* multS))))

(define non-binop-reserved-words (list 'if0 'let 'let-rec 'lambda 'display 'read 'seq))

; check if the identifier is disallowed as a variable or function name
(define (reserved? [s : symbol]) : boolean
  (or (member s non-binop-reserved-words)
      (some? (hash-ref binop-map s))))

(module+ test
  (test (reserved? '+) true)
  (test (reserved? '-) true)
  (test (reserved? '*) true)
  (test (reserved? 'display) true)
  (test (reserved? 'read) true)
  (test (reserved? 'seq) true)
  (test (reserved? '_) false)
  (test (reserved? 'a) false)
  (test (reserved? 'let) true))

; parse s-expressions into ExprS STs
(define (parse [s-exp : s-expression]) : ExprS
  (s-exp-type-case s-exp
                   (lambda ([selst : (listof s-expression)]) : ExprS
                     (cond 
                       [(and (= (length selst) 1)
                             (s-exp-symbol? (first selst))
                             (symbol=? (s-exp->symbol (first selst)) 'read))
                        (readS)]
                       [(and (= (length selst) 2)
                             (s-exp-symbol? (first selst))
                             (symbol=? (s-exp->symbol (first selst)) 'display))
                        (displayS (parse (second selst)))]
                       [(and (= (length selst) 3)
                             (s-exp-symbol? (first selst))
                             (symbol=? (s-exp->symbol (first selst)) 'seq))
                        (seqS (parse (second selst)) (parse (third selst)))]
                       [(and (= (length selst) 4)
                             (s-exp-symbol? (first selst))
                             (symbol=? (s-exp->symbol (first selst)) 'if0))
                        (if0S (parse (second selst))
                              (parse (third selst))
                              (parse (fourth selst)))]
                       [(and (= (length selst) 3)
                             (s-exp-symbol? (first selst))
                             (symbol=? (s-exp->symbol (first selst)) 'let)
                             (s-exp-list? (second selst)))
                        (local [(define bpair (s-exp->list (second selst)))
                                (define body (third selst))]
                          (if (and (= (length bpair) 2)
                                   (s-exp-symbol? (first bpair))
                                   (not (reserved? (s-exp->symbol (first bpair)))))
                              (letS
                               (s-exp->symbol (first bpair))
                               (parse (second bpair))
                               (parse body))
                              (error 'parse (string-append "malformed let in: " (to-string s-exp)))))]
                       [(and (= (length selst) 3)
                             (s-exp-symbol? (first selst))
                             (symbol=? (s-exp->symbol (first selst)) 'let-rec)
                             (s-exp-list? (second selst)))
                        (local [(define bpair (s-exp->list (second selst)))
                                (define body (third selst))]
                          (if (and (= (length bpair) 2)
                                   (s-exp-symbol? (first bpair))
                                   (not (reserved? (s-exp->symbol (first bpair)))))
                              (local [(define val (parse (second bpair)))]
                                (if (lamS? val)
                                    (letrecS
                                     (s-exp->symbol (first bpair))
                                     val
                                     (parse body))
                                    (error 'parse (string-append "value expression must be a syntactic lambda in: " (to-string s-exp)))))
                              (error 'parse (string-append "malformed let-rec in: " (to-string s-exp)))))]
                       [(and (= (length selst) 3)
                             (s-exp-symbol? (first selst))
                             (symbol=? (s-exp->symbol (first selst)) 'lambda)
                             (s-exp-list? (second selst))
                             (= (length (s-exp->list (second selst))) 1))
                        (local [(define sexparg (first (s-exp->list (second selst))))
                                (define body (third selst))]
                          (if (and (s-exp-symbol? sexparg)
                                   (not (reserved? (s-exp->symbol sexparg))))
                              (lamS (s-exp->symbol sexparg)
                                    (parse body))
                              (error 'parse (string-append "malformed lambda in: " (to-string s-exp)))))]
                       [(and (= (length selst) 3)
                             (s-exp-symbol? (first selst)))
                        (type-case (optionof (ExprS ExprS -> ExprS)) (hash-ref binop-map (s-exp->symbol (first selst)))
                          [none () (error 'parse (string-append "non-binary-operator symbol used as binary operator in: "
                                                                (to-string selst)))]
                          [some (opS) (opS (parse (second selst)) (parse (third selst)))])]
                       [(= (length selst) 2)
                        (appS (parse (first selst)) (parse (second selst)))]
                       [else
                        (error 'parse (string-append "malformed operator expression in: " (to-string selst)))]))
                   (lambda ([senum : number]) : ExprS (numS senum))
                   (lambda ([sesym : symbol]) : ExprS (if (reserved? sesym)
                                                          (error 'parse 
                                                                 (string-append "attempt to use reserved word as identifier in: " 
                                                                                (to-string sesym)))
                                                          (idS sesym)))
                   (lambda ([sestr : string]) : ExprS (strS sestr))))


; Test the "standard" cases:
(module+ test
  (test (parse '"hello") (strS "hello"))
  (test (parse '1) (numS 1))
  (test (parse '(+ 1 2)) (plusS (numS 1) (numS 2)))
  (test (parse '(seq 1 2)) (seqS (numS 1) (numS 2)))
  (test (parse '(* 1 2)) (multS (numS 1) (numS 2)))
  (test (parse '(- 1 2)) (bminusS (numS 1) (numS 2)))
  (test (parse '(a 1)) (appS (idS 'a) (numS 1)))
  (test (parse (symbol->s-exp 'a)) (idS 'a))
  
  ; Test one "complex" case, just to be safe.
  (test (parse '(+ (* 1 2) (- 3 4))) (plusS (multS (numS 1) (numS 2))
                                            (bminusS (numS 3) (numS 4))))
  
  (test (parse '(read)) (readS))
  (test (parse '(display 1)) (displayS (numS 1)))
  
  ; Test lambda parsing
  ;(test/exn (parse 'lambda) "")
  (test (parse '(lambda (x) x)) (lamS 'x (idS 'x)))
  (test/exn (parse '(lambda)) "")
  (test/exn (parse '(lambda (let) 1)) "")
  (test/exn (parse '(lambda (x y) 1)) "")
  (test/exn (parse '(lambda (x) 1 2)) "")
  
  ; Test let parsing
  (test (parse '(let (x 1) x)) (letS 'x (numS 1) (idS 'x)))
  (test/exn (parse '(let x 1 x)) "")
  (test/exn (parse '(let (x 1 2) x)) "")
  (test/exn (parse '(let (1 2) x)) "")
  ;(test/exn (parse 'let) "")
  (test/exn (parse '(let (let 1) 1)) "")
  
  ; Test let-rec parsing
  (test (parse '(let-rec (x (lambda (y) (x y))) x)) (letrecS 'x (lamS 'y (appS (idS 'x) (idS 'y))) (idS 'x)))
  (test/exn (parse '(let-rec (x 1) x)) "")
  (test/exn (parse '(let-rec x 1 x)) "")
  (test/exn (parse '(let-rec (x 1 2) x)) "")
  (test/exn (parse '(let-rec (1 2) x)) "")
  ;(test/exn (parse 'let-rec) "")
  (test/exn (parse '(let-rec (let-rec 1) 1)) "")
  
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
  (test/exn (parse (first (s-exp->list '(- 1 2)))) ""))


(define (strings-append los)
  (foldl (lambda (x y) (string-append y x)) "" los))

(module+ test
  (test (strings-append empty) "")
  (test (strings-append (list "a")) "a")
  (test (strings-append (list "a" "b" "c")) "abc"))

;; A subtree-part has the field name and the value of the subtree.
;; A property part is, e.g., the number in a numS or the id in an idS.
;; For that, we need both its name and its value (since we won't call
;; into it recursively).
(define-type Part
  [subtree-part (name : string) (subtree : NodeInfo)]
  [property-part (name : string) (value : string)])

;; The name of the node type plus a list of its parts (in order!)
(define-type NodeInfo
  [node-info (name : string) (parts : (listof Part))])

(define (construct-info-tree [node : ExprS]) : NodeInfo
  (type-case ExprS node
    [numS (n) 
          (node-info "numS"
                     (list (property-part "n" (to-string n))))]
    [seqS (exp1 exp2)
          (node-info "seqS"
                     (list (subtree-part "exp1" (construct-info-tree exp1))
                           (subtree-part "exp2" (construct-info-tree exp2))))]
    [if0S (tst thn els) 
          (node-info "if0S"
                     (list (subtree-part "test" (construct-info-tree tst))
                           (subtree-part "then" (construct-info-tree thn))
                           (subtree-part "else" (construct-info-tree els))))]
    [readS ()
           (node-info "readS"
                      (list))]
    [strS (s)
          (node-info "strS"
                     (list (property-part "s" s)))]
    [displayS (exp)
              (node-info "displayS"
                         (list (subtree-part "exp" (construct-info-tree exp))))]
    [plusS (l r) 
           (node-info "plusS"
                      (list (subtree-part "l" (construct-info-tree l))
                            (subtree-part "r" (construct-info-tree r))))]
    [multS (l r) 
           (node-info "multS"
                      (list (subtree-part "l" (construct-info-tree l))
                            (subtree-part "r" (construct-info-tree r))))]
    [bminusS (l r) 
             (node-info "bminusS"
                        (list (subtree-part "l" (construct-info-tree l))
                              (subtree-part "r" (construct-info-tree r))))]
    [appS (f a) 
          (node-info "appS"
                     (list (subtree-part "f" (construct-info-tree f))
                           (subtree-part "a" (construct-info-tree a))))]
    [idS (i) 
         (node-info "idS"
                    (list (property-part "i" (to-string i))))]
    [lamS (id body) 
          (node-info "lamS"
                     (list (property-part "id" (to-string id))
                           (subtree-part "body" (construct-info-tree body))))]
    [letS (id val body) 
          (node-info "letS"
                     (list (property-part "id" (to-string id))
                           (subtree-part "val" (construct-info-tree val))
                           (subtree-part "body" (construct-info-tree body))))]
    [letrecS (id val body) 
             (node-info "letrecS"
                        (list (property-part "id" (to-string id))
                              (subtree-part "val" (construct-info-tree val))
                              (subtree-part "body" (construct-info-tree body))))]))



; produce gv graph (as string) 
(define (gvify [info-tree : NodeInfo]) : string
  (local [(define next-node-number 1)
          (define (fresh-node) : number
            (begin (set! next-node-number (add1 next-node-number))
                   (sub1 next-node-number)))
          (define (node-name [n : number]) : string
            (string-append "node" (to-string n)))
          (define (gen-edge [parent : number] [child : number] [label : 'a] [style : 'b]) : string
            (strings-append 
             (list "\t" (node-name parent) " -> "
                   (node-name child) " [label=" 
                   (to-string label) ",style=" (to-string style) "]" "\n")))
          (define (gen-node [n : number] [shape : 'a] [label : 'b]) : string
            (strings-append
             (list "\t" (node-name n) 
                   " [shape=" (to-string shape)
                   ",label=" (to-string label)
                   "]\n")))
          (define (gen-false-node [n : number] [label : 'a]) : string
            (gen-node n "none" label))
          (define (gen-real-node [n : number] [label : 'a]) : string
            (gen-node n "rectangle" label))
          (define (gen-real-edge [parent : number] [child : number] [label : 'a]) : string
            (gen-edge parent child label "solid"))
          (define (gen-false-edge [parent : number] [child : number] [label : 'a]) : string
            (gen-edge parent child label "dotted"))
          ;; Assumes the root node has already been created
          ;; and generates the nodes and edges for its children
          ;; and recursively for the rest of the tree.
          (define (gv-from-tree node-number tree)
            (local [(define (helper parts)
                      (foldl 
                       (lambda (part str)
                         (string-append
                          str
                          (local [(define child-node (fresh-node))]
                            (type-case Part part
                              [subtree-part (name child-node-info)
                                            (strings-append
                                             (list
                                              (gen-real-node child-node 
                                                             (node-info-name child-node-info))
                                              (gen-real-edge node-number child-node
                                                             name)
                                              (gv-from-tree child-node child-node-info)))]
                              [property-part (name value)
                                             (local [(define (trim-str value)
                                                       (if (> (string-length value) MAX-PROP-NAME-LENGTH)
                                                           (string-append (substring value 
                                                                                     0
                                                                                     (- MAX-PROP-NAME-LENGTH (string-length PROP-NAME-PADDING)))
                                                                          PROP-NAME-PADDING)
                                                           value))]
                                               (strings-append
                                                (list
                                                 (gen-false-node child-node (trim-str value))
                                                 (gen-false-edge node-number child-node
                                                                 name))))]))))
                       ""  ; initializer for the foldl
                       parts))]
              (helper (node-info-parts tree))))
          (define root-node-number (fresh-node))]
    (strings-append
     (list 
      "digraph G {\n"
      (gen-real-node root-node-number (node-info-name info-tree))
      (gv-from-tree root-node-number info-tree)
      "}\n"))))

(module+ test
  (test (desugar (letS 'x (numS 1) (numS 2)))
        (letC 'x (numC 1) (numC 2)))
  
  (test (desugar (letrecS 'x (numS 1) (numS 2)))
        (letrecC 'x (numC 1) (numC 2)))
  
  (test (desugar (lamS 'x (numS 1)))
        (lamC 'x (numC 1)))
  
  (test (desugar (seqS (numS 1) (numS 2))) (seqC (numC 1) (numC 2)))
  
  (test (desugar (strS "hello")) (strC "hello"))
  
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


















; desugar the surface abstract syntax tree into our core abstract syntax tree
(define (desugar [st : ExprS]) : ExprC
  (type-case ExprS st
    [numS (n) (numC n)]
    [plusS (l r) (plusC (desugar l) (desugar r))]
    [multS (l r) (multC (desugar l) (desugar r))]
    [readS () (readC)]
    [strS (s) (strC s)]
    [seqS (e1 e2) (seqC (desugar e1) (desugar e2))]
    [displayS (e) (displayC (desugar e))]
    [bminusS (l r) (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [appS (f a) (appC (desugar f) (desugar a))]
    [idS (i) (idC i)]
    [if0S (c t e) (if0C (desugar c) (desugar t) (desugar e))]
    [lamS (id body) (lamC id (desugar body))]
    [letrecS (i v b) (letrecC i (desugar v) (desugar b))]
    [letS (i v b) (letC i (desugar v) (desugar b))]))  
; Dropped this desugaring to make function call tree clearer:
; (letS i v b) => (appC (lamC i b) v)

(module+ test
  (test (desugar (letS 'x (numS 1) (numS 2)))
        (letC 'x (numC 1) (numC 2)))
  
  (test (desugar (readS)) (readC))
  (test (desugar (displayS (numS 1))) (displayC (numC 1)))
  
  (test (desugar (letrecS 'x (numS 1) (numS 2)))
        (letrecC 'x (numC 1) (numC 2)))
  
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


(define-type Binding
  [bind (name : symbol) (val : Value)])

(define-type-alias Env (listof Binding))
(define mt-env : Env empty)
(define extend-env : (Binding Env -> Env) cons)

; look up the id in env, giving an error if id is not present
(define (lookup [id : symbol] [env : Env]) : Value
  (type-case (optionof Binding) (findf (lambda (binding) (symbol=? (bind-name binding) id)) env)
    [some (binding) (bind-val binding)]
    [none () (error 'lookup (string-append "no binding found for identifier: " (to-string id)))]))

(module+ test
  (test/exn (lookup 'a mt-env) "")
  (test (lookup 'a (extend-env (bind 'a (numV 1)) mt-env)) (numV 1))
  (test (lookup 'a (extend-env (bind 'a (numV 2)) (extend-env (bind 'a (numV 1)) mt-env))) (numV 2))
  (test (lookup 'a (extend-env (bind 'b (numV 2)) (extend-env (bind 'a (numV 1)) mt-env))) (numV 1))
  (test (lookup 'b (extend-env (bind 'b (numV 2)) (extend-env (bind 'a (numV 1)) mt-env))) (numV 2))
  (test (lookup 'f (extend-env (bind 'f (closV 'x (numC 0) mt-env)) mt-env)) (closV 'x (numC 0) mt-env))
  (test/exn (lookup 'c (extend-env (bind 'b (numV 2)) (extend-env (bind 'a (numV 1)) mt-env))) ""))

; interpret (evaluate) the given well-formed arithmetic expression AST in the given environment
(define (interp [ast : ExprC] [env : Env]) : (Value * NodeInfo)
  (local [(define (interp-only [pred? : (Value -> boolean)] [err : string] [ast : ExprC] [env : Env]) : (Value * NodeInfo)
            (local [(define-values (result info) (helper ast env))]
              (if (pred? result)
                  (values result info)
                  (error 'interp (string-append err (to-string ast))))))
          (define (helper [ast : ExprC] [env : Env]) : (Value * NodeInfo)
            (type-case ExprC ast
              [numC (n) (values (numV n) (node-info (to-string n) empty))]
              [if0C (c t e)
                    (local [(define-values (c-result c-info) (interp-only numV? "expected numeric value from: " c env))]
                      (local [(define-values (result sub-info) (if (= (numV-n c-result) 0)
                                                                   (helper t env)
                                                                   (helper e env)))]
                        (values result (node-info "if0" (list (subtree-part "cond" c-info) (subtree-part "body" sub-info))))))]
              [seqC (e1 e2)
                    (local [(define-values (e1-result e1-info) (helper e1 env))
                            (define-values (e2-result e2-info) (helper e2 env))]
                      (values e2-result (node-info "seq" (list (subtree-part "exp1" e1-info)
                                                               (subtree-part "exp2" e2-info)))))]
              [readC ()
                     (values (numV (s-exp->number (read))) ; Just assume we get a number for now.
                             (node-info "read" (list)))]
              [strC (s)
                    (values (strV s) (node-info s (list)))]
              [displayC (exp)
                        (local [(define-values (e-result e-info) (interp-only (lambda (v) (or (numV? v) (strV? v))) "expected printable (non-closure) value from: " exp env))]
                          (begin
                            (display (if (numV? e-result) (to-string (numV-n e-result)) (strV-s e-result)))
                            (values e-result (node-info "display" (list (subtree-part "exp" e-info))))))]
              [plusC (l r) (local [(define-values (l-result l-info) (interp-only numV? "expected numeric value from: " l env))
                                   (define-values (r-result r-info) (interp-only numV? "expected numeric value from: " r env))]
                             (values (numV (+ (numV-n l-result) (numV-n r-result))) (node-info "plus" (list (subtree-part "l" l-info)
                                                                                                            (subtree-part "r" r-info)))))]
              [multC (l r) (local [(define-values (l-result l-info) (interp-only numV? "expected numeric value from: " l env))
                                   (define-values (r-result r-info) (interp-only numV? "expected numeric value from: " r env))]
                             (values (numV (* (numV-n l-result) (numV-n r-result))) (node-info "mult" (list (subtree-part "l" l-info)
                                                                                                            (subtree-part "r" r-info)))))]
              [letC (i v b) (local [(define-values (value v-info) (helper v env))
                                    (define real-env (extend-env (bind i value)
                                                                 env))
                                    (define-values (result b-info) (helper b real-env))]
                              (values result (node-info "let" (list (property-part "id" (symbol->string i))
                                                                    (subtree-part "val" v-info)
                                                                    (subtree-part "body" b-info)))))]
              [letrecC (i v b) 
                       (begin
                         ; We know v is a lamC.
                         ; Let's double-check and then use that.
                         (when (not (lamC? v))
                           (error 'interp (string-append "Malformed letrecC (non-lambda value) in: " (to-string ast))))
                         
                         ; I am (clumsily) just using plai-typed's let-rec equivalent.
                         ; Our mutation solution makes what's happening clearer.
                         ; It's also possible to desugar this with ONLY lamC and appC.
                         (shared [(real-env (cons (bind i (closV (lamC-arg v)
                                                                 (lamC-body v)
                                                                 real-env))
                                                  env))]
                           (local [(define-values (result b-info) (helper b real-env))]
                             (values result (node-info "let-rec" (list (property-part "id" (symbol->string i))
                                                                       (subtree-part "arg" 
                                                                                     (node-info "lam" 
                                                                                                (list 
                                                                                                 (property-part "id" (symbol->string (lamC-arg v)))
                                                                                                 (property-part "body" (to-string (lamC-body v))))))
                                                                       (subtree-part "body" b-info)))))))]
              [appC (f a) (local [(define-values (fv f-info) (interp-only closV? "expected a closure for application from: "
                                                                          f env))
                                  (define-values (av a-info) (helper a env))
                                  (define fv-arg (closV-arg fv))
                                  (define fv-body (closV-body fv))
                                  (define fv-env (closV-env fv))
                                  (define-values (result call-info) (helper fv-body (extend-env (bind fv-arg av) fv-env)))]
                            (values result (node-info "app" (list (subtree-part "fun-expr" f-info)
                                                                  (subtree-part "arg-expr" a-info)
                                                                  (subtree-part "call" call-info)))))]
              [lamC (arg body) (values (closV arg body env) (node-info "lam" empty))]
              [idC (i) (local [(define value (lookup i env))]
                         (values value
                                 (cond
                                   [(numV? value)
                                    (node-info (strings-append (list (symbol->string i) "=" (to-string (numV-n value)))) empty)]
                                   [(strV? value)
                                    (node-info (strings-append (list (symbol->string i) "=" (strV-s value))) empty)]
                                   [else (node-info (symbol->string i) empty)])))]))]
    (helper ast env)))

(define (interp-value ast env)
  (local [(define-values (result info) (interp ast env))]
    result))

(module+ test
  (test (interp-value (desugar (parse '(display 5))) mt-env) (numV 5))
  
  (test (interp-value (desugar (parse '"hello")) mt-env) (strV "hello"))
  
  (test (interp-value (desugar (parse '(seq 1 2))) mt-env) (numV 2))
  
  ; Shriram's static scoping test
  (test (interp-value (appC (appC (lamC 'x
                                        (lamC 'y
                                              (plusC (idC 'x) (idC 'y))))
                                  (numC 4))
                            (numC 5)) mt-env) (numV 9))
  
  (test (interp-value (lamC 'x (idC 'y)) (extend-env (bind 'y (numV 5)) mt-env))
        (closV 'x (idC 'y) (extend-env (bind 'y (numV 5)) mt-env)))
  (test (interp-value (appC (lamC 'x (idC 'x)) (numC 1)) mt-env) (numV 1))
  (test (interp-value (appC (lamC 'x (numC 2)) (numC 1)) mt-env) (numV 2))
  
  ; We SHOULD get access to this y, since the function's lexical scope includes this "definition".
  (test (interp-value (appC (lamC 'x (idC 'y)) (numC 1)) (extend-env (bind 'y (numV 5)) mt-env)) (numV 5))
  
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
  
  (test (interp-value (appC (lamC 'x (appC (lamC 'f (appC (idC 'f) (numC 1000)))
                                           (lamC 'y (plusC (idC 'x) (idC 'y)))))
                            (numC 1)) 
                      mt-env)
        (numV 1001))
  (test (interp-value (appC (lamC 'x (appC (lamC 'f (appC (lamC 'x (appC (lamC 'y (appC (idC 'f) (numC 1000)))
                                                                         (numC 100)))
                                                          (numC 10)))
                                           (lamC 'y (plusC (idC 'x) (idC 'y)))))
                            (numC 1)) 
                      mt-env)
        (numV 1001))
  (test/exn (interp-value (appC (lamC 'f (appC (lamC 'x (appC (lamC 'y (appC (idC 'f) (numC 1000)))
                                                              (numC 100)))
                                               (numC 10)))
                                (lamC 'y (plusC (idC 'x) (idC 'y))))
                          mt-env)
            "")
  
  (test/exn (interp-value (appC (numC 1) (numC 0)) mt-env) "")
  (test/exn (interp-value (plusC (lamC 'x (numC 1)) (numC 0)) mt-env) "")
  
  ;  (define yield1 (lamC 'yield1 'x (numC 1)))
  ;  (define identity (lamC 'identity 'x (idC 'x)))
  ;  (define rename (lamC 'rename 'rename (idC 'rename)))
  ;
  ;  (define yield2 (lamC 'yield2 'x (numC 2)))
  ;  (define yield3 (lamC 'yield2 'x (numC 3)))
  ;  
  ;  (define fds1 (list yield1 yield2 yield3))
  ;  (define fds2 (list yield1 yield3 yield2))
  ;  (define fds3 (list yield2 yield1 yield3))
  ;  (define fds4 (list yield2 yield3 yield1))
  ;  (define fds5 (list yield3 yield1 yield2))
  ;  (define fds6 (list yield3 yield2 yield1))
  ;  (define fdss (list fds1 fds2 fds3 fds4 fds5 fds6))
  ;  
  ;  (map (lambda (x) (test (interp-value (appC 'yield1 (numC 0)) mt-env x) 1)) fdss)
  
  (test (interp-value (numC 1) mt-env) (numV 1))
  (test (interp-value (plusC (numC 1) (numC -2)) mt-env) (numV -1))
  (test (interp-value (multC (numC -3) (numC 2)) mt-env) (numV -6))
  ;  (test (interp-value (appC 'yield1 (numC 5)) mt-env (list yield1)) 1)
  ;  (test (interp-value (appC 'identity (numC 5)) mt-env (list identity)) 5)
  ;  (test (interp-value (appC 'rename (numC 5)) mt-env (list rename)) 5)
  
  ; Test one "complex" case, just to be safe.
  (test (interp-value (desugar (parse '(- (* 2 -1) (+ 3 4)))) mt-env)
        (numV (- (* 2 -1) (+ 3 4))))
  
  (test/exn (interp-value (idC 'x) mt-env) "")
  ;  (test/exn (interp-value (idC 'x) mt-env (list (lamC 'x 'y (numC 0)))) "")
  ;  (test/exn (interp-value (appC 'foo (numC 0)) mt-env fds1) "")
  
  ;(test (interp-value (idC 'x) (extend-env (bind 'x 5) mt-env)) 5)
  
  ;  ; Shriram's tests:
  ;  (test (interp-value (plusC (numC 10) (appC 'const5 (numC 10)))
  ;                mt-env
  ;                (list (lamC 'const5 '_ (numC 5))))
  ;        15)
  ; 
  ;  (test (interp-value (plusC (numC 10) (appC 'double (plusC (numC 1) (numC 2))))
  ;                mt-env
  ;                (list (lamC 'double 'x (plusC (idC 'x) (idC 'x)))))
  ;        16)
  ;  
  ;  (test (interp-value (plusC (numC 10) (appC 'quadruple (plusC (numC 1) (numC 2))))
  ;                mt-env
  ;                (list (lamC 'quadruple 'x (appC 'double (appC 'double (idC 'x))))
  ;                      (lamC 'double 'x (plusC (idC 'x) (idC 'x)))))
  ;        22)
  ;  
  ;  ; Simplified version of last:
  ;  (test (interp-value (appC 'quadruple (numC 3))
  ;                mt-env
  ;                (list (lamC 'quadruple 'x (appC 'double (appC 'double (idC 'x))))
  ;                      (lamC 'double 'x (plusC (idC 'x) (idC 'x)))))
  ;        12)
  
  ;  ; But, what about things like this???
  ;  (test/exn (interp-value (appC 'oops (numC 1)) (extend-env (bind 'x 5) mt-env)
  ;                    (list (lamC 'oops 'y (idC 'x)))) "")
  )

(define (run-with-info [sexp : s-expression]) : (Value * NodeInfo)
  (interp (desugar (parse sexp)) mt-env))

(define (run [sexp : s-expression]) : Value
  (local [(define-values (result info) (run-with-info sexp))]
    result))

(define (parse-to-gv sexp)
  (gvify (construct-info-tree (parse sexp))))

(define (run-to-gv sexp)
  (local [(define-values (result info) (run-with-info sexp))]
    (gvify info)))

(module+ test
  ; Test some parsed behaviour
  (test (run '1) (numV 1))
  (test (run '(+ 1 2)) (numV (+ 1 2)))
  (test (run '(* 2 3)) (numV (* 2 3)))
  (test (run '(- 2 3)) (numV (- 2 3)))
  
  (test (run '(let (x 3) (let (y 4) (let (x 2) (+ x y))))) (numV 6))
  (test (run '(let (x 1) (let (y (lambda (z) x)) (let (x 2) (y 1))))) (numV 1))
  (test/exn (run '(let (x x) x)) "")
  (test (run '(let (x 1) (let (x x) x))) (numV 1))
  (test/exn (run '(let-rec (x 3) (let-rec (y 4) (let-rec (x 2) (+ x y))))) "")
  (test/exn (run '(let-rec (x 1) (let-rec (y (lambda (z) x)) (let-rec (x 2) (y 1))))) "")
  ;(test/exn (run '(let-rec (x x) x)) "") ;; This does fail, but with the wrong "kind" of error.
  ;(test/exn (run '(let-rec (x 1) (let-rec (x x) x))) "") ;; Ditto.
  
  #;(test (run '(let-rec (fact (lambda (n) (if0 n
                                              1
                                              (* n (fact (+ n -1))))))
                       (fact 5)))
        (numV (* 5 4 3 2 1)))
  
  (test (run '(let (x 1) x)) (numV 1))
  (test (run '(let (x 1) (let (f (lambda (y) (+ x y))) (let (x 10) (let (y 100) (f 1000)))))) (numV 1001)))


(define web-example
  '(let (web-read (lambda (s)
                    (seq
                     (seq (display s) (display "\n"))
                     (read))))
     (seq
      (seq
       (display
        (+ (web-read "Enter the first number:")
           (web-read "Enter the second number:")))
       (display "\n"))
      "")))

