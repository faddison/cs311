#lang plai-typed

(require (typed-in racket/base (raise-user-error : (string -> void))))

(define-type FieldP
  [fieldP (name : string) (value : ExprP)])

(define-type LHS
  [BracketLHS (obj : ExprP) (field : ExprP)]
  [DotLHS (obj : ExprP) (field : symbol)]
  [IdLHS (id : symbol)])

;; ExprPs are ParselTongue's toplevel:
(define-type ExprP
  [ObjectP (fields : (listof FieldP))]
  [DotP (obj : ExprP) (field : symbol)]
  [BracketP (obj : ExprP) (field : ExprP)]
  [DotMethodP (obj : ExprP) (field : symbol) (args : (listof ExprP))]
  [BrackMethodP (obj : ExprP) (field : ExprP) (args : (listof ExprP))]

  [FuncP (args : (listof symbol)) (body : ExprP)]
  [AppP (func : ExprP) (args : (listof ExprP))]
  [DefvarP (id : symbol) (bind : ExprP) (body : ExprP)]
  [DeffunP (name : symbol) (ids : (listof symbol)) (funbody : ExprP) (body : ExprP)]
  [IdP (name : symbol)]

  [WhileP (test : ExprP) (body : ExprP)]
  [ForP (init : ExprP) (test : ExprP) (update : ExprP) (body : ExprP)]

  [AssignP (lhs : LHS) (value : ExprP)]

  [SeqP (es : (listof ExprP))]
  [IfP (cond : ExprP) (then : ExprP) (else : ExprP)]

  [NumP (n : number)]
  [StrP (s : string)]
  [TrueP]
  [FalseP]

; An op is one of '+ '- '== 'print
  [PrimP (op : symbol) (args : (listof ExprP))]
; A PrimAssign op is one of '+ '-
  [PrimAssignP (op : symbol) (lhs : LHS) (value : ExprP)]

  [PreIncP (lhs : symbol)]
  [PostIncP (lhs : symbol)]
  [PreDecP (lhs : symbol)]
  [PostDecP (lhs : symbol)])

(define-type FieldC
  [fieldC (name : string) (value : ExprC)])

(define-type ExprC

  [ObjectC (fields : (listof FieldC))]
  [GetFieldC (obj : ExprC) (field : ExprC)]
  [SetFieldC (obj : ExprC) (field : ExprC) (value : ExprC)]

  [FuncC (args : (listof symbol)) (body : ExprC)]
  [AppC (func : ExprC) (args : (listof ExprC))]
  [LetC (id : symbol) (bind : ExprC) (body : ExprC)]
  [IdC (id : symbol)]
  [Set!C (id : symbol) (value : ExprC)]

  [IfC (cond : ExprC) (then : ExprC) (else : ExprC)]
  [SeqC (e1 : ExprC) (e2 : ExprC)]

  [NumC (n : number)]
  [StrC (s : string)]
  [TrueC]
  [FalseC]

  [ErrorC (expr : ExprC)]

; The core operations are 'string+ 'num+ 'num- '== '< '> 'print 'tagof
  [Prim1C (op : symbol) (arg : ExprC)]
  [Prim2C (op : symbol) (arg1 : ExprC) (arg2 : ExprC)])

;;;;;;;;;; Environment Definitions ;;;;;;;;;;;;;;
;; Please consider the interface to the environment to be:
;; - the types Env, Location, and Binding
;;   (and associated functions like bind-name)
;; - the variable empty-env
;; - the extend-env, env-lookup, and env-bound-ids function

(require
(typed-in
 racket
 [remove-duplicates : ((listof 'a) ('a 'a -> boolean) -> (listof 'a))]))

(define-type-alias Env (listof Binding))
(define-type Binding
 [bind (name : symbol) (value : Location)])

(define-type-alias Location number)

(define empty-env empty)

; produce a new environment that is env extended by binding id to value.
(define (extend-env [id : symbol] [locn : Location] [env : Env]) : Env
 (cons (bind id locn) env))

; env-lookup is the standard environment lookup (with error on unbound)
; (Neither this nor store-lookup is the metafunction Lookup described by
; the ParselTongue spec.)
(define (env-lookup [id : symbol] [env : Env]) : Location
 (cond [(empty? env)
        (interp-error (string-append "Unbound identifier: "
                                     (symbol->string id)))]
       [(symbol=? id (bind-name (first env)))
        (bind-value (first env))]
       [else
        (env-lookup id (rest env))]))

; collect all bound identifiers from an environment
(define (env-bound-ids [env : Env]) : (listof symbol)
 (remove-duplicates (map bind-name env) symbol=?))

(define-type FieldV
  [fieldV (name : string) (value : ValueC)])

(define-type ValueC
  [ObjectV (fields : (listof FieldV))]
  [ClosureV (args : (listof symbol)) (body : ExprC) (env : Env)]
  [NumV (n : number)]
  [StrV (s : string)]
  [TrueV]
  [FalseV])

(define (pretty-value (v : ValueC)) : string
  (type-case ValueC v
    [ObjectV (fs) "object"]
    [ClosureV (a b e) "function"]
    [NumV (n) (to-string n)]
    [StrV (s) s]
    [TrueV () "true"]
    [FalseV () "false"]))

(define (interp-error str)
  (begin
    (raise-user-error str)
    (error 'interp str)))

