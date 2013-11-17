#lang plai-typed

(require "typed-lang2.rkt")

;; ;;;;;;;; Store Definitions ;;;;;;;;;;;;;;
;; Please consider the interface to the store to be:
;; - the types Location, Cell, and Store
;;   (and associated functions like cell-location)
;; - the variable empty-store
;; - the store-lookup, fresh-loc, update-store,
;;   and alloc-store functions
;;
;; TODO: complete fresh-loc, and alloc-store!

(define-type Cell
 [cell (location : Location) (value : ValueC)])

(define-type-alias Store (listof Cell))
(define empty-store empty)

; find the value stored at the given location
; (with an error on an unallocated location)
(define (store-lookup [locn : Location] [store : Store]) : ValueC
 (cond [(empty? store)
        (interp-error (string-append "Unallocated cell: "
                                     (to-string locn)))]
       [(= locn (cell-location (first store)))
        (cell-value (first store))]
       [else
        (store-lookup locn (rest store))]))

; produce a fresh location not presently in the store
(define (fresh-loc [store : Store]) : Location
 ;; TODO: implement me!
 ;; Hint: can you find out what the largest
 ;; location in the store is?  Once you have
 ;; that, can you calculate a fresh location?

	;;(cond 
		;;[(empty? store) 0]
		;;[(empty? (rest store)) (+ 1 (cell-location (first store)))]
		;;[else (+ 1 (foldl (lambda (expr result) (max result expr)) (first (map cell-location store)) (rest (map cell-location store))))]
	;;)
	 (+ 1 (foldl max -1 (map cell-location store))))


; update the store to contain the given value at the given location
; PRESENTLY: no check that the location already exists
(define (update-store [locn : Location]
                     [value : ValueC]
                     [store : Store]) : Store	
	
	(cons 
		(cell locn value) 
		store
		;;(store-remove (cell locn (store-lookup locn store)) store empty-store)
	)
)

(define (store-remove [c1 : Cell] [old : Store] [new : Store]) : Store
	(cond
		[(empty? old) (cons (first new) (rest new))] ;; this is weird
		[(cell-equal c1 (first old)) (store-remove c1 new (rest old))]
		[else (store-remove c1 (cons (first old) new) (rest old))]
	)
)


(define (cell-equal [c1 : Cell] [c2 : Cell]) : boolean
	(and (= (cell-location c1) (cell-location c2))
			 (value-equal (cell-value c1) (cell-value c2))
	)
)

(define (value-equal [v1 : ValueC] [v2 : ValueC]) : boolean
	(equal? (pretty-value v1) (pretty-value v1))
)
		
						

; allocate the given value at a new location in the store,
; producing the location used and the new store.
;
; to get the Location and Store out of the result, use
; code like:
;
; (local [(define-values (locn store) (alloc-store ...))]
;   ...)
;
; PRESENTLY: no check that the location already exists
; We may want to add that in the future.
(define (alloc-store [value : ValueC]
                    [store : Store]) : (Location * Store)
 ;; TODO: implement me!
	 (local [(define new-loc (fresh-loc store))]
    (values new-loc (cons (cell new-loc value) store))))
 
 (define (get-type [value : ValueC]) : string
	(type-case ValueC value
		[ObjectV (fs) "object"]
		[ClosureV (a b e) "function"]
		[NumV (n) "number"]
		[StrV (s) "string"]
		[TrueV () "boolean"]
		[FalseV () "boolean"]
	)
)
 
 
 (define (thread-args
         [args : (listof ExprC)]
         [env : Env]
         [store : Store])
  : ((listof ValueC) * Store)
  (if (empty? args)
      (values empty store)
      (type-case Result (interp-full (first args) env store)
        [v*s (arg-v arg-s)
             (local [(define-values (args-rest args-store) (thread-args (rest args) env arg-s))]
               (values (cons arg-v args-rest) args-store))])))

(define (foldl2
         [f : ('a 'b 'c -> 'c)]
         [l1 : (listof 'a)]
         [l2 : (listof 'b)]
         [base : 'c])
  : 'c
  (if (or (empty? l1) (empty? l2)) base
      (foldl2 f (rest l1) (rest l2) (f (first l1) (first l2) base))))

(define (extend-env-helper
         [env : Env]
         [store : Store]
         [ids : (listof symbol)]
         [vals : (listof ValueC)])
  : (Env * Store)
  (if (empty? ids)
      (values env store)
      (local [(define-values (new-locs new-store) (n-alloc-store vals store))]
        (values (foldl2 extend-env ids new-locs env)
                new-store))))
				
(define (n-alloc-store [vals : (listof ValueC)] [store : Store]) : ((listof Location) * Store)
  (if (empty? vals)
      (values empty store)
      (local [(define-values (loc1 store1) (alloc-store (first vals) store))
              (define-values (locs-rest store-rest) (n-alloc-store (rest vals) store1))]
        (values (cons loc1 locs-rest) store-rest))))
		
(define (fieldc-to-fieldv [field : FieldC] [env : Env] [store : Store]) : FieldV
	(type-case FieldC field
		[fieldC (name value) 
			(type-case Result (interp-full value env store)
				[v*s (v-value s-value) (fieldV name v-value)]
			)
		]
	)
)


(module+ test
  (local ((define store0 empty-store)
          (define-values (locn1 store1) (alloc-store (NumV 1) store0))
          (define-values (locn2 store2) (alloc-store (NumV 2) store1))
          (define-values (locn3 store3) (alloc-store (NumV 3) store2)))
    
    ; Sadly, these don't work because of the implementation of interp-error.
    ;(test/exn (store-lookup (fresh-loc store0) store0) "Unallocated cell:")
    ;(test/exn (store-lookup (fresh-loc store1) store1) "Unallocated cell:")
    ;(test/exn (store-lookup (fresh-loc store2) store2) "Unallocated cell:")
    ;(test/exn (store-lookup (fresh-loc store3) store3) "Unallocated cell:")
    
    ; Instead, we'll do this.
    (begin
      (test (member (fresh-loc store1) (list locn1)) false)
      (test (member (fresh-loc store2) (list locn1 locn2)) false)
      (test (member (fresh-loc store3) (list locn1 locn2 locn3)) false)
      
      (test (store-lookup locn1 store1) (NumV 1))
      (test (store-lookup locn1 store2) (NumV 1))
      (test (store-lookup locn2 store2) (NumV 2))
      (test (store-lookup locn1 store3) (NumV 1))
      (test (store-lookup locn2 store3) (NumV 2))
      (test (store-lookup locn3 store3) (NumV 3))
      (test (store-lookup locn1 (update-store locn1 (NumV -1) store1))
            (NumV -1))
      (test (store-lookup locn1 (update-store locn1 (NumV -1) store3))
            (NumV -1))
      (test (store-lookup locn3 (update-store locn1 (NumV -1) store3))
            (NumV 3))
      (test (store-lookup locn1 (update-store locn3 (NumV -3) store3))
            (NumV 1))
      (test (store-lookup locn3 (update-store locn3 (NumV -3) store3))
            (NumV -3)))))

(define-type Result
  [v*s (value : ValueC) (store : Store)])

(define (interp-full [exprC : ExprC] [env : Env] [store : Store]) : Result
  (type-case ExprC exprC
;; TODO: implement all remaining cases of ExprC; you will certainly
;;       want helper functions (like the Lookup meta function
;;       described in the ParselTongue specification!)    

	;;[ObjectC (fields : (listof FieldC))]
	;;[GetFieldC (obj : ExprC) (field : ExprC)]
	;;[SetFieldC (obj : ExprC) (field : ExprC) (value : ExprC)]
	;;[FuncC (args : (listof symbol)) (body : ExprC)]
	;;[AppC (func : ExprC) (args : (listof ExprC))]
	;;[LetC (id : symbol) (bind : ExprC) (body : ExprC)]
	;;[IdC (id : symbol)]
	;;[Set!C (id : symbol) (value : ExprC)]
	;;[IfC (cond : ExprC) (then : ExprC) (else : ExprC)]
	;;[SeqC (e1 : ExprC) (e2 : ExprC)]
	;;[NumC (n : number)]
	;;[StrC (s : string)]
	;;[TrueC]
	;;[FalseC]
	;;[ErrorC (expr : ExprC)]
	;;[Prim1C (op : symbol) (arg : ExprC)]
	;;[Prim2C (op : symbol) (arg1 : ExprC) (arg2 : ExprC)])
	
	;;(define-type FieldV
	;;[fieldV (name : string) (value : ValueC)])
	;;[ObjectV (fields : (listof FieldV))]
	
	[ObjectC (fields) (v*s (ObjectV (map (lambda (field) (fieldc-to-fieldv field env store)) fields)) store)] ;; how do we account for updated stores? see piazza post
		
	[GetFieldC (obj field) 
		(type-case Result (interp-full obj env store)
			[v*s (v-obj s-obj) (interp-full field env s-obj)]
		)
	]
	
	[SetFieldC (obj field value) 
		(type-case Result (interp-full obj env store)
			[v*s (v-obj s-obj)
				(type-case Result (interp-full field env s-obj)
					[v*s (v-field s-field) (interp-full value env s-field)]
				)
			]
		)
	]

	[NumC (n) (v*s (NumV n) store)]
	[StrC (s) (v*s (StrV s) store)]
	[TrueC () (v*s (TrueV) store)]
	[FalseC () (v*s (FalseV) store)]
	[IdC (id) (v*s (store-lookup (env-lookup id env) store) store)]
	[ErrorC (s) (interp-error (expr-to-string s))]
	[FuncC (args body) (v*s (ClosureV args body env) store)]
	
	[IfC (cnd thn els) 
		(type-case Result (interp-full cnd env store)
			[v*s (v-cnd s-cnd)
				(type-case ValueC v-cnd
					[TrueV () (interp-full thn env s-cnd)]
					[else (interp-full els env s-cnd)]
				)
			]
		)
	]
	
	[LetC (id expr body)
          (type-case Result (interp-full expr env store)
            [v*s (expr-v expr-s)
                 (local [(define-values (new-loc new-store)
                           (alloc-store expr-v expr-s))]
                   (interp-full body (extend-env id new-loc env)
                                new-store))])]
								
    [AppC (func args)
          (type-case Result (interp-full func env store)
            [v*s (func-v func-s)
                 (local [(define-values (args-values args-s) (thread-args args env store))
                         (define-values (extended-env extended-store)
                           (extend-env-helper (ClosureV-env func-v) args-s (ClosureV-args func-v) args-values))]
                   (interp-full (ClosureV-body func-v)
                                extended-env
                                extended-store))])]
								
	
	
	[Prim1C (op arg)
		(case op
			['print
				(type-case Result (interp-full arg env store)
					[v*s (v-arg s-arg)
						(v*s (StrV (pretty-value v-arg)) s-arg)
					]
				)
			]
			['tagof 
				(type-case Result (interp-full arg env store)
					[v*s (v-arg s-arg) (v*s (StrV (get-type v-arg)) s-arg)]
				)
			]
		)
	]
		
	;; Milestone Methods
	[Prim2C (op arg1 arg2)
		(type-case Result (interp-full arg1 env store)
			[v*s (v-arg1 s-arg1)
				(type-case Result (interp-full arg2 env s-arg1)
					[v*s (v-arg2 s-arg2)
						(v*s 
							(case op
								['string+ (StrV (string-append (pretty-value v-arg1) (pretty-value v-arg2)))]
								['num+ 
									(type-case ValueC v-arg1
										[NumV (n1)
											(type-case ValueC v-arg2
												[NumV (n2)
													(NumV (+ n1 n2))
												]
												[else (interp-error "Bad arguments to +")]
											)
										]
										[StrV (v1) ;; no idea why strings are in num+. maybe because of faulty =='?
											(type-case ValueC v-arg2
												[StrV (v2)
													(StrV (string-append (pretty-value v-arg1) (pretty-value v-arg2)))
												]
												[else (interp-error "Bad arguments to +")]
											)
										]
										[else (interp-error "Bad arguments to +")]
									)
								]
								['num- 
									(type-case ValueC v-arg1
										[NumV (n1)
											(type-case ValueC v-arg2
												[NumV (n2)
													(NumV (- n1 n2))
												]
												[else (interp-error "Bad arguments to -")]
											)
										]
										[else (interp-error "Bad arguments to -")]
									)
								]
								['< 
									(type-case ValueC v-arg1
										[NumV (n1)
											(type-case ValueC v-arg2
												[NumV (n2)
													(if (< n1 n2)
														(TrueV)
														(FalseV)
													)
												]
												[else (interp-error "Bad arguments to <")]
											)
										]
										[else (interp-error "Bad arguments to <")]
									)
								]
								['> 
									(type-case ValueC v-arg1
										[NumV (n1)
											(type-case ValueC v-arg2
												[NumV (n2)
													(if (> n1 n2)
														(TrueV)
														(FalseV)
													)
												]
												[else (interp-error "Bad arguments to >")]
											)
										]
										[else (interp-error "Bad arguments to >")]
									)
								]
								['== 
									(if (eq? (get-type v-arg1) (get-type v-arg2))
										(TrueV)
										(FalseV)
									)
								]
							) s-arg2									
						)
					]
				)
			]
		)
	]
	
	
	[SeqC (e1 e2) 
		(type-case Result (interp-full e1 env store)
			[v*s (v-e1 s-e1)
				(interp-full e2 env s-e1)])]
								
	[Set!C (id value) 
		(type-case Result (interp-full value env store)
			[v*s (v-value s-value)
				(v*s v-value 
					(update-store (env-lookup id env) v-value s-value))])]
										
	)
)
									   
(define (expr-to-string [exprC : ExprC]) : string
	(pretty-value (interp exprC))
)

(define (interp [exprC : ExprC]) : ValueC
  (type-case Result (interp-full exprC empty empty)
    [v*s (value store) value]))


