#lang plai-typed

(require "typed-lang.rkt")

(define (make-ids (n : number)) : (listof symbol)
  (build-list n (lambda (n) (string->symbol (string-append "var-" (to-string n))))))

;; cascade-lets will build up the nested lets, and use body as the
;; eventual body, preserving order of evaluation of the expressions
(define (cascade-lets (ids : (listof symbol))
                      (exprs : (listof ExprC))
                      (body : ExprC)) : ExprC
  (cond [(empty? ids) body]
        [(cons? ids)
         (LetC (first ids) (first exprs) (cascade-lets (rest ids) (rest exprs) body))]))

;;(define (cascade-fields (ids : (listof symbol))
;;                      (exprs : (listof FieldC))
;;                      (body : ExprC)) : ExprC
;;  (cond [(empty? ids) body]
;;        [(cons? ids)
;;         (LetC (first ids) (first exprs) (cascade-fields (rest ids) (rest exprs) body))]))

;; check-type builds an expression that checks the type of the expression
;; given as an argument
(define (check-type (expr : ExprC) (type : string)) : ExprC
  (Prim2C '== (Prim1C 'tagof expr) (StrC type)))

;; and builds up an and expression from its two pieces
(define (and (expr1 : ExprC) (expr2 : ExprC)) : ExprC
  (IfC expr1 expr2 (FalseC)))

;; all builds up a series of ands over the expression arguments
(define (all (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (exp result) (and exp result)) (TrueC) exprs))

;; map-subtract builds an expression that maps 'num- over a list of expressions
(define (map-subtract (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (expr result) (Prim2C 'num- result expr)) (first exprs) (rest exprs)))


(define (desugar-subtract (args : (listof ExprP))) : ExprC
  (local ([define ids (make-ids (length args))]
          [define id-exps (map IdC ids)])
    (cascade-lets ids (map desugar args)
      (IfC (all (map (lambda (e) (check-type e "number")) id-exps))
           (map-subtract id-exps)
           (ErrorC (StrC "Bad arguments to -"))))))

(define (desugar-add (args : (listof ExprP))) : ExprC
  (local ([define ids (make-ids (length args))]
          [define id-exps (map IdC ids)])
    (cascade-lets ids (map desugar args)
      (IfC (all (map (lambda (e) (check-type e "number")) id-exps))
		    (map-add-num id-exps)
		    (IfC (all (map (lambda (e) (check-type e "string")) id-exps))
		    	(map-add-string id-exps)
		    	(ErrorC (StrC "Bad arguments to +")))
			) ;; theres a problem here regarding the correct error to be thrown: string vs num
		)
	)
)

(define (desugar-dots (obj : ExprC) (field : ExprC) (args : (listof ExprP))) : ExprC
	(local ([define ids (make-ids (length args))]
          [define id-exps (map IdC ids)])
    (cascade-lets ids (map desugar args)
			(GetFieldC obj field)
		) 
	)
)

(define (desugar-bracks (obj : ExprP) (field : ExprP) (args : (listof ExprP))) : ExprC
	(local ([define ids (make-ids (length args))]
          [define id-exps (map IdC ids)])
    (cascade-lets ids (map desugar args)
			(GetFieldC (desugar obj) (desugar field))
		) 
	)
)



;;(define (desugar-object-fields (fields : (listof FieldP))) : ExprC
;;	(local ([define ids (make-ids (length fields))]
;;          [define id-exps (map IdC ids)])
;;    (cascade-fields id-exps (map desugar-field fields)
;;			(ObjectC id-exps)
;;		) 
;;	)
;;)

(define (desugar-field (field : FieldP)) : FieldC
  (type-case FieldP field
		[fieldP (name value) (fieldC name (desugar value))]
	)
)

;; this. does stuff.
(define (desugar-seq (args : (listof ExprP))) : ExprC
  (local ([define ids (make-ids (length args))]
          [define id-exps (map IdC ids)])
    (cascade-lets ids (map desugar args)
      (map-seq id-exps))))

(define (map-seq (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (expr result) (SeqC result expr)) (first exprs) (rest exprs)))

;; map-add builds an expression that maps 'num over a list of expressions
(define (map-add-num (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (expr result) (Prim2C 'num+ result expr)) (first exprs) (rest exprs)))

;; map-add builds an expression that maps 'num over a list of expressions
(define (map-add-string (exprs : (listof ExprC))) : ExprC
  (foldl (lambda (expr result) (Prim2C 'string+ result expr)) (first exprs) (rest exprs)))

;; yeehaaaa!
(define (map-exprs (exprs : (listof ExprP))) : (listof ExprC)
	(map (lambda (expr) (desugar expr)) exprs))

;;(define (map-fields (fields : (listof FieldP) : (listof FieldC)
	;;(map (lambda (field (

(define (desugar-prim-assign-id (id : symbol) (op : symbol) (value : ExprC)) : ExprC
	(case op
		[(-) (Set!C id (Prim2C 'num- (IdC id) value))]
    [(+) (IfC (check-type (IdC id) "number")
					 	 (IfC (check-type value "number")
						 	 (Set!C id (Prim2C 'num+ (IdC id) value))
							 (ErrorC (StrC "Bad arguments to +"))
						 )
					 	 (IfC (check-type (IdC id) "string")
						 	 (IfC (check-type value "string")
							   (Set!C id (Prim2C 'string+ (IdC id) value))
								 (ErrorC (StrC "Bad arguments to +"))
							 )
							 (ErrorC (StrC "Bad arguments to +"))
						 )
					 )
				 
		]
	)
)

(define (desugar-prim-assign-id-post (id : symbol) (op : symbol) (value : ExprC)) : ExprC
	(case op
		[(-) (Set!C id (Prim2C 'num- (IdC id) value))]
    [(+) (IfC (check-type (IdC id) "number")
					 	 (IfC (check-type value "number")
						 	 (LetC 'tmp (IdC id) 
							 	 (SeqC (Set!C id (Prim2C 'num+ (IdC id) value)) (IdC 'tmp))
							 )
							 (ErrorC (StrC "Bad arguments to +"))
						 )
					 	 (IfC (check-type (IdC id) "string")
						 	 (IfC (check-type value "string")
							   (Set!C id (Prim2C 'string+ (IdC id) value))
								 (ErrorC (StrC "Bad arguments to +"))
							 )
							 (ErrorC (StrC "Bad arguments to +"))
						 )
				)
				 
		]
	)
)

(define (desugar-prim-assign-dot (obj : ExprC) (field : ExprC) (op : symbol) (value : ExprC)) : ExprC
	(case op
		[(-) (SetFieldC obj field (Prim2C 'num- (GetFieldC obj field) value))]
    [(+) (IfC (check-type (GetFieldC obj field) "number")
					 	 (IfC (check-type value "number")
						 	 (SetFieldC obj field (Prim2C 'num+ (GetFieldC obj field) value))
							 (ErrorC (StrC "Bad arguments to +"))
						 )
					 	 (IfC (check-type  (GetFieldC obj field) "string")
						 	 (IfC (check-type value "string")
							   (SetFieldC obj field (Prim2C 'string+ (GetFieldC obj field) value))
								 (ErrorC (StrC "Bad arguments to +"))
							 )
							 (ErrorC (StrC "Bad arguments to +"))
						 )
					 )
				 
		]
	)
)


(define (desugar-prim-assign-brack (obj : ExprC) (field : ExprC) (op : symbol) (value : ExprC)) : ExprC
	(case op
		[(-) (SetFieldC obj field (Prim2C 'num- (GetFieldC obj field) value))]
    [(+) (IfC (check-type (GetFieldC obj field) "number")
					 	 (IfC (check-type value "number")
						 	 (SetFieldC obj field (Prim2C 'num+ (GetFieldC obj field) value))
							 (ErrorC (StrC "Bad arguments to +"))
						 )
					 	 (IfC (check-type  (GetFieldC obj field) "string")
						 	 (IfC (check-type value "string")
							   (SetFieldC obj field (Prim2C 'string+ (GetFieldC obj field) value))
								 (ErrorC (StrC "Bad arguments to +"))
							 )
							 (ErrorC (StrC "Bad arguments to +"))
						 )
					 )
		]
	)
)

(define (desugar (exprP : ExprP)) : ExprC
  (type-case ExprP exprP

    [NumP (n) (NumC n)]
    [StrP (s) (StrC s)]
		[IfP (condP thenP elseP) (IfC (desugar condP) (desugar thenP) (desugar elseP))]
		;; IfP wrong according to if1.psl test. not reaching else case
		[TrueP () (TrueC)]
		[FalseP () (FalseC)]
		[IdP (name) (IdC name)] ;; 1 test
		[FuncP (args body) (FuncC args (desugar body))] ;; 1 test. untested. see specs.
		;;[FuncP (args body) (StrC (to-string exprP))] 

		[SeqP (es) (desugar-seq es)] ;; untested. not right.
		;;[SeqP (es : (listof ExprP))]
		;;[SeqC (e1 : ExprC) (e2 : ExprC)]

		[AppP (func args) (AppC (desugar func) (map-exprs args))] ;; untested. see specs
		;;[AppC (func : ExprC) (args : (listof ExprC))]
		;;[AppP (func : ExprP) (args : (listof ExprP))]

		[DeffunP (name ids funbody body) (LetC name (FuncC ids (desugar funbody)) (desugar body))]
		;;[DeffunP (name : symbol) (ids : (listof symbol)) (funbody : ExprP) (body : ExprP)]
		;;[FuncC (args : (listof symbol)) (body : ExprC)]

		[DefvarP (id bind body) (LetC id (desugar bind) (desugar body))]
		;; [LetC (id : symbol) (bind : ExprC) (body : ExprC)]

		
		;; [DeffunP (name : symbol) (ids : (listof symbol)) (funbody : ExprP) (body : ExprP)]

		[AssignP (lhs value) 
			(type-case LHS lhs
				[BracketLHS (obj field) 
					(LetC 'tmpfield (desugar field)
						(IfC (check-type (IdC 'tmpfield) "string")
							(SetFieldC (desugar obj) (IdC 'tmpfield) (desugar value))
							(IfC (check-type (IdC 'tmpfield) "number")
								(ErrorC (desugar field))
								(ErrorC (Prim2C 'string+ (StrC "test2") (StrC "")))
							)
						)		
					)		
				]
				[DotLHS (obj field) (SetFieldC (desugar obj) (StrC (symbol->string field)) (desugar value))]
				[IdLHS (id) (Set!C id (desugar value))]
			)
		]
		
		;;[BracketLHS (obj : ExprP) (field : ExprP)]

		;; A PrimAssign op is one of '+ '-
		[PrimAssignP (op lhs value)
			(type-case LHS lhs
				[BracketLHS (obj field) 
					(LetC 'tmpfield (desugar field)
						(IfC (check-type (IdC 'tmpfield) "string")
							(desugar-prim-assign-brack (desugar obj) (IdC 'tmpfield) op (desugar value))
							(ErrorC (StrC (string-append "warning " "1")))
						)		
					)	
				]
				[DotLHS (obj field) (desugar-prim-assign-dot (desugar obj) (StrC (symbol->string field)) op (desugar value))]
				[IdLHS (id) (desugar-prim-assign-id id op (desugar value))]
			)
		]

 	  [PostIncP (lhs) (desugar-prim-assign-id-post lhs '+ (NumC 1))] ;;doesnt work
		[PreIncP (lhs) (desugar-prim-assign-id lhs '+ (NumC 1))]
		[PostDecP (lhs) (desugar-prim-assign-id lhs '- (NumC 1))] ;;doesnt work
		[PreDecP (lhs) (desugar-prim-assign-id lhs '- (NumC 1))]

		;;[DotMethodP (obj field args) (StrC (to-string exprP))]
		[DotMethodP (obj field args)  (desugar-dots (desugar obj) (StrC (symbol->string field)) args)]
		;;[DotMethodP (obj field args)  
		;;	(LetC 'obj (desugar obj)
			;;	(LetC 'field (GetFieldC (IdC 'obj) (StrC (symbol->string field)))
				;;	(type-case ExprC (IdC 'field)
					;;	[FuncC (fun-args body) 
						;;	(IfC (Prim2C '== (NumC (length args)) (NumC (length fun-args)))
							;;	(desugar-dots 'obj (StrC (symbol->string field)))
								;;(ErrorC (StrC "Arity mismatch"))
							;;)
						;;]
						;;[else (desugar-dots 'obj (StrC (symbol->string field)))]
					;;)
				;;)
			;;)
		;;]

		[BrackMethodP (obj field args) (desugar-bracks obj field args)]
		
		;; functions are evaluated too many times becuase of not using LetC

		;;[fieldP (name : string) (value : ExprP)])
		;;[fieldC (name : string) (value : ExprC)])
		;;[GetFieldC (obj : ExprC) (field : ExprC)]
	  ;;[SetFieldC (obj : ExprC) (field : ExprC) (value : ExprC)]

		[ObjectP (fields) (ObjectC (map desugar-field fields))]
		;;[ObjectP (fields) (desugar-object-fields fields)]
		;;[ObjectP (fields) (StrC (to-string exprP))]
		;;[ObjectP (fields : (listof FieldP))]
		;;[ObjectC (fields : (listof FieldC))]

		[BracketP (obj field) (GetFieldC (desugar obj) (desugar field))]
		[DotP (obj field) (GetFieldC (desugar obj) (StrC (symbol->string field) ))]
		;;[DotP (obj field) (StrC (to-string exprP))]
	
    ;; Fill in more cases here...

	; An op is one of '+ '- '== 'print '< '>
    [PrimP (op args)
      (case op
      	[(-) (cond
          [(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
          [(< 0 (length args)) (desugar-subtract args)]
				)]
				[(+) (cond
          [(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
          [(< 0 (length args)) (desugar-add args)]
				)]
				[(==) (cond
					[(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
					[(= 2 (length args)) (Prim2C op (desugar (first args)) (desugar (second args)))] 
					[else (ErrorC (StrC "Bad primop"))]
				)]
				[(print) (cond
					[(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
					[(= 1 (length args)) (Prim1C op (desugar (first args)))]
					[else (ErrorC (StrC "Bad primop"))] 
				)]
				[(<) (cond
					[(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
					[(= 2 (length args)) (Prim2C op (desugar (first args)) (desugar (second args)))]
					[else (ErrorC (StrC "Bad primop"))] 
				)]
				[(>) (cond
					[(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
					[(= 2 (length args)) (Prim2C op (desugar (first args)) (desugar (second args)))]
					[else (ErrorC (StrC "Bad primop"))] 
				)]
				[(tagof) (cond
					[(= 0 (length args)) (ErrorC (StrC "Empty list for prim op"))]
					[(= 1 (length args)) (Prim1C op (desugar (first args)))]
					[else (ErrorC (StrC "Bad primop"))] 
				)]
			)
		]

    [WhileP (test body)
          ;; dummy-fun will tell us it was called if we do so accidentally
          (local ([define dummy-fun (FuncC (list) (ErrorC (StrC "Dummy function")))])
          (IfC (desugar test)

               ;; while-var will hold the actual function once we tie
               ;; everything together
               (LetC 'while-var dummy-fun
                 (LetC 'while-func

                   ;; this function does the real work - it runs the body of
                   ;; the while loop, then re-runs it if the test is true, and
                   ;; stops if its false
                   (FuncC (list)
                     (LetC 'temp-var
                       (desugar body)
                       (IfC (desugar test)
                            (AppC (IdC 'while-var) (list))
                            (IdC 'temp-var))))

                   ;; The Set!C here makes sure that 'while-var will resolve
                   ;; to the right value later, and the AppC kicks things off
                   (SeqC (Set!C 'while-var (IdC 'while-func))
                         (AppC (IdC 'while-var) (list)))))

               (FalseC)))]

		[ForP (init test update body)
          ;; dummy-fun will tell us it was called if we do so accidentally
          (local ([define dummy-fun (FuncC (list) (ErrorC (StrC "Dummy function")))])
						(LetC 'for-init (desugar init)
							(LetC 'for-test (desugar test)          		
								(IfC (IdC 'for-test)
			           (LetC 'for-var dummy-fun
			             (LetC 'for-func
			               
											(FuncC (list)
					              (LetC 'for-body (desugar body)
													(LetC 'for-update (desugar update)
														(LetC 'for-test (desugar test)
  						              	(IfC (IdC 'for-test)
						                    (AppC (IdC 'for-var) (list))
						                    (IdC 'for-body)
													 		)
														)
													)
												)
											)
	
				              (SeqC (Set!C 'for-var (IdC 'for-func))
										 	 	 (AppC (IdC 'for-var) (list))
											)
										)
									)
									(IdC 'for-init)
								)
							 )
						 )
						)
					
		]

	)
)

