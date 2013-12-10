(letrec (main-loop
	(lambda ()
		(begin
			(display "Enter a numerator and denominator: ")
			(let (div (lambda (x y)
									(if (= y 0)
										(throw "division by zero")
										(/ x y)
									)
								)
						)
					(catch (div (read) (read)) in e (begin 
																									(display e) 
																									(display "\n")
									(main-loop)))))))
									(main-loop))