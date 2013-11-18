

## Lecture 7 - Functions Intro ##

### Function Test Cases ###

What happens...

 - in 'normal' cases where we call a natural-seeming function and it does its thing
 - when a function calls another function
 - when a function calls itself (requires conditionals)
 - when a function does not use its parameters
 - when a function uses its parameter twice (how can we tell?)
 	- look for multiple references to the identifier. it will always have one binding site where it's defined, but it may be referenced multiple times
 - when a function's 'actual parameter' is an identifier
 - when we try to use an identifier that is not bound anywhere
 - when we try to use an identifier that's bound in the function that calls the current function
 	- if this is allowed, it means our language has dynamic scope for identifiers. in other words, an identifier binding made in a particular part of the program may be used in a totally unrelated part of the program just because this part of the program calls a function in that part (or calls a function that calls a function that....
 - how could we tell the different between lazy and eager evaluation semantics? can we teset for the appropriate semantics? what do we need to be able to do such a test?
 	

### Learning Goals ###

- Explain in context four of the key features of a function
 - delaying evaluation of the function body
 - allowing evaluation of the function body from (possibly distant) locations in the program
 - blocking out bindings from the function's dynamic context
 - "allowing in" a dynamica value vai the parameters

- Formal parameters vs. actual parameters
 - distinguish between formal and actual parameters
 	- formal parameters are the names give to argument values within the function
 	- actual parameters are the argument expressions whose values (under eager evaluation) are bound to the formal parameters
 - identify formal and actual parameters in context

- Function calls vs function definitions
 - distinguish between a function call (aka function 'application') and a function 'definition'
 	- a function call is application of a previously defined function to actual parameters, which causes the function body to be evaluated.
 	- a function definition creates a function (prepares it to be used) with formal parameters and a body but does not evaluate the body yet
 - identify function calls and definitions in context

 - Bound vs unbound identifiers
  - define bound and unbound identifier, including illustrating their meanings with examples
  - identify bound and unbound identifiers in context
  - define scope with respect to identifier
  	- the scope of an identifier's binding is the protion of the program in which that binding is visible. In Racket, bindings use lexical (aka static) scope. However, Racket does have a facility for something like dynamic scope.

 - Eager evaluation vs lazy evaluation
  - Explain the basic different between lazy and eager evaluation.
  	- in lazy evaluation, actual parameters are not evaluated before proceeding with a function call. Formal parameters are bound to the actual parameter expressions, not their values.
  	- in eager evaluation, actual parameters are evaluated prior to proceeding with a function call, and the function's formal parameters are bound to the resulting values.
  - be able to distinguish between lazy and eager evaluation regimes by evaluating (and possibly providing a test case that behaves differently under the two regimes
  - alter existing substitution and interpreter code to switch back and forth between lazy and eager evaluation regimes
  	
  
