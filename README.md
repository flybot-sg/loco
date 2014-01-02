# loco

A Constraint Programming library. This is a Clojure wrapper of the Java library "Choco".
This library is the rebirth of "CloCoP", a wrapper of JaCoP, and since then I've switched the
underlying Java library (and made some general improvements to my API for CP in Clojure).

The name "Constraint Programming" represents a set of problems that can be expressed by a series of
constraints. What's interesting about these problems is that solutions are very easy to check, but not
very easy to find. For example, if I have the constraint "(X * 3) mod (Y ^ 5) = 4", it's very easy
to verify that this fact holds (given an X and a Y), but not nearly as easy to come up with an X and a Y that
satisfy the rule. The idea of Constraint Programming, however, is to find a way to come up with these solutions,
presumably much faster than brute force.

#### But what about core.logic?

You may start to notice a suspicious similarity to core.logic. I agree that both serve as finite-domain solvers,
but in my opinion, loco is a better choice for solving finite-domain problems:
- loco has a better suite of constraints (including arithmetic, logic, and global constraints) tailored to
more challenging problems.
- loco is significantly faster at solving most problems, because it has a more low-level finite-domain engine
underneath.


## Usage

(Insert lein dependency here)

Here is a sample problem written in Loco:

	(defn sample-problem
	  []
	  (let [s (solver "sample_problem")
	        x (int-var s "x" 1 5)
	        y (int-var s "y" 2 6)]
	    (constrain! s
	      ($= ($+ x y) 10)
	      ($= x y))
	    (solution s)))
	=>
	{"x" 5, "y" 5}

## API

#### The solver

The "solver" is essentially a container for all of the variables and constraints in your CP problem.
Calls to <code>int-var</code> and <code>constrain!</code> require that the corresponding solver be the first argument.
You can create a solver using <code>loco.core/solver</code>:

	(solver "mySolver")
	(solver)

#### Creating vars

In Loco, the only type of variable is an integer variable, or "int-var" for short.
Every int-var has its own domain, which is a finite set of integers.
The default type of int-var (an enumerated int-var) keeps track of its domain using a Bit Set.
However, a "bounded int-var" is a variation on this concept, which keeps track of only a minimum and a maximum of
the domain. It provides a trade-off between memory and running time (decreasing memory usage but increasing running time).
I recommend sticking with the enumerated variables unless you are running low on memory.

To create an int-var, use the <code>loco.core/int-var</code> function:

	(int-var solver name? min max)
	(int-var solver name? values)
	(int-var solver name? min max :bounded)
	Examples:
	(def s (solver))
	(int-var s "a" 1 5)
	(def b (int-var s 1 5))
	(int-var s "c" [1 2 3 4 5])
	(int-var s "d" 1 5 :bounded)

In all cases, the "name" field is optional.

A "boolean var" (or "bool-var") is an int-var that has the domain #{0, 1}. You can create one with

	(bool-var solver name?)
	


#### Creating constraints

All constraints are in the <code>loco.constraints</code> namespace. Also, the functions that generate the constraints
all begin with <code>$</code> (e.g. <code>$=</code> for "=", <code>$all-different?</code> for "all different", etc.) so
that you can safely call <code>(use 'loco.constraints)</code> without overlap with clojure.core functions.

Note that some of these functions don't actually return
constraints, but will generate new variables to be used in constraints. For example, you'd never call
<code>(constrain! ($+ x y))</code>, but you might call <code>(constrain! ($= ($+ x y) 2))</code>. Also note
that these variable-generators don't generate the variables immediately; they return a data structure to be
interpreted by the <code>constrain!</code> function later.

Here is a complete list of all of the constraints available to you.
- <code>$+</code> - given a mixture of variables / numbers, returns the sum.
- <code>$-</code> - given a mixture of variables / numbers, returns <code>X - Y - Z - ...</code>,
or <code>-X</code> if only one argument is given.
- <code>$*</code> - given two arguments (one of which is allowed to be a number >= -1), returns the product.
- <code>$min</code> - returns the minimum of several arguments.
- <code>$max</code> - returns the maximum of several arguments.
- <code>$mod</code> - given two arguments X and Y, returns X mod Y.
- <code>$scalar</code> - given a list of variables (X, Y, Z, ...) and a list of integer coefficients (a, b, c, ...)
returns <code>aX + bY + cZ + ...</code>.

- <code>$=, $<, $>, $<=, $>=, $!=</code> - constraints that specify equality/inequality between two or more arguments.
Calling these on more than one argument will return a composition of multiple constraints (which has the
same functionality, but might be less efficient then you'd like).

- <code>$and</code> - given zero or more constraints, returns another constraint that is the "and" of the subconstraints,
i.e. it is true iff all of the subconstraints is true.
- <code>$or</code> - given zero or more constraints, returns another constraint that is the "or" of the subconstraints,
i.e. it is true iff at least one of the subconstraints is true.
- <code>$not</code> - given one constraint C, returns another constraint that is the "not" of C, i.e. it is true
iff C is false.
- <code>$true, $false</code> - takes no arguments, returns an "always true" or an "always false" constraint, respectively.
- <code>$if</code> - takes an "if", a "then", and optionally an "else", and returns an implies statement.
Given P and Q, returns P => Q, i.e. P or ~Q. Given P, Q, and R, returns (P => Q) ^ (~P => R).
- <code>$cond</code> - takes several if-then pairs (as one would use in <code>cond</code>), and composes together
several <code>$if</code> constraints. The final "else" clause can be specified with <code>:else</code> (like in <code>cond</code>),
or put as the last argument (like in <code>case</code> and <code>condp</code>). This function is mostly syntactic sugar, and not
more efficient than composing the <code>$if</code> statements manually.

- <code>$reify</code> - given a constraint C, will generate a boolean var V, such that V = 1 iff C.
- <code>$all-different?</code> - a constraint that specifies that several variables must end up with different values.
- <code>$circuit?</code> - a constraint that specifies that a given list L is a circuit, i.e. each item in the list
contains the index of the next item in the circuit. For example, <code>[1 2 3 4 0]</code> is a circuit because
<code>L[0]</code> contains 1, <code>L[1]</code> contains 2, <code>L[2]</code> contains 3, and if you follow the chain you'll
eventually visit every index once. You can also pass in an offset number to add to the indices (e.g. if you want to make the
array one-based).
- <code>$nth</code> - given a list L and an index i (a variable), will generate another variable that equals <code>L[i]</code>.
- <code>$satisfies-automaton?</code> - given an automaton (created with the following function) and a list of variables, returns
a constraint that specifies that the variables in sequence must satisfy the automaton.
- <code>$automaton</code> - given a regular-expression-style string, returns a finite automaton to be used in <code>satisfies-automaton?</code>.
Example: <code>($automaton "(1|2)(3*)(4|5)")</code> means that a sequence of variables begins with 1 or 2, followed by
any number of 3's, ended with a 4 or 5. All digits (0-9) are treated as the numbers themselves, and any other character
(that isn't a paren, bar, star, plus, etc)
is treated as its unicode number. e.g. to write the number 10, you'd have to write <code>\u000A</code> (hex for 10).

#### Finding solutions

It's no fun to set up your variables and constraints and then not have a way to find the solution. There are a few
ways to find solutions:

Calling <code>(solve! solver)</code> will return true if it finds a solution and false if not. If it did find a solution,
you can call <code>(get-val x)</code> on all of the variables you wish to find the values of.

	(let [s (solver "sample")
	      x (int-var s "x" 1 5)]
	  (constrain! s ($= x 1))
	  (solve! s)
	  (get-val x))
	=> 1

You can also call <code>solve!</code> with keyword argument <code>:minimize</code> or <code>:maximize</code>.

	(let [s (solver "sample")
          x (int-var s "x" 1 5)]
      (constrain! s ($> x 2))
      (solve! s :minimize x)
      (get-val x))
    => 3
    
Note that if you minimize/maximize a variable and there is no solution, the solver will find a solution that bypasses
one or more of the constraints. This idiosyncrasy is built-in to the underlying Java library and thus beyond my control.

One more thing I need to mention about <code>solve!</code> is that you call it multiple times (when you aren't minimizing/maximizing).
Each successive call to <code>solve!</code> will set the variables to a new solution, returning false when it's out of solutions.

The next way to find a solution is to call <code>(solution solver)</code>. It calls <code>solve!</code> and then returns a map,
whose keys are the names
of variables that you gave names to, and whose vals are their values. It behaves like <code>solve!</code> in that
you can call it multiple times, or pass in variables to optimize.

	(let [s (solver "sample")
	      x (int-var s "x" 1 5)]
	  (constrain! s ($> x 2))
	  (solution s :minimize x))
	=> {:x 3}

Finally, you can find a lazy sequence of solution maps to all solutions, via <code>(solutions solver)</code>.
Solution maps have metadata attached with the keyword <code>:loco/solution</code> denoting the nth solution
(starting with 0). Don't call <code>solutions</code> more than once, as the second call to it will most likely
return an empty list (or have even more awkward behavior if the first result hasn't been fully realized yet).

#### Fun facts / common idioms

First of all, you can use the names of variables (as strings, keywords, or symbols) anywhere you would put the variable
itself. This includes inside constraints, and in uses of the <code>:minimize/:maximize</code> keyword.

You can also pass arithmetic to the optimizers, e.g. <code>(solve! s :minimize ($+ x y))</code>. Using this feature
with <code>$scalar</code> allows you to emulate Mixed Integer Programming (e.g. Linear Programming with integer variables).

Here is an example of using threading macros to avoid passing a solver to too many function calls.

	(-> (solver "sample")
	  (doto
	    (int-var "x" 1 4)
	    (int-var "y" 2 5)
	    (constrain! ($= ($* :x :y) 15)))
	  (solutions))
	=> ({"x" 3, "y" 5})

You may assume that this library is pretty slow for significant problems,
given that it takes 5-10 milliseconds for a small problem. However, there is significant overhead attached to the
process of creating the variables and constraints, mostly because of the usage of Clojure data structures to simplify
the user interface. But once the lower-level Java library underneath kicks in, it's much faster to actually find
solutions.

## License

Copyright © 2013 FIXME

Distributed under the Eclipse Public License, the same as Clojure.
