/-!
# Homework 6

The established rules apply. Do this work on your own.

This homework will test and strengthen your understanding
of inductive data types, including Nat and List α, and the
use of recursive functions to process and construct values
of such types.

The second part will test and develop your knowledge and
understanding of formal languages, and propositional logic,
(PL) in particular, including the syntax and semantics of
PL, and translations between formal statements in PL and
corresponding concrete English-language examples.
-/

/-! 
## Part 1: Inductive Types and Recursive Functions
-/

/-! 
### #1: Iterated Function Application 

Here are two functions, each of which takes a function,
*f*, as an argument, and an argument, *a*, to that function, 
and returns the result of applying *f* to *a* one or more
times. The first function just applies *f* to *a* once. The
second function applies *f* to *a* twice. Be sure you fully
understand these definitions before proceeding. 
-/

def apply {a : α} : (α → α) → α → α 
| f, a => f a

def apply_twice {a : α} : (α → α) → α → α 
| f, a => f (f a)

/-!
Your job now is to define a function, *apply_n*, that takes
a function, *f*, a natural number,  *n*, and an argument, 
*a*, and that returns the result of applying *f* to *a n* 
times. Define the result of applying *f* to *a* zero times
as just *a*. Hint: recursion on *n*. That is, you will have
two cases: where *n* is *0*; and where *n* is greater than 
*0*, and can thus be written as *(1 + n')* for some smaller
natural number, *n'*.
-/

-- Answer here

def apply_n {α : Type} : (α → α) → α → Nat → α  
| f, a, 0 => a
| f, a, (n' + 1) => f (apply_n f a n')

-- Test cases: confirm that expectations are correct

-- apply Nat.succ to zero four times
#eval apply_n Nat.succ 0 4        -- expect 4

-- apply "double" to 2 four times
#eval apply_n (λ n => 2*n) 2 4    -- expect 32

-- apply "square" to 2 four times
#eval apply_n (λ n => n^2) 2 4    -- expect 65536


/-! 
### #2: List length function

Lists are defined inductively in Lean. A list of
values of some type α is either the empty list of
α values, denoted [], or an α value followed by a
shorter list of α values, denoted *h::t*, where 
*h* (the *head* of the list) is a single value of
type α, and *t* is a shorter list of α values. 
The base case is of course the empty list. Define 
a function called *len* that takes a list of 
values of any type, α, and that returns the length
of the list.
-/

def len {α : Type} : List α → Nat
| [] => 0
| h::t => .succ (len t)

#eval @len Nat []                   -- expect 0
#eval len [0,1,2]                   -- expect 3
#eval len ["I", "Love", "Logic!"]   -- expect 3


/-! 
### #3: Reduce a List of Bool to a Bool

Define a function that takes a list of Boolean 
values and that "reduces" it to a single Boolean
value, which it returns, where the return value
is true if all elements are true and otherwise
is false. Call your function *reduce_and*. 

Hint: the answer is the result of applying *and* 
to two arguments: (1) the first element, and (2) 
the result of recursively reducing the rest of the 
list. You will have to figure out what the return
value for the base case of an empty list needs to
be for your function to work in all cases. 
-/

def reduce_and : List Bool → Bool
| [] => true
| h::t => and h (reduce_and t)

-- Test cases

#eval reduce_and [true]           -- expect true
#eval reduce_and [false]          -- expect false
#eval reduce_and [true, true]     -- expect true
#eval reduce_and [false, true]    -- expect false


/-! 
### #4 Negate a List of Booleans 

Define a function, call it (map_not) that takes a 
list of Boolean values and returns a list of Boolean
values, where each entry in the returned list is the
negation of the corresonding element in the given
list of Booleans. For example, *map_not [true, false]*
should return [false, true].
-/

def map_not : List Bool → List Bool 
| [] => []
| h::t => (not h)::(map_not t)   -- hint: use :: to construct answer

-- test cases
#eval map_not []              -- exect []
#eval map_not [true, false]   -- expect [false, true]

/-! 
### #5 List the First n Natural Numbers

Define a function called *countdown* that takes a 
natural number argument, *n*, and that returns a list 
of all the natural numbers from *n* to *0*, inclusive. 
-/

-- Your answer here

def countdown : Nat → List Nat
| 0 => 0::[]
| (n + 1) => (.succ n)::(countdown n)

-- test cases
#eval countdown 0            -- expect [0]
#eval countdown 5            -- expect [5,4,3,2,1,0]


/-! 
### #6: List concatenation 

Suppose Lean didn't provide the List.append function,
denoted *++*. Write your own list append function. Call
it *concat*. For any type *α*, it takes two arguments of 
type *List α* and returns a result of type *List α,* the
result of appending the second list to the first. Hint:
do case analysis on the first argument, and think about
this function as an analog of natural number addition.
-/

-- Here

def concat {α : Type} : List α → List α → List α 
| [], m => m
| t::g, m => t::(concat g m) 

-- Test cases

#eval concat [1,2,3] []   -- expect [1,2,3]
#eval concat [] [1,2,3]   -- expect [1,2,3]
#eval concat [1,2] [3,4]  -- expect [1,2,3,4]

/-!
### #7: Lift Element to List

Write a function, *pure'*, that takes a value, *a*, of any
type α, and that returns a value of type List α containing
just that one element.
-/

-- Here

def pure' : α → List α 
| a => a::[] 

#eval pure' "Hi"       -- expect ["Hi"]


/-!
### Challenge: List Reverse

Define a function, list_rev, that takes a list of values
of any type and that returns it in reverse order. Hint: you 
can't use :: with a single value on the right; it needs a
list on the right. Instead, consider using *concat*.
-/

-- Answer here:

def list_rev : List α → List α
| [] => []
| a::t => concat (list_rev t) (pure' a)

#eval list_rev [1, 2, 3, 4]

/-!
## Part 2: Propositional Logic: Syntax and Semantics



## HOMEWORK: 

Refer to each of the problems in HW5, Part 1. 
For each one, express the proposition that each function
type represents using our formal notation for propositional
logic. We'll take you through this exercise in steps. 
-/

structure var : Type := 
(n: Nat)

inductive unary_op : Type
| not

inductive binary_op : Type
| and
| or
| imp
| iff

inductive Expr : Type
| var_exp (v : var)
| un_exp (op : unary_op) (e : Expr)
| bin_exp (op : binary_op) (e1 e2 : Expr)

notation "{"v"}" => Expr.var_exp v
prefix:max "¬" => Expr.un_exp unary_op.not 
infixr:35 " ∧ " => Expr.bin_exp binary_op.and  
infixr:30 " ∨ " => Expr.bin_exp binary_op.or 
infixr:25 " ⇒ " =>  Expr.bin_exp binary_op.imp
infixr:20 " ⇔ " => Expr.bin_exp binary_op.iff 

def eval_un_op : unary_op → (Bool → Bool)
| unary_op.not => not

def eval_bin_op : binary_op → (Bool → Bool → Bool)
| binary_op.and => and
| binary_op.or => or
| binary_op.imp => fun c d => match c, d with | true, false => false | _, _ => true
| binary_op.iff => fun c d => match c, d with | true, true | false, false => true | _, _ => false

def Interp := var → Bool  

def eval_expr : Expr → Interp → Bool 
| (Expr.var_exp v),        i => i v
| (Expr.un_exp op e),      i => (eval_un_op op) (eval_expr e i)
| (Expr.bin_exp op e1 e2), i => (eval_bin_op op) (eval_expr e1 i) (eval_expr e2 i)

/-!
### #1. Propositional Variables

First, define *b, c,* *j,* and *a* as propositional variables
(of type *var*). We'll use *b* for *bread* or *beta*,* *c* for 
*cheese,* *j* for *jam,* and *a* for α*. 
-/

def b := var.mk 0
def j := var.mk 1
def c := var.mk 2
def a := var.mk 3

-- get the index out of the c structure
#eval c.n

/-!
### #2. Atomic Propositions

Define B, C, J and A as corresponding atomic propositions,
of type *Expr*. 
-/

def B := {b}     
def C := {c}
def J := {j}
def A := {a}

/-!
### #3. Compound Propositions

Now redefine the function names in HW5 in propositional logic (Expr)
-/

def e0 := (¬J ∨ ¬C) ⇒ ¬(J ∧ C)
def demorgan1 := (¬J ∨ ¬C) ⇒ ¬(J ∧ C)
def demorgan2 := ¬(A ∨ B) ⇒ (¬A ∧ ¬B)
def demorgan3 := (¬J ∧ ¬C) ⇒ ¬(J ∨ C)

/-!
### #4. Implement Syntax and Semantics for Implies and Biimplication
Next go back and extend our formalism to support the implies connective.
Do the same for biimplication while you're at it. This is already done 
for *implies*. Your job is to do the same for bi-implication, which
Lean does not implement natively. 
-/


/-!
### #5. Evaluate Propositions in Various Worlds

Now evaluate each of these expressions under the all_true and all_false
interpretations. These are just two of the possible interpretations so
we won't have complete proofs of validity, but at least we expect them
to evaluate to true under both the all_true and all_false interpretations.
-/

#eval eval_expr e0 (λ _ => false) -- expect true
#eval eval_expr e0 (λ _ => true)  -- expect true

-- You do the rest
#eval eval_expr demorgan1 (λ _ => false) -- expect true
#eval eval_expr demorgan1 (λ _ => true) -- expect true

#eval eval_expr demorgan2 (λ _ => false) -- expect true
#eval eval_expr demorgan2 (λ _ => true) -- expect true

#eval eval_expr demorgan3 (λ _ => false) -- expect true
#eval eval_expr demorgan3 (λ _ => true) -- expect true


/-!
### #6. Evaluate the Expressions Under Some Other Interpretation

Other than these two, evaluate the propositions under your new
interpretation, and confirm that they still evaluate to true.
Your interpretation should assign various true and false values
to *j, c, b,* and *a.* An interpretation has to give values to
all (infinitely many) variables. You can do case analysis by
pattern matching on a few specific variables (by index) then 
use wildcard matching to handle all remaining cases.
-/

-- Answer here
def isodd : Nat → Bool
| 0 => false
| 1 => true
| n + 2 => isodd n

def oddtrue : var → Bool
| n => isodd n.n

def custom_interp : var → Bool
| v => match v.n with 
  | 0 => true
  | 1 => false
  | 2 => false
  | 3 => true
  | _ => false
  
def custom_interp' : var → Bool
| v => match v.n with 
  | 0 => true
  | 1 => false
  | 2 => false
  | 3 => true
  | _ => false

#eval eval_expr e0 custom_interp -- expect true
#eval eval_expr e0 oddtrue -- expect true

-- You do the rest
#eval eval_expr demorgan1 custom_interp -- expect true
#eval eval_expr demorgan1 oddtrue -- expect true

#eval eval_expr demorgan2 custom_interp -- expect true
#eval eval_expr demorgan2 oddtrue -- expect true

#eval eval_expr demorgan3 custom_interp -- expect true
#eval eval_expr demorgan3 oddtrue -- expect true


