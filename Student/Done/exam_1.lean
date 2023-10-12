/-!
# UVa CS2120-002 F23 Midterm Exam

The first section of this exam just repeats our definition
of propositional logic syntax and semantics. Skip ahead to
the second section to find the exam.

## Propositional Logic: Syntax, Sematics, Satisfiability

This section of the exam simply includes our formal 
definition of the syntax and semantics of propositional
logic and of functions that determine whether a given 
expression is valid, satisfiable, or unsatisfiable.

### Syntax
-/

-- variables
structure var : Type :=  (n: Nat)

-- connectives/operators
inductive unary_op : Type | not
inductive binary_op : Type
| and
| or
| imp
| iff

-- expressions (abstract syntax)
inductive Expr : Type
-- Extra credit answers here
| var_exp (v : var)
| un_exp (op : unary_op) (e : Expr)
| bin_exp (op : binary_op) (e1 e2 : Expr)
| top_exp
| bot_exp

-- concrete syntax 
notation "{"v"}" => Expr.var_exp v
prefix:max "¬" => Expr.un_exp unary_op.not 
infixr:35 " ∧ " => Expr.bin_exp binary_op.and  
infixr:30 " ∨ " => Expr.bin_exp binary_op.or 
infixr:25 " ⇒ " =>  Expr.bin_exp binary_op.imp
infixr:20 " ⇔ " => Expr.bin_exp binary_op.iff 
notation " ⊤ " => Expr.top_exp
notation " ⊥ " => Expr.bot_exp


/-!
### Semantics
-/

-- meanings of unary operators
def eval_un_op : unary_op → (Bool → Bool)
| unary_op.not => not

-- missing binary Boolean operators
def implies : Bool → Bool → Bool
| true, false => false
| _, _ => true

def iff : Bool → Bool → Bool
| true, true => true
| false, false => true
| _, _ => false

-- meanings of binary operators
def eval_bin_op : binary_op → (Bool → Bool → Bool)
| binary_op.and => and
| binary_op.or => or
| binary_op.imp => implies
| binary_op.iff => iff

-- The interpretation type
def Interp := var → Bool 

-- The meanings of expressions "under" given interpretations
def eval_expr : Expr → Interp → Bool 
-- Extra credit answers here
| (Expr.var_exp v),        i => i v
| (Expr.un_exp op e),      i => (eval_un_op op) (eval_expr e i)
| (Expr.bin_exp op e1 e2), i => (eval_bin_op op) (eval_expr e1 i) (eval_expr e2 i)
| (Expr.top_exp),          _ => true
| (Expr.bot_exp),       _ => false

/-!
### Satisfiability

We built a satisfiability checker for propositional logic,
in several pieces. This subsection includes all definitions.

#### Truth Table Input Rows 
-/

-- Nat to Binary
-- You don't need to worry about the "have" part
def right_bit (n : Nat) := n%2
def shift_right (n : Nat) := n/2
def nat_to_bin : Nat → List Nat
| 0     => [0]
| 1     => [1]
| n' + 2 =>
  have : (shift_right (n' + 2)) < (n' + 2) := sorry
  nat_to_bin (shift_right (n' + 2)) ++ [right_bit (n' + 2)]

-- Left pad with zeros
def zero_pad : Nat → List Nat → List Nat
  | v, l => zero_pad_recursive (v - (l.length)) l
where zero_pad_recursive : Nat → List Nat → List Nat
  | 0, l => l
  | v'+1, l => zero_pad_recursive v' (0::l)

-- Make row of bits at index "row" padded out to "cols" wide 
def mk_bit_row : (row: Nat) → (cols : Nat) → List Nat
| r, c => zero_pad c (nat_to_bin r)

-- Convert list of bits to list of bools
def bit_to_bool : Nat → Bool
| 0 => false
| _ => true

def bit_list_to_bool_list : List Nat → List Bool
| [] => []
| h::t => (bit_to_bool h) :: (bit_list_to_bool_list t)

-- Make row'th row of truth table with vars variables
def mk_row_bools : (row : Nat) → (vars : Nat) → List Bool
| r, v => bit_list_to_bool_list (mk_bit_row r v)

/-!
#### Interpretations
-/

-- Convert list of bools to interpretation
def override : Interp → var → Bool → Interp
| old_interp, var, new_val => 
  (λ v => if (v.n == var.n)     -- when applied to var
          then new_val          -- return new value
          else old_interp v)  -- else retur old value

def bools_to_interp : List Bool → Interp
  | l => bools_to_interp_helper l.length l
where bools_to_interp_helper : (vars : Nat) → (vals : List Bool) → Interp
  | _, [] => (λ _ => false)
  | vars, h::t =>
    let len := (h::t).length
    override (bools_to_interp_helper vars t) (var.mk (vars - len)) h 

-- Make an interpretation for given row with "vars" variables
def mk_interp_vars_row : (vars: Nat) → (row: Nat) → Interp
| v, r => bools_to_interp (mk_row_bools r v)

-- Given number of variables, return list of interpretations
def mk_interps (vars : Nat) : List Interp := 
  mk_interps_helper (2^vars) vars
where mk_interps_helper : (rows : Nat) → (vars : Nat) → List Interp
  | 0, _         => []
  | (n' + 1), v  => (mk_interp_vars_row v n')::mk_interps_helper n' v

-- Count the number of variables in a given expression
def max_variable_index : Expr → Nat
| Expr.var_exp (var.mk i) => i
| Expr.un_exp _ e => max_variable_index e
| Expr.bin_exp _ e1 e2 => max (max_variable_index e1) (max_variable_index e2)
| Expr.top_exp => 0
| Expr.bot_exp => 0

def num_vars : Expr → Nat := λ e => max_variable_index e + 1

/-!
#### Truth Table Output Column
-/ 
def eval_expr_interps : List Interp → Expr → List Bool
| [], _ => []
| h::t, e => eval_expr_interps t e ++ [eval_expr e h]

-- Given expression, return truth table outputs by ascending row index
def truth_table_outputs : Expr → List Bool
| e =>  eval_expr_interps (mk_interps (num_vars e)) e

/-!
### Satisfiability Checkers
-/

-- functions to check if bool list has any, resp. all, values true
def reduce_or : List Bool → Bool 
| [] => false
| h::t => or h (reduce_or t)

def reduce_and : List Bool → Bool 
| [] => true
| h::t => and h (reduce_and t)

-- Three main functions: test given expression for satsfiability properties
def is_sat : Expr → Bool := λ e : Expr => reduce_or (truth_table_outputs e)
def is_valid : Expr → Bool := λ e : Expr => reduce_and (truth_table_outputs e)
def is_unsat : Expr → Bool := λ e : Expr => not (is_sat e)


/-!
****************
****************
EXAM STARTS HERE
****************
****************
-/

/-!
## #1 Proofs as Programs 

### a. And elimination [15 points]

Prove, by completing the following function definition, that 
from a value of type α × β one can always derive a value of 
type α.
-/

-- Your answer here

def and_elimination {α β : Type} : α × β → α 
| (a, _) => a

/-!
### b. Funny transitivity [15 points]

Prove, by completing the following function definition, that
(α → β) × (β → γ) → (α → γ). In other words, if you have a
pair of functions, one converting α to β and one converting
β to γ, then you can always construct a function from α to γ.
Hint: Use type-guided top-down programming, and remember how
to express a *function* value: that's what you have to return
in this case.
-/

-- Your answer here

def funny_transitivity {α β γ : Type} : (α → β) × (β → γ) → (α → γ)
| (a, b) => fun c => b (a c)


/-!
### c. Ex empty quodlibet [15 points]

Prove that if a type, α, is uninhabited then from an 
assumed value (a : α) one can always derive a value of 
*any* type, β. 
-/

-- Your answer here

def ex_empty {α β : Type} : (α → Empty) → α → β
| f, a => nomatch f a

/-!
## #2 Data Types

### a. Enumerated Types [10 points]

Define three enumerated types, called Bread, Spread, 
and Cheese, where the values of type Bread are white and 
wheat; the values of type Spread are jam and pesto;
and the values of type Cheese are cheddar and brie.
-/
namespace Hungry
-- Your answers here
inductive Bread 
| white
| wheat

inductive Spread
| jam
| pesto

inductive Cheese
| cheddar
| brie -- I love brie 😊

/-!
### b. An interesting inductive type [15 points]

Define a data type called Sandwich, with one constructor
called mk, taking as its arguments a choice of bread and 
*either (but not both)* a choice of Cheese or a choice of
Spread. Hint: Remember how to define a type that carries 
a value of either one type or another. Extra credit [2pts]
for using *structure* instead of *inductive* to declare 
the Sandwich type.
-/

-- Your answer here

structure Sandwich : Type := (b:Bread) (t: Spread ⊕ Cheese)

/-
### c. Now make yourself a Sandwich [15 points]

Define jam_sandwhich to be a Sandwhich made with 
wheat bread and jam. You have to use Sandwich.mk 
to create a term representing a sandwich with wheat
bread and jam as a spread.
-/

-- Your answer here

def jam_sandwich : Sandwich := Sandwich.mk Bread.wheat (.inl Spread.jam)


/-! 
### #3 Recursive Data and Functions [15 points]

In our implementation of propositional logic, we defined a 
function, *bit_list_to_bool_list*, to convert a list of Nat 
to a corresponding list of Bool. Here's the definition (with
a tick mark on the name).
-/

def bit_list_to_bool_list' : List Nat → List Bool
| [] => []
| h::t => (bit_to_bool h) :: (bit_list_to_bool_list t)

-- expect [true, false, true, false, true]
#eval bit_list_to_bool_list [1, 0, 3, 0, 1]

/-!
Your job is to generalize this solution by defining a new
function, called *map*. Generalize the types, Nat and Bool,
to arbitrary types, α and β. Generalize *bit_to_bool* to 
be any function for converting an individual α value into
a corresponding β value. Your map function will thus take
as its arguments (1) type parameters (make them implicit), 
(2) a function for converting elements, and (3) a List of 
α values, and will return a correspond List of β values.  
-/

-- Your answer here

def map {α β : Type} (f: (α → β)) : List α → List β
| [] => []
| a::t => (f a)::(map f t)

-- test case: use map instead of bit_list_to_bool_list
-- expect [true, false, true, false, true]
#eval map bit_to_bool [1, 0, 1, 0, 1]

/-!
## #4 Propositional Logic [10 pts Extra Credit, for A+]

Propositional logic as we've formulate it has variable
expressions (atomic expressions), and larger expressions
built by applying connectives (∧, ∨, ¬, ⇒, ⇔) to smaller
expressions. 

Some formalizations of propositional logic also include
the *constant* expressions *True* and *False*. In concrete
syntax, they are sometimes written as ⊤ (pronounced *top*) 
and ⊥ (bottom). Semantically ⊤ evaluates to Boolean true
and ⊥ evaluates to Boolean false.

### a. Extend Syntax and Semantics

Your job is to extend our syntax and semantics to include
⊤ and ⊥ as valid expressions. You will have to carry out
the following tasks.

- add top_exp and bottom_exp as constructors in Expr
- note that we've already added concrete notation definitions
- add rules for evaluating these expressions to eval_expr
- add rules for these expressions to max_variable_index

When you're done, the following logic should evaluate 
without error.
-/

def X := {var.mk 0}
#eval num_vars (X ⇒ ⊥)
#eval is_sat (X ⇒ ⊥)  -- expect true
/-! 
### b. Give a model for (X ⇒ ⊥)

Recall that a model is a binding of values to variables
that makes a proposition true. What value must X have to
make (X ⇒ ⊥) true?

-- Answer: {X is false } is a model of (X ⇒ ⊥)
-/
#eval is_valid (⊥ ⇒ ⊥)
