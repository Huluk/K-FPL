/*!
\title{FPL}
\author{Lars Hansen}
*/

require "fpl_value.k"
require "fpl_name.k"
require "fpl_need.k"

require "ans_rules.k"

module FPL-SYNTAX
  /*@

  This is a functional language with three different methods
  of function evaluation:

  1. Call by Value: Parameters are reduced to base values,
                    then assigned to the argument variables.
  2. Call by Name: In the function body, argument names are
                  substituted with parameter values.
  3. Call by Need: Parameters are assigned to argument values
                  and only evaluated on usage. Once evaluated,
                  the value is stored instead of the expression.

  Call by Value functions are eagerly evaluated, Call by Name and
  Call by Need are lazyly evaluated.

  FPL currently has the following features:
  - variable assignment (no override, all 3 evaluation methods)
  - variable lookup
  - standard arithmetics (+,-,*,/) (call by need)
  - branching (if, including comparison operator <)
  - anonymous functions (all 3 evaluation methods)
  - named functions (all 3 evaluation methods)
  - eager lists (including predefined functions empty,head and tail)

  To demonstrate the different evaluation styles,
  this language also includes pre-increment ++x,
  thereby introducing side effects to the language.
  It is noteworthy that pre-increment may also be skipped
  in lazy-evaluated contexts.
  This is somewhat counter-intuitive, so let's analyze
  the alternatives:
  1. execute on read: does not comply with project specification,
                      as call-by-name square(++x) would be equal
                      to call-by-value square(++x) (see test.fpl)
  2. execute on variable read: this requires the data structure to
                              tell numeric variables from other
                              kinds and mark them as tainted,
                              thus creating considerable overhead
  */

  /*@ top level program expressions: \newline
  Expressions, variable and function definitions, halt program and sequential composition
  */
  syntax PgmExp ::= VExp
                  | Let
                  | Funct
                  | "halt"
                  | PgmExp ";" PgmExp [left] // sequential composition

  //@ values or expressions which return values
  syntax VExp ::= Exp | Val

  /*@
  expressions which return values: \newline
  \verb|Id| variable lookup \newline
  \verb|++Id| pre-increment (with side-effects! \newline
  \verb|AOp VExp VExp| arithmetics in polish notation \newline
  \verb|VExp : VExp| haskell-style list extension \newline
  \verb|VExp ( VExps )| function / lambda call \newline
  \verb|if VExp then Block else Block| if condition \newline
  \verb|$arg VExp| evaluate expression in caller context (e.g. function arguments)\newline
  pre-defined list functions: \newline
  \verb|empty ( VExp )| check if list is empty \newline
  \verb|head ( VExp )| get head of list \newline
  \verb|tail ( VExp )| get tail of list
  */
  syntax Exp ::= Id // get value of variable
               > "++" Id // pre-increment // this adds side-effects!
               > AOp VExp VExp // arithmetics
               > VExp ":" VExp // list extension
               > "empty" "(" VExp ")" // check if list is empty
               | "head" "(" VExp ")" // get head of list
               | "tail" "(" VExp ")" // get tail of list
               > VExp "(" VExps ")" // function / lambda call
               | "if" VExp "then" Block "else" Block // if
               > "$arg" VExp // evaluate expression in caller context
               | "(" VExp ")" [bracket]

  /*@
  variable assignment \newline
  \verb|let Id = ( VExp )| for call by need \newline
  \verb|set Id = ( VExp )| for call by name \newline
  \verb|(Id := VExp)| for call by value
  */
  syntax Let ::= "let" Id "=" "(" VExp ")" // call by need
               | "set" Id "=" "(" VExp ")" // call by name
               | Id ":=" VExp [right,strict(2)] // call by value

  /*@
  function definition \newline
  \verb|def Id ( Ids ) Block| for call by need \newline
  \verb|sub Id ( Ids ) Block| for call by name \newline
  \verb|function Id ( Ids ) Block| for call by value
  */
  syntax Funct ::= "def" Id "(" Ids ")" Block // call by need
                 | "sub" Id "(" Ids ")" Block // call by name
                 | "function" Id "(" Ids ")" Block // call by value

  /*@
  anonymous function definition \newline
  \verb|\\ Ids -> Block| for call by need \newline
  \verb|proc Ids -> Block| for call by name \newline
  \verb|lambda Ids -> Block| for call by value
  */
  syntax Lambda ::= "\\" Ids "->" Block // call by need
                  | "proc" Ids "->" Block // call by name
                  | "lambda" Ids "->" Block // call by value

  //@ list [eager]
  syntax Li ::= "[" VExps "]" [strict]

  //@ code block for conditions and functions
  syntax Block ::= "{" PgmExp "}"

  //@ predefined functions
  syntax Predef ::= "empty"
                  | "head"
                  | "tail"

  // various Lists of things
  syntax Ids ::= List{Id,","}
  syntax VExps ::= List{VExp,","} [strict]

  //@ arithmetic operations (call by need)
  syntax AOp ::= "*" | "/" > "+" | "-" | "<"

  //@ base values (string used for comments only)
  syntax Val ::= Int | Bool | String | Lambda | Li
endmodule

module FPL-CONFIG
  imports FPL-SYNTAX

  syntax KResult ::= Val

  /*@
    additional syntax for internal processes:
    \emph{execute} starts evaluation in functions with lazy evaluation \newline
    \emph{ans} allows insertion of value from ans cell (like \textsc{Hole}) \newline
    \emph{continue} returns evaluation in another scope \newline
    \emph{(\%,K)} stores call-by-name values \newline
    \emph{Id <- VExp} overrides memory of variables
  */
  syntax K ::= "execute" // start actual evaluation in lazy evaluation
             | "ans" // used for lazy evaluation, instead of HOLE
             | (Map,K) // used to save state in fstack
             | "continue" "(" Map "," K ")" // return to scope
             | "(" "%" "," K ")" // call-by-name storage
             | Id "<-" VExp // variable override

  // current default evaluation in main scope: eager
  // change to lazy by adding "~> execute" after $PGM:K in <k>
  // and changing start value in <reading> to true
  configuration
    <T>
      /*@
      \emph{k} program (eager evaluation in main scope) \newline
      \emph{env} scoped environment \newline
      \emph{genv} global environment (functions only) \newline
      \emph{store} heap memory \newline
      \emph{fstack} function stack, each element with (environment,remaining commands) \newline
      \emph{reading} reading mode for lazy evaluation \newline
      \emph{ans} answer value of last expression
      */
      <k color="green"> $PGM:K </k>
      <env color="yellow"> .Map </env>
      <genv color="orange"> .Map </genv>
      <store color="red"> .Map </store>
      <fstack color="blue"> .List </fstack>
      <reading color="cyan"> false </reading>
      <ans> false </ans>
    </T>
endmodule

module FPL
  imports FPL-CONFIG
  imports FPL-VALUE
  imports FPL-NAME
  imports FPL-NEED

  //@ pre-increment (with side-effects!)
  rule ++ N:Id => (+ N 1) ~> N <- ans

  //@ halting
  rule <k> halt => HOLE ... </k>
       <fstack> .=>ListItem("halt") ... </fstack>
  
  //@ sequential composition
  rule X:PgmExp ; Y:PgmExp => X ~> Y [structural]

  //@ end of reading program
  rule <k> execute => A ... </k>
       <ans> A </ans>
       <reading> true => false </reading>

  //@ base case integer rules
  rule (+ X:Int Y:Int) => X +Int Y
  rule (- X:Int Y:Int) => X -Int Y
  rule (* X:Int Y:Int) => X *Int Y
  rule (/ X:Int Y:Int) => X /Int Y
    when Y =/=Int 0
  //@ comparison
  rule < X:Int Y:Int => X <Int Y

  //@ conditional
  rule if true then {E:PgmExp} else _ => E
  rule if false then _ else {E:PgmExp} => E

  //@ lambda - end of execution, garbage collect
  rule <k> .K </k>
       <env> ... (N |-> L) =>. </env>
       <store> ... (L |-> _) =>. ... </store>
       // don't garbage collect main scope
       <fstack> ListItem(_) ... </fstack>

  //@ lambda - end of execution, change scope
  rule <k> .K => V ~> K </k>
       <env> .Map=>Env </env>
       <fstack> ListItem((Env,K))=>. ... </fstack>
       <ans> V </ans> //@ necessary for HOLE in eager lists

  //@ list extension
  rule X:VExp : [Els:VExps] => [X,Els]

  //@ predef functions
  rule empty ( [.VExps] ) => true
  rule empty ( [E:VExp,Es:VExps] ) => false
  rule head ( [E:VExp,Es:VExps] ) => E
  rule tail ( [E:VExp,Es:VExps] ) => [Es]

  //@ write ans
  rule <k> (V:Val ~> E) => E ... </k>
       <ans> _ => V </ans>

  //@ skip over all expressions while reading program
  rule <k> X:Exp ~> Y => Y ... </k>
       <ans> _=>X </ans>
       <reading> true </reading>
  
  //@ get value from different scope
  rule <k> $arg E:VExp => E:VExp ~> continue(CurEnv,K) ... </k>
       <env> CurEnv=>Env </env>
       <fstack> ListItem((Env,K))=>. ... </fstack>

  //@ return to scope
  rule <k> continue(Env,K) =>. ... </k>
       <env> CurEnv=>Env </env>
       <fstack> .=>ListItem((CurEnv,K)) ... </fstack>

  //@ base variable lookup
  rule <k> N:Id => V ... </k>
       <env> ... N |-> L ... </env>
       <store> ... L |-> V:Val ... </store>
       <reading> false </reading>

  //@ global variable lookup
  rule <k> N:Id => E ... </k>
       <genv> ... N |-> L ... </genv>
       <store> ... L |-> E ... </store>
       <reading> false </reading>

endmodule
