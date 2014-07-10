/*execute
\title{FPL}

TODO doc

TODO make evaluation of lists for result possible
 (maybe by print for lists! print is deterministic!)

TODO call by value needs own arithmetic rules,
or only use infix for all

\author{Lars Hansen}
*/

require "fpl_value.k"
require "fpl_name.k"
require "fpl_need.k"

require "ans_rules.k"

module FPL-SYNTAX

  syntax PgmExp ::= VExp
                  | Let
                  | Funct
                  | "halt"
                  | PgmExp ";" PgmExp [left]

  syntax VExp ::= Exp | Val

  syntax Exp ::= Id // get value of variable
               > "empty" "(" VExp ")" // check if list is empty
               | "head" "(" VExp ")" // get head of list
               | "tail" "(" VExp ")" // get tail of list
               > VExp "(" VExps ")" // function / lambda call
               | "if" VExp "then" Block "else" Block // if
               > "++" Id // pre-increment // this adds side-effects!
               > AOp VExp VExp // arithmetics
               > VExp ":" VExp // list extension
               > "$arg" VExp // evaluate expression in caller context
               | "(" VExp ")" [bracket]

  syntax Let ::= "let" Id "=" "(" VExp ")" // call by need let
               | "set" Id "=" "(" VExp ")" // call by name let
               | Id ":=" VExp [right,strict(2)] // call by value let

  syntax Funct ::= "def" Id "(" Ids ")" Block // call by need def
                 | "sub" Id "(" Ids ")" Block // call by name def
                 | "function" Id "(" Ids ")" Block // call by value def

  syntax Lambda ::= "\\" Ids "->" Block // call by need lambda
                  | "proc" Ids "->" Block // call by name lambda
                  | "lambda" Ids "->" Block // call by value lambda

  syntax Li ::= "[" VExps "]" [strict] // TODO allow lazy lists

  syntax Block ::= "{" PgmExp "}"

  syntax Predef ::= "empty"
                  | "head"
                  | "tail"

  syntax Ids ::= List{Id,","}
  syntax VExps ::= List{VExp,","} [strict] // TODO allow lazy lists

  syntax AOp ::= "*" | "/" > "+" | "-" | "<"

  syntax Val ::= Int | Bool | String | Lambda | Li
endmodule

module FPL-CONFIG
  imports FPL-SYNTAX

  syntax KResult ::= Val

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
      <k color="green"> $PGM:K </k>
      <env color="yellow"> .Map </env>
      <store color="red"> .Map </store>
      <fstack color="blue"> .List </fstack>
      <genv color="orange"> .Map </genv>
      <reading color="cyan"> false </reading>
      <ans> false </ans>
    </T>
endmodule

module FPL
  imports FPL-CONFIG
  imports FPL-VALUE
  imports FPL-NAME
  imports FPL-NEED

  // side effects:
  // pre-increment
  rule ++ N:Id => (+ N 1) ~> N <- ans

  // halting
  rule <k> halt => HOLE ... </k>
       <fstack> .=>ListItem("halt") ... </fstack>
  
  // sequential composition
  rule X:PgmExp ; Y:PgmExp => X ~> Y [structural]

  // end of reading program
  rule <k> execute => A ... </k>
       <ans> A </ans>
       <reading> true => false </reading>

  // base case integer rules
  rule (+ X:Int Y:Int) => X +Int Y
  rule (- X:Int Y:Int) => X -Int Y
  rule (* X:Int Y:Int) => X *Int Y
  rule (/ X:Int Y:Int) => X /Int Y
    when Y =/=Int 0
  // comparison
  rule < X:Int Y:Int => X <Int Y

  // conditional
  rule if true then {E:PgmExp} else _ => E
  rule if false then _ else {E:PgmExp} => E

  // lambda - end of execution
  rule <k> .K => V ~> K </k>
       <env> _=>Env </env>
       <fstack> ListItem((Env,K))=>. ... </fstack>
       <ans> V </ans>

  // list extension
  rule X:VExp : [Els:VExps] => [X,Els]

  // predef functions
  rule empty ( [.VExps] ) => true
  rule empty ( [E:VExp,Es:VExps] ) => false
  rule head ( [E:VExp,Es:VExps] ) => E
  rule tail ( [E:VExp,Es:VExps] ) => [Es]

  // write ans
  rule <k> (V:Val ~> E) => E ... </k>
       <ans> _ => V </ans>

  // skip over all expressions while reading program
  rule <k> X:Exp ~> Y => Y ... </k>
       <ans> _=>X </ans>
       <reading> true </reading>
  
  // get value from different scope
  rule <k> $arg E:VExp => E:VExp ~> continue(CurEnv,K) ... </k>
       <env> CurEnv=>Env </env>
       <fstack> ListItem((Env,K))=>. ... </fstack>

  // return to scope
  rule <k> continue(Env,K) =>. ... </k>
       <env> CurEnv=>Env </env>
       <fstack> .=>ListItem((CurEnv,K)) ... </fstack>

  // base variable lookup
  rule <k> N:Id => V ... </k>
       <env> ... N |-> L ... </env>
       <store> ... L |-> V:Val ... </store>
       <reading> false </reading>

  // global variable lookup
  rule <k> N:Id => E ... </k>
       <genv> ... N |-> L ... </genv>
       <store> ... L |-> E ... </store>
       <reading> false </reading>

endmodule
