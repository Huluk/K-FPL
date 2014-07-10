/*execute 
\title{FPL}

Problem: all base operations may be executed, /bc they don't check reading

Trying out <thunk> execute


current thoughts:

if I create call-by-need lists,
then these lists may contain arbitrary VExp.
When one of these elements is evaluated (by calling hd),
then it must be overridden in the original list,
which may be anywhere in any variable.
so, each list must contain a backlink in order to signify,
part of which list it is.
possible solution: make new list object:
list_reference_starting_at_index_i,
which solves this problem.

\author{Lars Hansen}
*/
module FPL-NEED
  imports FPL-CONFIG
  imports ANS-RULES

  // lambda partial application
  rule \ X:Id,Xs:Ids -> {B} ( E:VExp,Es:VExps ) =>
       \ Xs -> { let X = ($arg E) ; B } (Es)
  // lambda application
  rule <k> \ .Ids -> {B} ( .VExps ) ~> K => B ~> execute </k>
       <env> Env => .Map </env>
       <fstack> .=>ListItem((Env,K)) ... </fstack>
       <reading> false => true </reading>

  // variable definition
  rule <k> let N:Id = (E:VExp) => . ... </k>
       <env> ... .=>(N |-> L) </env>
       <store> ... .=>(L |-> E) </store>
    when fresh(L)

  // function definition
  rule <k> def N:Id ( Args:Ids ) B:Block => . ... </k>
       <genv> ... .=>(N |-> L) </genv>
       <store> ... .=>(L |-> \ Args -> B) </store>
    when fresh(L)

  // thunk variable lookup
  rule <k> N:Id => E ~> N <- ans ... </k>
       <env> ... N |-> L ... </env>
       <store> ... L |-> E:Exp ... </store>
       <reading> false </reading>

  // thunk variable override
  rule <k> N:Id <- ans => V ... </k>
       <ans> V </ans>
       <env> ... N |-> L ... </env>
       <store> ... L |-> (_=>V) ... </store>

endmodule
