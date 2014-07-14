module FPL-NEED
  imports FPL-CONFIG
  /*@
  Special rules for call by need.
  */

  //@ lambda partial application
  rule \ X:Id,Xs:Ids -> {B} ( E:VExp,Es:VExps ) =>
       \ Xs -> { let X = ($arg E) ; B } (Es)
  //@ lambda application
  rule <k> \ .Ids -> {B} ( .VExps ) ~> K => B ~> execute </k>
       <env> Env => .Map </env>
       <fstack> .=>ListItem((Env,K)) ... </fstack>
       <reading> false => true </reading>

  //@ variable definition
  rule <k> let N:Id = (E:VExp) => . ... </k>
       <env> ... .=>(N |-> L) </env>
       <store> ... .=>(L |-> E) </store>
    when fresh(L)

  //@ function definition
  rule <k> def N:Id ( Args:Ids ) B:Block => . ... </k>
       <genv> ... .=>(N |-> L) </genv>
       <store> ... .=>(L |-> \ Args -> B) </store>
    when fresh(L)

  //@ thunk variable lookup
  rule <k> N:Id => E ~> N <- ans ... </k>
       <env> ... N |-> L ... </env>
       <store> ... L |-> E:Exp ... </store>
       <reading> false </reading>

  //@ thunk variable override
  rule <k> N:Id <- ans => V ... </k>
       <ans> V </ans>
       <env> ... N |-> L ... </env>
       <store> ... L |-> (_=>V) ... </store>

endmodule
