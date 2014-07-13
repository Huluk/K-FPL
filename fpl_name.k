require "ans_rules.k"

module FPL-NAME
  imports FPL-CONFIG

  //@ lambda partial application
  rule proc X:Id,Xs:Ids -> {B} ( E:VExp,Es:VExps ) =>
       proc Xs -> { set X = ($arg E) ; B } (Es)
  //@ lambda application
  rule <k> proc .Ids -> {B} ( .VExps ) ~> K => B ~> execute </k>
       <env> Env => .Map </env>
       <fstack> .=>ListItem((Env,K)) ... </fstack>
       <reading> false => true </reading>

  //@ variable definition
  rule <k> set N:Id = (E:VExp) => . ... </k>
       <env> ... .=>(N |-> L) </env>
       <store> ... .=>(L |-> (%,E)) </store>
    when fresh(L)

  //@ function definition
  rule <k> sub N:Id ( Args:Ids ) B:Block => . ... </k>
       <genv> ... .=>(N |-> L) </genv>
       <store> ... .=>(L |-> proc Args -> B) </store>
    when fresh(L)

  //@ base variable lookup
  rule <k> N:Id => E ... </k>
       <env> ... N |-> L ... </env>
       <store> ... L |-> (%,E) ... </store>
       <reading> false </reading>

endmodule
