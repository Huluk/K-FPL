module FPL-VALUE
  imports FPL-CONFIG

  //@ lambda derivation
  syntax K ::= "lambda" Ids "->" Block "(" "ans" "," VExps ")"
  rule lambda X:Id,Xs:Ids -> B:Block ( E:Exp,Es:VExps ) =>
       E ~> lambda X,Xs -> B ( ans,Es )
  //@ lambda read ans
  rule <k> lambda Xs:Ids -> B:Block ( ans,Es:VExps ) =>
           lambda Xs -> B ( V,Es ) ... </k>
       <ans> V </ans>

  //@ lambda partial application
  rule lambda X:Id,Xs:Ids -> {B} ( V:Val,Es:VExps ) =>
       lambda Xs -> { (X := V) ; B } (Es)

  //@ lambda application
  rule <k> lambda .Ids -> {B} ( .VExps ) ~> K => B </k>
       <env> Env => .Map </env>
       <fstack> .=>ListItem((Env,K)) ... </fstack>

  //@ variable definition
  rule <k> (N:Id := V:Val) => V ... </k>
       <env> ... .=>(N |-> L) </env>
       <store> ... .=>(L |-> V) </store>
    when fresh(L)

  //@ function definition
  rule <k> function N:Id ( Args:Ids ) B:Block => . ... </k>
       <genv> ... .=>(N |-> L) </genv>
       <store> ... .=>(L |-> lambda Args -> B) </store>
    when fresh(L)

endmodule
