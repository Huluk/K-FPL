module ANS-RULES
  imports FPL-CONFIG
  /*@
  Various rules which allow to replace the command \emph{ans}
  with the value stored in \emph{<ans>}.
  */


  //@ arithmetic derivation rules
  rule <k> O:AOp X:Exp Y:VExp => X ~> O ans Y ... </k>
       <reading> false </reading>
  rule <k> O:AOp X:VExp Y:Exp => Y ~> O X ans ... </k>
       <reading> false </reading>
  //@ arithmetic read ans
  rule <k> O X ans => O X V ... </k>
       <ans> V </ans>
  rule <k> O ans X => O V X ... </k>
       <ans> V </ans>

  //@ conditional derivation rules
  rule <k> if X:Exp then T else F => X ~> if ans then T else F ... </k>
       <reading> false </reading>
  //@ conditional read ans
  rule <k> if ans then T else F => if V then T else F ... </k>
       <ans> V </ans>

  //@ function/lambda derivation rules
  rule <k> X:Exp ( Args:VExps ) => X ~> ans (Args) ... </k>
       <reading> false </reading>
  //@ function/lambda read ans
  rule <k> ans ( Args ) => V (Args) ... </k>
       <ans> V </ans>

  //@ list extension derivation rules
  rule <k> X : Y:Exp => Y ~> X : ans ... </k>
       <reading> false </reading>
  //@ list extension ans
  rule <k> X : ans => X : V ... </k>
       <ans> V </ans>

  //@ empty derivation rules
  rule <k> empty ( L:Exp ) => L ~> empty ( ans ) ... </k>
       <reading> false </reading>
  //@ empty read ans
  rule <k> empty ( ans ) => empty ( V ) ... </k>
       <ans> V </ans>
  //@ head derivation rules
  rule <k> head ( L:Exp ) => L ~> head ( ans ) ... </k>
       <reading> false </reading>
  //@ head read ans
  rule <k> head ( ans ) => head ( V ) ... </k>
       <ans> V </ans>
  //@ tail derivation rules
  rule <k> tail ( L:Exp ) => L ~> tail ( ans ) ... </k>
       <reading> false </reading>
  //@ tail read ans
  rule <k> tail ( ans ) => tail ( V ) ... </k>
       <ans> V </ans>
endmodule
