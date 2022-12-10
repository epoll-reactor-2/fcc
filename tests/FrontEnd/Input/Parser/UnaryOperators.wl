//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:18, col:1>
//    FunctionDeclRetType <line:18, col:1> void
//    FunctionDeclName <line:18, col:1> `f`
//    FunctionDeclArgs <line:18, col:1>
//    FunctionDeclBody <line:18, col:1>
//      CompoundStmt <line:18, col:10>
//        VarDecl <line:19, col:3> int `var1`
//          Number <line:19, col:14> 0
//        Postfix UnaryOperator <line:20, col:7> ++
//          Symbol <line:20, col:3> `var1`
//        Postfix UnaryOperator <line:21, col:7> --
//          Symbol <line:21, col:3> `var1`
//        Prefix UnaryOperator <line:22, col:3> --
//          Symbol <line:22, col:5> `var1`
//        Prefix UnaryOperator <line:23, col:3> ++
//          Symbol <line:23, col:5> `var1`
void f() {
  int var1 = 0;
  var1++;
  var1--;
  --var1;
  ++var1;
}