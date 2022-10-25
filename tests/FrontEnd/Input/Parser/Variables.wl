//CompoundStmt <line:0, col:0>
//  FunctionDecl <line:14, col:1>
//    FunctionDeclRetType <line:14, col:1> <VOID>
//    FunctionDeclName <line:14, col:1> f
//    FunctionDeclArgs <line:14, col:1>
//    FunctionDeclBody <line:14, col:1>
//      CompoundStmt <line:14, col:10>
//        VarDecl <line:15, col:3> <FLOAT> value
//          FloatingPointLiteral <line:15, col:17> 3.1415
//        VarDecl <line:16, col:3> <BOOLEAN> good_boolean
//          BooleanLiteral <line:16, col:23> true
//        VarDecl <line:17, col:3> <BOOLEAN> malevolent_boolean
//          BooleanLiteral <line:17, col:29> false
void f() {
  float value = 3.1415;
  bool good_boolean = true;
  bool malevolent_boolean = false;
}