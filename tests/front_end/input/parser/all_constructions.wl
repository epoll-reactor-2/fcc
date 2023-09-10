//CompoundStmt <line:0, col:0>
//  StructDecl <line:72, col:1> `a`
//    CompoundStmt <line:72, col:1>
//      StructDecl <line:73, col:3> `b`
//        CompoundStmt <line:73, col:3>
//          VarDecl <line:74, col:5> int `first`
//          VarDecl <line:75, col:5> int `second`
//      VarDecl <line:77, col:3> struct b `bb`
//      VarDecl <line:78, col:3> struct a **** `aa`
//  FunctionDecl <line:81, col:1>
//    FunctionDeclRetType <line:81, col:1> int
//    FunctionDeclName <line:81, col:1> `main`
//    FunctionDeclArgs <line:81, col:1>
//    FunctionDeclBody <line:81, col:1>
//      CompoundStmt <line:81, col:12>
//        ArrayDecl <line:82, col:3> struct a ** [2] `object`
//        ArrayDecl <line:83, col:3> int ** [2] `args`
//        BinaryOperator <line:84, col:11> =
//          ArrayAccess <line:84, col:3> `args`
//            Number <line:84, col:8> 0
//          StructMember <line:84, col:14>
//            Prefix UnaryOperator <line:84, col:14> *
//              Prefix UnaryOperator <line:84, col:16> *
//                Prefix UnaryOperator <line:84, col:18> *
//                  Prefix UnaryOperator <line:84, col:20> *
//                    StructMember <line:84, col:21>
//                      Symbol <line:84, col:21> `object`
//                      Symbol <line:84, col:28> `aa`
//            StructMember <line:84, col:35>
//              Symbol <line:84, col:35> `bb`
//              Symbol <line:84, col:38> `first`
//        BinaryOperator <line:85, col:11> =
//          ArrayAccess <line:85, col:3> `args`
//            Number <line:85, col:8> 1
//          StructMember <line:85, col:14>
//            Prefix UnaryOperator <line:85, col:14> *
//              Prefix UnaryOperator <line:85, col:16> *
//                Prefix UnaryOperator <line:85, col:18> *
//                  Prefix UnaryOperator <line:85, col:20> *
//                    StructMember <line:85, col:21>
//                      Symbol <line:85, col:21> `object`
//                      Symbol <line:85, col:28> `aa`
//            StructMember <line:85, col:35>
//              Symbol <line:85, col:35> `bb`
//              Symbol <line:85, col:38> `second`
//        ReturnStmt <line:86, col:3>
//          FunctionCall <line:86, col:10> `a`
//            FunctionCallArgs <line:86, col:10>
//              CompoundStmt <line:86, col:10>
//                FunctionCall <line:86, col:12> `b`
//                  FunctionCallArgs <line:86, col:12>
//                    CompoundStmt <line:86, col:12>
//                      FunctionCall <line:86, col:14> `c`
//                        FunctionCallArgs <line:86, col:14>
//                          CompoundStmt <line:86, col:14>
//                            FunctionCall <line:86, col:16> `d`
//                              FunctionCallArgs <line:86, col:16>
//                                CompoundStmt <line:86, col:16>
//                                  FunctionCall <line:86, col:18> `e`
//                                    FunctionCallArgs <line:86, col:18>
//                                      CompoundStmt <line:86, col:18>
//                                        FunctionCall <line:86, col:20> `f`
//                                          FunctionCallArgs <line:86, col:20>
//                                            CompoundStmt <line:86, col:20>
//                                              BinaryOperator <line:86, col:32> +
//                                                Prefix UnaryOperator <line:86, col:22> ++
//                                                  ArrayAccess <line:86, col:24> `args`
//                                                    Number <line:86, col:29> 0
//                                                Prefix UnaryOperator <line:86, col:34> --
//                                                  ArrayAccess <line:86, col:36> `args`
//                                                    Number <line:86, col:41> 1
struct a {
  struct b {
    int first;
    int second;
  };
  b bb;
  a ****aa;
}

int main() {
  a **object[2];
  int **args[2];
  args[0] = (*(*(*(*object.aa)))).bb.first;
  args[1] = (*(*(*(*object.aa)))).bb.second;
  return a(b(c(d(e(f(++args[0] + --args[1]))))));
}