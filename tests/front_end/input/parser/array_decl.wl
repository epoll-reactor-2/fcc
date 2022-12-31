//CompoundStmt <line:0, col:0>
//  FunctionPrototype <line:23, col:1> `f`
//    FunctionPrototypeArgs <line:23, col:1>
//      VarDecl <line:23, col:8> int `size`
//  FunctionPrototype <line:24, col:1> `f`
//    FunctionPrototypeArgs <line:24, col:1>
//      ArrayDecl <line:24, col:8> int [200000000] `array`
//      VarDecl <line:24, col:30> int `size`
//  FunctionPrototype <line:25, col:1> `f`
//    FunctionPrototypeArgs <line:25, col:1>
//      VarDecl <line:25, col:8> int `size`
//      ArrayDecl <line:25, col:18> int [300000000] `array`
//  FunctionDecl <line:27, col:1>
//    FunctionDeclRetType <line:27, col:1> int
//    FunctionDeclName <line:27, col:1> `main`
//    FunctionDeclArgs <line:27, col:1>
//    FunctionDeclBody <line:27, col:1>
//      CompoundStmt <line:27, col:12>
//        VarDecl <line:28, col:5> int `variable`
//          Number <line:28, col:20> 0
//        ArrayDecl <line:29, col:5> int [3] `array`
//        ArrayDecl <line:30, col:5> int [1][2][3] `array`
void f(int size);
void f(int array[200000000], int size);
void f(int size, int array[300000000]);

int main() {
    int variable = 0;
    int array[3];
    int array[1][2][3];
}
