# Architecture

Language is formally split into two parts: front-end and middle-end.

## Front end

This module is responsible to make all input program transformations before **AST** building stage. So there
is
* definitions of all tokens
* lexical analyzer
* AST
* syntactic analyzer (parser)

### Tokens

Token is small part of input stream containing its **type** (which is simple enumeration), value (which is string;
can be empty, if all information is clear from the type, for example, ";", "{", etc.), and its position in input program
(line and column number).

### Lexical analyzer

This tool is responsible for dividing text to tokens. Nothing special, although here is used
[maximal munch](https://en.wikipedia.org/wiki/Maximal_munch) idea to recognize tokens **+** and **++** correctly.

### AST

Each node is a child of [**ASTNode**](https://github.com/epoll-reactor/weak_compiler/blob/master/lib/include/FrontEnd/AST/ASTNode.hpp)
class, which is single root object for all other AST nodes. The main idea of this tree hierarchy is
[visitor pattern](https://en.wikipedia.org/wiki/Visitor_pattern). There is **Accept** method, which each child of **ASTNode** must to implement.

Thus, we can easily write any logic acting as tree traversal outside of AST classes. Inside the project there are
two visitors: one is for printing it to screen, other is to code generation.

In the future also external AST visitors can be inserted via some plugin system (like in clang).

### Syntactic analyzer

Producer of AST. As mentioned [there]((https://github.com/epoll-reactor/weak_compiler/blob/master/documentation/CompilationProcess.md)
), set of correct trees, that it can produce, denoted by formal grammar. In the code, each **Parse\*()** function is
representing each syntax rule, that can be applied. Of course, not any rule is available from any stage of parser.
For example, we cannot parse **break** or **continue** statements if we are outside any loop. Parser must take care of such moments.

## Middle end

### LLVM IR generator

The core of IR forming is **CodeGen** class, which is implemented also as AST visitor. His task is simple: traverse AST
and determine elementary expressions, that can be easily converted to intermediate code.

This class uses bunch of helpers:
* **ScalarExprEmitter** - there is long list of arithmetic operations and codegen operations to it
* **TypeCheck** - different type assertions (types are same, array index is not out of bound, etc.)
* **TypeResolver** - converter from front end types (token kinds) to LLVM types.

Also, code generator is responsible to handle variable definitions and their life scopes. **DeclsStorage** helps him to deal with it.
