[![Documentation](https://img.shields.io/badge/docs-doxygen-blue.svg)](https://epoll-reactor.github.io/weak_compiler/index.html)

# Compiler

This is an implementation of simple (or not so simple, XD) compiler,
which uses LLVM.

## TODO
* Preprocessing;
* something similar to standard library (libc wrappers);
* well-defined type system;
* scopes;
* handling of multiple definitions;
* graph-based optimizations.

## Command line
Let me show how we can use it from command line:
```
$ cat example.wl
// Declared in libc.
int puts(string arg);

int main() {
	string input = "Hello, World!";
	return puts(input);
}
```
If we're want to view tokens:
```
$ ./Compiler -i example.wl -dump-lexemes
Token                <INT>  
Token             <SYMBOL>  puts
Token                    (  
Token             <STRING>  
Token             <SYMBOL>  arg
Token                    )  
Token                    ;  
Token                <INT>  
Token             <SYMBOL>  main
Token                    (  
Token                    )  
Token                    {  
Token             <STRING>  
Token             <SYMBOL>  input
Token                    =  
Token       STRING LITERAL  Hello, World!
Token                    ;  
Token             <RETURN>  
Token             <SYMBOL>  puts
Token                    (  
Token             <SYMBOL>  input
Token                    )  
Token                    ;  
Token                    }
```
If we're want to view syntax tree:
```
$ ./Compiler -i example.wl -dump-ast
CompoundStmt <line:0, col:0>
  FunctionPrototype <line:2, col:1> puts
    FunctionPrototypeArgs <line:2, col:1>
      VarDeclStmt <line:2, col:10> <STRING> arg
  FunctionDecl <line:4, col:1>
    FunctionDeclRetType <line:4, col:1> <INT>
    FunctionDeclName <line:4, col:1> main
    FunctionDeclArgs <line:4, col:1>
    FunctionDeclBody <line:4, col:1>
      CompoundStmt <line:4, col:12>
        VarDeclStmt <line:5, col:2> <STRING> input
          StringLiteral <line:5, col:17> Hello, World!
        ReturnStmt <line:6, col:2>
          FunctionCall <line:6, col:9> puts
            FunctionCallArgs <line:6, col:9>
              Symbol <line:6, col:14> input
```
If we're want to view LLVM IR:
```
$ ./Compiler -i example.wl -dump-llvm
@0 = constant [14 x i8] c"Hello, World!\00"

declare i32 @puts(i8*)

define i32 @main() {
entry:
  %input = alloca i8*, align 8
  store i8* getelementptr inbounds ([14 x i8], [14 x i8]* @0, i32 0, i32 0), i8** %input, align 8
  %input1 = load i8*, i8** %input, align 8
  %0 = call i32 @puts(i8* %input1)
  ret i32 %0
}
```
And if we're want just to get executable file:
```
$ ./Compiler -i example.wl -o example
$ ./example
Hello, World!
```

## Comparison with IR from clang
This is an example of sqrt function LLVM IR (on the left - clang++, on the right - weak compiler)

![alt text](https://github.com/epoll-reactor/weak_compiler/blob/introduce-llvm/images/sqrt-clang-comparison.png?raw=true)
