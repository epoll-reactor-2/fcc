# Example usage

```
$ cat example.wl
int puts(string arg);

int main() {
	string input = "Hello, World!";
	return puts(input);
}
```

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
Token     <STRING_LITERAL>  Hello, World!
Token                    ;  
Token             <RETURN>  
Token             <SYMBOL>  puts
Token                    (  
Token             <SYMBOL>  input
Token                    )  
Token                    ;  
Token                    }
```
```
$ ./Compiler -i example.wl -dump-ast
CompoundStmt <line:0, col:0>
  FunctionPrototype <line:1, col:1> puts
    FunctionPrototypeArgs <line:1, col:1>
      VarDeclStmt <line:1, col:10> <STRING> arg
  FunctionDecl <line:3, col:1>
    FunctionDeclRetType <line:3, col:1> <INT>
    FunctionDeclName <line:3, col:1> main
    FunctionDeclArgs <line:3, col:1>
    FunctionDeclBody <line:3, col:1>
      CompoundStmt <line:3, col:12>
        VarDeclStmt <line:4, col:2> <STRING> input
          StringLiteral <line:4, col:17> Hello, World!
        ReturnStmt <line:5, col:2>
          FunctionCall <line:5, col:9> puts
            FunctionCallArgs <line:5, col:9>
              Symbol <line:5, col:14> input
```
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
```
$ ./Compiler -i example.wl -o example
$ ./example
Hello, World!
```

## Comparison with clang

Example of sqrt function (on the left - clang++, on the right - weak compiler).

![alt text](https://github.com/epoll-reactor/weak_compiler/blob/master/images/sqrt-clang-comparison.png?raw=true)
