# Compilation process

The main mission of the compiler is to transform one data representation (which is often set of commands to be
executed) to another one (both machine code or other language). In case of this language, it accepts most usual
programming language (similar to C) and goes through several stages to provide executable file to us. Let's go
through these steps.

##  Lexical analysis

Consider simple program

```c
int main() {
    return 1 + 2;
}
```

How should we start our transformations? First, we need to split this program into elementary pieces of text,
which are called **tokens**. To deal with it, we ask lexical analyzer (lexer) to do it. Once this phase was done,
we have now set of tokens.

```
Token                <INT>  
Token             <SYMBOL>  main
Token                    (  
Token                    )  
Token                    {  
Token             <RETURN>  
Token        <INT LITERAL>  1
Token                    +  
Token        <INT LITERAL>  2
Token                    ;  
Token                    }
```

Also, we got rid of some syntax details, for example, of quotes. Now, for each token, we know what type it
has, and what information it stores (number value, string, etc.).

## Syntax analysis

After we received our tokens, next step is to convert it to **Abstract Syntax Tree (AST)**. During this
step, we omit some syntactic details (Scopes, semicolons, etc.), which is needed to form needed for our
convenience details, but unnecessary for further steps of compilation.

The AST is built on the basis of language **grammar**, or set of **rules**, which we can apply to get
correct according to our idea syntax. For example, having very simple rules denoted in
[**EBNF**](https://en.wikipedia.org/wiki/Extended_Backus%E2%80%93Naur_form), such as

```
<program>      ::= '{' <decl> '}'
<type>         ::= 'structure' '{' <field-decl>* '}'
<field-decl>   ::= <type> | <var-decl>
<var-decl>     ::= ( 'int' | 'char' ) <alpha> '=' <decl-body>
<decl-body>    ::= ...
```

we can produce AST only according to these rules.

In case of our example program, tree can look like

```
  FunctionDecl <line:1, col:1>
    FunctionDeclRetType <line:1, col:1> <INT>
    FunctionDeclName <line:1, col:1> main
    FunctionDeclArgs <line:1, col:1>
    FunctionDeclBody <line:1, col:1>
      CompoundStmt <line:1, col:12>
        ReturnStmt <line:1, col:14>
          BinaryOperator <line:1, col:23> +
            IntegerLiteral <line:1, col:21> 1
            IntegerLiteral <line:1, col:25> 2
```

AST only stores information about operators priority, for example, expression **1 * 2 + 2 * 2** must be
represented as `{{1*2}+{2*2}}`, not, for example, as `{1*{2+{2*2}}}` to follow common arithmetic rules.

We can operate on such tree with depth-first traversals to analyze for errors or to create intermediate
representation (IR).

## Intermediate code generation

In order to make compiler cross-platform, code is turned to some abstract, assembly-like language, such as
LLVM IR or GIMPLE.

With our AST, we can easily then convert it to subsequence of trivial commands.

Let's write more complex example to demonstrate purpose of this step.

```c
int main() {
	int a = 1;
	int b = 2;
	return a + b;
}
```

So, AST of this code is turned into following LLVM IR

```
define i32 @main() {
entry:
  %0 = alloca i32, align 4
  store i32 1, i32* %0, align 4
  %1 = alloca i32, align 4
  store i32 2, i32* %1, align 4
  %2 = load i32, i32* %0, align 4
  %3 = load i32, i32* %1, align 4
  %4 = add i32 %2, %3
  ret i32 %4
}
```

Here is lot unnecessary at the moment details, but we can see, that we cannot just do something like a
`return a + b` on this level; we should to get variables **a** and **b** from memory, load them from
somewhere (register, RAM, etc.), after this we save result of this operation and finally return result.

## Platform-dependent code generation

With our abstract IR, we can now do last step of compilation - machine code creation. From example
above, LLVM provides to us following program

```assembly
	.text
	.file	"code.ll"
	.globl	main                            # - Begin function main
	.p2align	4, 0x90
	.type	main,@function
main:                                   # @main
	.cfi_startproc
# %bb.0:                                # %entry
	movl	$1, -4(%rsp)
	movl	$2, -8(%rsp)
	movl	$3, %eax
	retq
.Lfunc_end0:
	.size	main, .Lfunc_end0-main
	.cfi_endproc
                                        # - End function
	.section	".note.GNU-stack","",@progbits
```

Simple, right? : )
