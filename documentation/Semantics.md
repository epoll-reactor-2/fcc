# Language semantics

## Data types

* **int** - signed 32-bit
* **float** - signed 32-bit
* **bool** - 8-bit
* **string** - character sequence (actually usual pointer), that ends with Null character
* **void** - empty type

Each type except **void** can represent array, for example, **bool array[10];**.

## Statements

* **while** - loop statement that performs its body until the condition evaluates to true.
```c
while (condition) {
    // Something.
} 
```

* **do-while** - loop statement with similar to **while** semantics, but it executes body before condition check at first time.
```c
do {
    // Something.
} while (condition);
```

* **for** - Loop statement with three initial parts and body. This includes **initial**, **conditional**, and **incremental** parts.
```c
for (int i = 0; true; ++i) {
    // Something.
}
```

* **if** - Conditional statement, that should execute **if part** when it's condition evaluates to true. Otherwise, **else part** should be executed.
```c
if (condition) {
    // Something.
} else {
    // Something else.
}
```

## Semantics

### Types

* Integer (boolean, integer, floating point) types are simple numeric types, which can be copied in trivial way (with memcpy and so on).

* String type initially is a pointer to string literal. However, once contents under this pointer are "modified",
copy of literal created and emplaced onto stack. After that, all operations on  string variable affecting local copy.

## Function parameters

* All types including arrays are copied to function parameters during call.

## Declarations

### Variables
```c
int value = 100;
float percentage = 77.89;
bool flag = false;
string text = "Hi!";
```

### Arrays
```c
int memory[1000];
```

### Functions

```c
int factorial(int n) {
    if (n == 0 || n == 1) {
        return 1;
    }
    return n * factorial(n - 1);
}
```

### Function prototypes

We can define functions without implementation. Then, language will try to find given function in
linked to it libraries, if it present.
```c
int puts(string data); // This is declared in C standard library which you use (see below).

int main() {
    return puts("Hello, World); // And called there.
}
```

## Call conventions

* The language have FFI with the GNU C Library and with other C  libraries in general. This mean, that \textbf{cdecl} call convention is used.
