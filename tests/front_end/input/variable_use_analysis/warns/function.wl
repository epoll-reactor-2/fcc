//Warning at line 5, column 5: Variable `x` is never used
//Warning at line 9, column 5: Variable `y` is never used
//Warning at line 8, column 1: Function `g` is never used
void f() {
    char x = 'a';
}

void g() {
    char y = 'a';
}

int main() {
    f();
    return 0;
}