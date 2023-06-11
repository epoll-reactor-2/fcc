//W<5:5>: Variable `x` is never used
//W<9:5>: Variable `y` is never used
//W<8:1>: Function `g` is never used
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