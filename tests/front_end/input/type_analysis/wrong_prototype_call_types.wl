// Error at line 5, column 19: For argument `b` got string, but expected char
void f(string a, string b);

int main() {
    f("Hello", 'W');
    return 0;
}