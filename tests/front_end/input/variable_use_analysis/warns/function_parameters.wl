// Warning at line 5, column 19: Variable `second` is never used
// Warning at line 5, column 46: Variable `fourth` is never used
// Warning at line 5, column 8: Variable `first` is never used
// Warning at line 5, column 32: Variable `third` is never used
void f(int first, char second, string third, bool fourth) {}

int main() {
    f(0, 'a', "aaa", false);
    return 0;
}