//W<5:19>: Variable `second` is never used
//W<5:46>: Variable `fourth` is never used
//W<5:8>: Variable `first` is never used
//W<5:32>: Variable `third` is never used
void f(int first, char second, string third, bool fourth) {}

int main() {
    f(0, 'a', "aaa", false);
    return 0;
}
