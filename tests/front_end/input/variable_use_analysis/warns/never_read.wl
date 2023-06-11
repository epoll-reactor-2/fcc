//W<3:5>: Variable `mem` written, but never read
int main() {
    int mem = 0;
    mem = 1;
    ++mem;
    return 0;
}
