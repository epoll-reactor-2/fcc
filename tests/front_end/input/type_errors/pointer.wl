//E<5:9>: Indirection level mismatch (1 vs 0)
int main() {
    int result = 0;
    int *ptr = &result;
    ptr = 2;
    return result;
}