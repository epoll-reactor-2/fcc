//E<5:9>: Indirection level mismatch (1 vs 2)
int main() {
    int result = 0;
    int *ptr = &result;
    ptr = &ptr;
    return result;
}