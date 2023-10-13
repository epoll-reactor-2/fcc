//E<6:7>: Indirection level mismatch (1 vs 2)
int main() {
    int a = 0;
    int *b = &a;
    int **c = &b;
    b = c;
}