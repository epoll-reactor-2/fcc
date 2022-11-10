// Warning at line 7, column 5: Variable `k` is never used
// Warning at line 8, column 5: Variable `l` is never used
int main() {
    int i = 0;
    while (i) {}
    int j = 0;
    int k = 0;
    int l = 0;
    do {
        do {
            do {
                do {
                    ++i;
                    ++j;
                } while (i);
            } while (i);
        } while (i);
    } while (i);
    return 0;
}