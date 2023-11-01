//a
int main() {
    int t = 0;
    int p = 0;
    int r = 0;
    int s = 0;
    int q = 0;

    int i = 1;
    int j = 1;
    int k = 1;
    int l = 1;

    do {
        if (p) {
            j = i;
            if (q) {
                l = 2;
            } else {
                l = 3;
            }
            ++k;
        } else {
            k = k + 2;
        }
        do {
            if (r) {
                l = l + 4;
            }
        } while (s);
    } while (t);

    i = i + 6;

    return 0;
}