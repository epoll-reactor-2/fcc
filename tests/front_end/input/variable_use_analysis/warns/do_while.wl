//W<8:5>: Variable `l` is never used
//W<7:5>: Variable `k` is never used
//W<6:5>: Variable `j` written, but never read
int main() {
    int i = 0;
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
