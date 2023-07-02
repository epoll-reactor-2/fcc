int main() {
    int a = 1;
    int b = 2;
    int c = 3;

    while (a) {
        int d = 0;

        for (int i = 0; i < 1000; ++i) {
            if (a % 2 == 0) {
                ++b;
            }
            if (a % 3 == 0) {
                ++c;
            }
        }

        while (b) {
            --b;
            while (c) {
                --c;
                while (d) {
                    --d;
                    a + b - c + b + a + a - b + a;
                }
            }
        }
    }

    return a;
}