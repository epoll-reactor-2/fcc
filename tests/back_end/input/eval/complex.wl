//25125250
int main() {
    int a = 10000;
    int b = 15000;
    int c = 20000;
    int d = 25000;
    int result = 0;

    for (int i = 0; i < 500; ++i) {
        result = result + (a + i + b + d);
        ++result;
    }

    return result;
}