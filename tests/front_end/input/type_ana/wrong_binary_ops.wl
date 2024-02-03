//E<11:7>: Cannot apply `<<=` to float and float
int main() {
    int i1 = 1;
    int i2 = 2;
    i2 /= i1;
    i2 <<= i1;

    float f = 0.0;
    float v = 0.1;
    f /= v;
    f <<= v;
    return 0;
}