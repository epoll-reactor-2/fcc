//E<5:19>: Cannot apply `<<` to float and float
int main() {
    float f0 = 0.0;
    float f1 = 1.0;
    float f2 = f0 << f1;
    return 0;
}