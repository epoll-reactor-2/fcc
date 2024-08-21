//a
int main() {
    int a = 1;
    int b = 2;
    int c = 3;
    int d = 4;
    int e = 5;
    int f = 6;
    int g = 7;
    int h = 8;
    int i = 9;
    int j = 10;

    // Perform a complex series of operations to ensure spill
    int result1 = a + b * c - d / e + f;
    int result2 = g * h - i + j * a - b;

    return result1 + result2;
}