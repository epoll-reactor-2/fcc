// Error at line 4, column 5: Out of range! Index (which is 100) >= array size (which is 99)
int main() {
    int mem[99];
    mem[100] = 100;
    return mem[100];
}