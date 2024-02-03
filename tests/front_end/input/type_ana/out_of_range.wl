//E<4:18>: Out of range! Index (which is 4) >= array size (which is 4)
int main() {
    int mem[1][2][3][4];
    mem[0][1][2][4];
    return 0;
}
