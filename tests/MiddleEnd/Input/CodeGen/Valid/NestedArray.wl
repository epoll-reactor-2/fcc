// 10
int main() {
    int mem[2][2];
    mem[0][0] = 1;
    mem[0][1] = 2;
    mem[1][0] = 3;
    mem[1][1] = 4;

    return mem[0][0] + mem[0][1] + mem[1][0] + mem[1][1];
}