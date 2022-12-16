// 10
int main() {
    int index[2];
    index[0] = 1;
    index[1] = 0;
    int mem[2][2];
    mem[index[1]][index[1]] = 1;
    mem[index[1]][index[0]] = 2;
    mem[index[0]][index[1]] = 3;
    mem[index[0]][index[0]] = 4;

    return mem[0][0] + mem[0][1] + mem[1][0] + mem[1][1];
}
